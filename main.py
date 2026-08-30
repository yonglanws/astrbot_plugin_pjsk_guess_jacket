import asyncio
import json
import random
import time
import os
import sqlite3
import urllib.request
import urllib.error
import io
import re
from datetime import datetime
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Optional
from urllib.parse import quote

from PIL import Image, ImageDraw, ImageFont, ImageFilter
from pilmoji import Pilmoji

from astrbot.api import logger

try:
    from astrbot.api.event import filter, AstrMessageEvent
    from astrbot.api.star import Context, Star, register, StarTools
    import astrbot.api.message_components as Comp
    from astrbot.core.utils.session_waiter import session_waiter, SessionController, SessionFilter
    from astrbot.api import AstrBotConfig
    from astrbot.core.utils.astrbot_path import get_astrbot_data_path
except ImportError:
    logger.error("Failed to import from astrbot.api, attempting fallback.")
    from astrbot.core.plugin import Plugin as Star, Context, register, filter, AstrMessageEvent
    import astrbot.core.message_components as Comp
    from astrbot.core.utils.session_waiter import session_waiter, SessionController, SessionFilter

    class StarTools:
        @staticmethod
        def get_data_dir(plugin_name: str) -> Path:
            return Path(__file__).parent.parent.parent.parent / 'data' / 'plugins_data' / plugin_name

    def get_astrbot_data_path() -> Path:
        return Path(__file__).parent.parent.parent.parent / 'data'


try:
    from .master_data_service import SERVER_JP, SERVER_SC, MasterDataService
except ImportError:  # 直接以脚本方式加载（单测）时使用绝对导入
    from master_data_service import SERVER_JP, SERVER_SC, MasterDataService



try:
    from PIL.Image import Resampling
    LANCZOS = Resampling.LANCZOS
except ImportError:
    LANCZOS = 1


PLUGIN_NAME = "pjsk_guess_jacket"
PLUGIN_AUTHOR = "慵懒午睡"
PLUGIN_DESCRIPTION = "PJSK猜曲绘插件"
PLUGIN_VERSION = "1.1.2"
PLUGIN_REPO_URL = "https://github.com/yonglanws/astrbot_plugin_pjsk_guess_jacket"
DEFAULT_PLATFORM_NAME = "aiocqhttp"
OFFICIAL_PLATFORM_NAME = "qq_official"
OFFICIAL_QID_PATTERN = re.compile(r"^[0-9a-fA-F]{32}$")

# --- 题库服务器与官机 markdown 机制（与 PJSK Wordle 保持一致） ---
SERVER_JP = "jp"
SERVER_SC = "sc"
SERVER_LABELS = {SERVER_JP: "日服", SERVER_SC: "国服"}
SERVER_BADGES = {SERVER_JP: "日服题库", SERVER_SC: "国服题库"}
# 结算尾部显示的切换指令（当前日服 → 提示切换国服）
SWITCH_COMMANDS = {SERVER_JP: "猜曲绘切换国服题库", SERVER_SC: "猜曲绘切换日服题库"}
# 结算连接入口使用的指令名（与注册指令别名一一对应）
CONNECT_SWITCH_COMMANDS = {SERVER_JP: "猜曲绘切换国服题库", SERVER_SC: "猜曲绘切换日服题库"}

# 指令连接的默认 markdown 模板：QQ 官方机器人 markdown 消息的参数指令标签
# （见 bot.q.qq.com/wiki 的 markdown / text-chain 文档）。
# text 只放指令本身：QQ 客户端在群聊发送时会自动 @ 官方机器人，
# 拼进 "@id" 反而会出现双重 @。
DEFAULT_CONNECT_TEMPLATE = '<qqbot-cmd-input text="{encoded_command}" show="{encoded_name}" />'
DEFAULT_JP_RESOURCE_URL_BASE = "https://storage.exmeaning.com/sekai-jp-assets"
DEFAULT_SC_RESOURCE_URL_BASE = "https://storage.exmeaning.com/sekai-sc-assets"
# 旧版本默认模板特征：命中即视为未自定义，自动升级到新默认模板
_LEGACY_TEMPLATE_MARKERS = ("{encoded_at_text}", "mqqapi://")

# 快捷入口：所有 PJSK 娱乐插件的触发指令，Wordle 固定排最后


class BindingSessionFilter(SessionFilter):
    """只接收发起绑定的同一用户在同一会话中的确认消息。"""

    def __init__(self, session_id: str, user_id: str):
        self.session_id = str(session_id)
        self.user_id = str(user_id)

    def filter(self, event: AstrMessageEvent) -> str:
        if (
            str(event.unified_msg_origin) != self.session_id
            or str(event.get_sender_id()) != self.user_id
        ):
            return ""
        return f"{event.unified_msg_origin}:{event.get_sender_id()}"


@dataclass
class SongInfo:
    """歌曲信息数据类"""
    music_id: int
    original_name: str
    cn_title: Optional[str] = None

    @property
    def display_name(self) -> str:
        """获取显示名称"""
        return self.cn_title if self.cn_title else self.original_name


@dataclass
class JacketGameData:
    """曲绘游戏数据"""
    correct_song: SongInfo
    effect_name: str
    effect_display_name: str
    difficulty: int
    score: int


@dataclass
class JacketGameSession:
    """曲绘游戏会话"""
    game_data: Optional[JacketGameData] = None
    game_ended_by_timeout: bool = False


class Config:
    """配置常量"""
    DEFAULT_TIMEOUT = 30
    DEFAULT_COOLDOWN = 30
    DEFAULT_DAILY_LIMIT = 10
    MAX_JACKET_LOAD_ATTEMPTS = 5
    CLEANUP_INTERVAL = 3600
    MAX_AGE_SECONDS = 3600

    class Image:
        MAX_WIDTH = 800
        PADDING = 40
        LINE_SPACING = 15

        class FontSize:
            TITLE = 36
            OPTION = 24
            SMALL = 18
            CARD_TITLE = 24
            CARD_SUBTITLE = 16

    class Ranking:
        WIDTH = 720
        CARD_WIDTH = 680
        CARD_HEIGHT = 100
        CARD_GAP = 16
        HEADER_HEIGHT = 130
        FOOTER_HEIGHT = 50
        PADDING_X = 20
        TITLE_Y = 40
        SUBTITLE_Y = 95
        CIRCLE_RADIUS = 22
        CIRCLE_X_OFFSET = 35
        NAME_X_OFFSET = 85
        NAME_Y_OFFSET = 22
        NAME_MAX_LENGTH = 20
        NAME_MAX_WIDTH = 240
        ATTEMPTS_X_OFFSET = 50
        ACCURACY_X_OFFSET = 120
        SCORE_X_OFFSET = 250
        DATA_Y_OFFSET = 28
        RANK_TEXT_Y_OFFSET = 15
        ID_Y_OFFSET = 32
        LABEL_Y_OFFSET = 6
        ACCURACY_LABEL_Y_OFFSET = 30

    class Color:
        BG_WHITE = (255, 255, 255)
        BG_LIGHT = (248, 249, 250)
        BG_CARD = (255, 255, 255)
        TEXT_DARK = (33, 37, 41)
        TEXT_GRAY = (108, 117, 125)
        TEXT_LIGHT_GRAY = (173, 181, 189)
        TEXT_ACCENT = (102, 126, 234)
        BORDER_LIGHT = (222, 226, 230)
        CARD_SHADOW = (233, 236, 239)
        BG_DARK = (25, 25, 35)
        BG_MEDIUM = (30, 30, 50)
        BG_RANKING = (30, 40, 60)
        TEXT_WHITE = (255, 255, 255)
        TEXT_SHADOW = (100, 100, 120)
        TEXT_GOLD = (255, 220, 100)
        TEXT_YELLOW = (255, 200, 100)
        TEXT_GREEN = (100, 255, 100)
        TEXT_BLUE = (100, 200, 255)
        TEXT_SUBTITLE = (102, 102, 102)
        OUTLINE = (80, 80, 120)
        CARD_OUTLINE = (70, 72, 100)
        LINE = (60, 60, 80)
        MEDAL_GOLD = (255, 215, 0)
        TITLE = (50, 50, 70)
        SUBTITLE = (120, 120, 140)
        CARD_BG = (255, 255, 255)
        CARD_BORDER = (230, 230, 240)
        TEXT_RANKING_DARK = (40, 40, 60)
        TEXT_RANKING_GRAY = (100, 100, 120)
        SCORE = (255, 140, 0)
        ACCURACY = (0, 150, 136)
        ATTEMPTS = (100, 149, 237)
        MEDAL_GOLD_RANK = (255, 193, 7)
        MEDAL_SILVER = (192, 192, 192)
        MEDAL_BRONZE = (205, 127, 50)
        RANK_BG = (220, 220, 230)
        GRADIENT_START = (252, 252, 254)
        GRADIENT_END = (244, 244, 246)


class LocalDataManager:
    """本地数据管理器，从本地文件读取歌曲翻译和别名数据"""

    def __init__(self, data_dir: Path, aliases_file: Optional[Path] = None, songs_file: Optional[Path] = None):
        self.data_dir = data_dir
        self.data_dir.mkdir(parents=True, exist_ok=True)
        self.aliases_file = aliases_file
        self.songs_file = songs_file
        self.cn_map: dict[int, str] = {}
        self.name_to_id_map: dict[str, int] = {}
        self.id_to_name_map: dict[int, str] = {}
        self.aliases_map: dict[int, list[str]] = {}
        self._load_local_data()

    def _load_local_data(self):
        """从本地 JSON 文件加载数据"""
        self._load_songs_data()
        self._load_aliases_data()

    def _load_songs_data(self):
        """加载 songs.json 中的中文翻译数据"""
        if self.songs_file and self.songs_file.exists():
            try:
                with open(self.songs_file, 'r', encoding='utf-8') as f:
                    songs_data = json.load(f)
                self._parse_songs_data(songs_data)
                logger.info(f"Loaded {len(self.cn_map)} translations from songs.json")
            except Exception as e:
                logger.warning(f"Failed to load songs data: {e}")

    def _parse_songs_data(self, songs_data: list):
        """解析 songs.json 数据，提取中文翻译"""
        for entry in songs_data:
            try:
                music_id = int(entry.get("id"))
                original_name = entry.get("n", "")
                cn_title = entry.get("cn", "")

                if original_name:
                    self.id_to_name_map[music_id] = original_name
                    self.name_to_id_map[original_name] = music_id
                if cn_title:
                    self.cn_map[music_id] = cn_title
                    self.name_to_id_map[cn_title] = music_id
            except (ValueError, TypeError):
                continue

    def _load_aliases_data(self):
        """加载别名数据"""
        if self.aliases_file and self.aliases_file.exists():
            self._parse_aliases_file(self.aliases_file)
        else:
            aliases_file = self.data_dir / "aliases.json"
            if aliases_file.exists():
                try:
                    with open(aliases_file, 'r', encoding='utf-8') as f:
                        data = json.load(f)
                        self._build_aliases_map(data)
                    logger.info(f"Loaded {len(self.aliases_map)} aliases from local file")
                except Exception as e:
                    logger.warning(f"Failed to load aliases: {e}")

    def _parse_aliases_file(self, file_path: Path):
        """解析 aliases.json 格式的数据"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                data = json.load(f)
            self._build_aliases_map(data)
            logger.info(f"Loaded {len(self.aliases_map)} aliases from aliases.json")
        except Exception as e:
            logger.warning(f"Failed to load aliases data: {e}")

    def _build_aliases_map(self, aliases_data: dict):
        """构建 musicId -> 别名列表 的映射"""
        self.aliases_map = {}
        musics = aliases_data.get("musics", [])
        for entry in musics:
            try:
                music_id = int(entry.get("music_id"))
                aliases = entry.get("aliases", [])
                # 支持两种字段名：title 或 original_name
                original_name = entry.get("original_name") or entry.get("title", "")
                cn_title = entry.get("cn_title", "")

                if aliases:
                    self.aliases_map[music_id] = aliases
                if original_name:
                    self.id_to_name_map[music_id] = original_name
                    self.name_to_id_map[original_name] = music_id
                if cn_title:
                    self.cn_map[music_id] = cn_title
                    self.name_to_id_map[cn_title] = music_id
            except (ValueError, TypeError):
                continue

    def get_cn_title(self, music_id: Optional[int]) -> Optional[str]:
        """获取中文标题"""
        if music_id is None:
            return None
        return self.cn_map.get(music_id)

    def get_music_id_by_name(self, name: str) -> Optional[int]:
        """通过名称获取 music_id"""
        return self.name_to_id_map.get(name)

    def is_known_song_name(self, answer: str) -> bool:
        """判断输入是否精确命中任一歌曲的中文名/原名/别名（用于区分真实作答与闲聊）"""
        answer_key = answer.strip().lower()
        if not answer_key:
            return False
        for name in self.name_to_id_map:
            if name.lower() == answer_key:
                return True
        for aliases in self.aliases_map.values():
            for alias in aliases:
                if alias.strip().lower() == answer_key:
                    return True
        return False

    def get_aliases(self, music_id: int) -> list[str]:
        """获取歌曲的所有别名"""
        return self.aliases_map.get(music_id, [])

    def check_answer(self, music_id: int, answer: str) -> tuple[bool, str]:
        """
        检查答案是否正确（支持模糊匹配）

        Args:
            music_id: 歌曲ID
            answer: 用户输入的答案

        Returns:
            (是否正确, 匹配到的名称)
        """
        answer = answer.strip().lower()
        if not answer:
            return False, ""

        cn_title = self.cn_map.get(music_id, "")
        original_name = self.id_to_name_map.get(music_id, "")
        aliases = self.aliases_map.get(music_id, [])

        all_names = [cn_title, original_name] + aliases
        all_names = [n for n in all_names if n]

        for name in all_names:
            if answer == name.lower():
                return True, name

        if len(answer) >= 1:
            for name in all_names:
                name_lower = name.lower()
                if len(name_lower) >= 1:
                    if answer in name_lower or name_lower in answer:
                        return True, name

        if len(answer) >= 2:
            for name in all_names:
                if self._similar(answer, name.lower(), threshold=0.55):
                    return True, name

        if len(answer) >= 3:
            for name in all_names:
                if self._fuzzy_match(answer, name.lower()):
                    return True, name

        if len(answer) >= 2:
            for name in all_names:
                if self._typo_tolerant_match(answer, name.lower()):
                    return True, name

        return False, ""

    def _fuzzy_match(self, s1: str, s2: str) -> bool:
        """
        模糊匹配，允许部分字符不匹配
        """
        if not s1 or not s2:
            return False

        s1, s2 = s1.lower(), s2.lower()

        if s1 == s2:
            return True

        if len(s1) < 2 or len(s2) < 2:
            return False

        s1_chars = set(s1)
        s2_chars = set(s2)
        common_chars = s1_chars & s2_chars

        if len(common_chars) == 0:
            return False

        similarity = len(common_chars) / min(len(s1_chars), len(s2_chars))
        if similarity >= 0.55:
            s1_no_space = s1.replace(" ", "")
            s2_no_space = s2.replace(" ", "")

            if self._contains_significant_substring(s1_no_space, s2_no_space):
                return True

        return False

    def _contains_significant_substring(self, s1: str, s2: str) -> bool:
        """
        检查是否包含有意义的子串
        """
        min_len = min(len(s1), len(s2))
        check_len = max(1, int(min_len * 0.3))

        for i in range(len(s1) - check_len + 1):
            substr = s1[i:i + check_len]
            if substr in s2:
                return True

        for i in range(len(s2) - check_len + 1):
            substr = s2[i:i + check_len]
            if substr in s1:
                return True

        return False

    def _typo_tolerant_match(self, s1: str, s2: str) -> bool:
        """
        容错匹配，处理常见拼写错误
        """
        if not s1 or not s2:
            return False

        s1, s2 = s1.lower(), s2.lower()

        common_typos = {
            '1': 'l',
            'l': 'l',
            'i': 'l',
            '0': 'o',
            'o': 'o',
            '5': 's',
            's': 's',
            '2': 'z',
            'z': 'z',
            '8': 'b',
            'b': 'b',
            '3': 'e',
            'e': 'e',
            '4': 'a',
            'a': 'a',
            '7': 't',
            't': 't',
            'n': 'n',
            'm': 'n',
            'u': 'u',
            'v': 'u',
            'c': 'c',
            'k': 'c',
        }

        def normalize(s: str) -> str:
            result = []
            for c in s:
                result.append(common_typos.get(c, c))
            return ''.join(result)

        s1_normalized = normalize(s1)
        s2_normalized = normalize(s2)

        if s1_normalized == s2_normalized:
            return True

        if len(s1_normalized) >= 1 and len(s2_normalized) >= 1:
            if s1_normalized in s2_normalized or s2_normalized in s1_normalized:
                return True

        return False

    def _similar(self, s1: str, s2: str, threshold: float = 0.8) -> bool:
        """简单的字符串相似度判断"""
        if not s1 or not s2:
            return False

        s1, s2 = s1.lower(), s2.lower()

        if s1 == s2:
            return True

        if s1 in s2 or s2 in s1:
            return True

        common = sum(1 for c in s1 if c in s2)
        similarity = common / max(len(s1), len(s2))

        return similarity >= threshold

    def reload_data(self):
        """重新加载本地数据"""
        self.cn_map.clear()
        self.name_to_id_map.clear()
        self.id_to_name_map.clear()
        self.aliases_map.clear()
        self._load_local_data()

    def apply_master_songs(self, songs: list, replace: bool = False) -> None:
        """用 master 同步数据重建歌名/翻译/别名映射（覆盖两服并集）。"""
        if replace:
            self.cn_map.clear()
            self.name_to_id_map.clear()
            self.id_to_name_map.clear()
            self.aliases_map.clear()
        for song in songs:
            mid = song.get("id")
            title = song.get("title")
            if mid is None or not title:
                continue
            self.id_to_name_map[mid] = title
            self.name_to_id_map[title] = mid
            cn = song.get("cn")
            if cn:
                self.cn_map[mid] = cn
                self.name_to_id_map[cn] = mid
            aliases = song.get("aliases") or []
            if aliases:
                self.aliases_map[mid] = list(aliases)

    def get_all_songs(self) -> list[SongInfo]:
        """获取所有歌曲列表"""
        songs = []
        for music_id in self.id_to_name_map:
            songs.append(SongInfo(
                music_id=music_id,
                original_name=self.id_to_name_map[music_id],
                cn_title=self.cn_map.get(music_id)
            ))
        return songs


class CloudJacketLoader:
    """按题库服务器加载并缓存曲绘。"""
    MAX_FILE_SIZE = 10 * 1024 * 1024
    MAX_IMAGE_DIMENSION = 4096
    MAX_PIXELS = 50 * 1024 * 1024

    def __init__(self, cache_dir: Optional[Path] = None, config=None):
        self.cache_dir = cache_dir
        self.config = config or {}
        if cache_dir:
            cache_dir.mkdir(parents=True, exist_ok=True)

    def _format_jacket_id(self, music_id: int) -> str:
        """格式化曲绘 ID：1-99 补零至三位，其余保持原样。"""
        return f"{music_id:03d}" if 1 <= music_id <= 99 else str(music_id)

    def get_jacket_url(self, music_id: int, server: str = SERVER_JP) -> Optional[str]:
        """获取当前题库服务器对应的曲绘 URL。"""
        if music_id < 1:
            return None
        config_key = "sc_resource_url_base" if server == SERVER_SC else "jp_resource_url_base"
        default = DEFAULT_SC_RESOURCE_URL_BASE if server == SERVER_SC else DEFAULT_JP_RESOURCE_URL_BASE
        base_url = str(self.config.get(config_key, default) or default).strip().rstrip("/")
        jacket_id = self._format_jacket_id(music_id)
        return f"{base_url}/music/jacket/jacket_s_{jacket_id}/jacket_s_{jacket_id}.png"

    def load_jacket_image(self, music_id: int, server: str = SERVER_JP) -> Optional[Image.Image]:
        """从云端加载曲绘图片"""
        if self.cache_dir:
            cache_file = self.cache_dir / f"{server}_{music_id}.png"
            if cache_file.exists():
                try:
                    with Image.open(cache_file) as img:
                        return img.copy()
                except Exception as e:
                    logger.warning(f"Failed to load cached jacket: {e}")
                    try:
                        cache_file.unlink()
                    except Exception:
                        pass

        url = self.get_jacket_url(music_id, server)
        if not url:
            return None

        try:
            req = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0'})
            with urllib.request.urlopen(req, timeout=10) as response:
                chunks = []
                total_size = 0
                while True:
                    chunk = response.read(8192)
                    if not chunk:
                        break
                    total_size += len(chunk)
                    if total_size > self.MAX_FILE_SIZE:
                        logger.warning(f"Image file too large for music_id {music_id}: {total_size} bytes")
                        return None
                    chunks.append(chunk)

                img_data = b''.join(chunks)
                img = Image.open(io.BytesIO(img_data))

                width, height = img.size
                if width > self.MAX_IMAGE_DIMENSION or height > self.MAX_IMAGE_DIMENSION:
                    logger.warning(f"Image dimensions too large for music_id {music_id}: {width}x{height}")
                    return None

                if width * height > self.MAX_PIXELS:
                    logger.warning(f"Image pixel count too large for music_id {music_id}: {width * height}")
                    return None

                if self.cache_dir:
                    try:
                        cache_file = self.cache_dir / f"{server}_{music_id}.png"
                        img.save(cache_file)
                    except Exception as e:
                        logger.warning(f"Failed to cache jacket: {e}")

                return img
        except Exception as e:
            logger.warning(f"Failed to load jacket from cloud for music_id {music_id}: {e}")
            return None


class ImageGenerator:
    """图片生成器"""

    def __init__(
        self,
        font_path: Optional[Path] = None,
        display_name_resolver: Optional[Callable[[str, Optional[str]], str]] = None,
    ):
        self.font_path = font_path
        self.display_name_resolver = display_name_resolver
        self.title_font: ImageFont.FreeTypeFont
        self.header_font: ImageFont.FreeTypeFont
        self.body_font: ImageFont.FreeTypeFont
        self.id_font: ImageFont.FreeTypeFont
        self.medal_font: ImageFont.FreeTypeFont
        self.option_font: ImageFont.FreeTypeFont
        self.small_font: ImageFont.FreeTypeFont
        self.card_title_font: ImageFont.FreeTypeFont
        self.card_subtitle_font: ImageFont.FreeTypeFont
        self._load_fonts()

    def _load_fonts(self):
        """加载排行榜字体，字号与猜卡面排行榜保持一致"""
        default_font = ImageFont.load_default()

        if self.font_path and self.font_path.exists():
            try:
                self.title_font = ImageFont.truetype(str(self.font_path), 48)
                self.header_font = ImageFont.truetype(str(self.font_path), 28)
                self.body_font = ImageFont.truetype(str(self.font_path), 26)
                self.id_font = ImageFont.truetype(str(self.font_path), 16)
                self.medal_font = ImageFont.truetype(str(self.font_path), 36)
                self.option_font = self.body_font
                self.small_font = self.id_font
                self.card_title_font = self.body_font
                self.card_subtitle_font = self.id_font
                return
            except Exception as e:
                logger.error(f"Failed to load fonts: {e}")

        self.title_font = default_font
        self.header_font = default_font
        self.body_font = default_font
        self.id_font = default_font
        self.medal_font = default_font
        self.option_font = default_font
        self.small_font = default_font
        self.card_title_font = default_font
        self.card_subtitle_font = default_font
        logger.warning("Using default font")

    def _get_text_width(self, draw: ImageDraw.ImageDraw, text: str, font: ImageFont.FreeTypeFont) -> int:
        """获取文本宽度"""
        try:
            return int(draw.textlength(text, font=font))
        except AttributeError:
            try:
                bbox = font.getbbox(text)
                return bbox[2] - bbox[0]
            except AttributeError:
                return len(text) * 10

    def _truncate_text(self, draw: ImageDraw.ImageDraw, text: str, font: ImageFont.FreeTypeFont, max_width: int) -> str:
        """截断文本以适应最大宽度"""
        while self._get_text_width(draw, text + "...", font) > max_width and len(text) > 0:
            text = text[:-1]
        return text

    def create_ranking_image(self, rows: list[tuple], output_dir: Path) -> Optional[str]:
        """渲染与猜卡面排行榜一致的横向表格图片"""
        try:
            width = 850
            base_height = 250
            item_height = 70
            height = base_height + len(rows) * item_height

            bg_color_start = (230, 240, 255)
            bg_color_end = (200, 210, 240)
            img = Image.new("RGB", (width, height), bg_color_start)
            draw_bg = ImageDraw.Draw(img)
            for y in range(height):
                r = int(bg_color_start[0] + (bg_color_end[0] - bg_color_start[0]) * y / height)
                g = int(bg_color_start[1] + (bg_color_end[1] - bg_color_start[1]) * y / height)
                b = int(bg_color_start[2] + (bg_color_end[2] - bg_color_start[2]) * y / height)
                draw_bg.line([(0, y), (width, y)], fill=(r, g, b))

            if img.mode != "RGBA":
                img = img.convert("RGBA")

            white_overlay = Image.new("RGBA", img.size, (255, 255, 255, 100))
            img = Image.alpha_composite(img, white_overlay)

            title_text = "PJSK猜曲绘排行榜"
            font_color = (30, 30, 50)
            shadow_color = (180, 180, 190, 128)
            header_color = (80, 90, 120)
            score_color = (235, 120, 20)
            accuracy_color = (0, 128, 128)

            with Pilmoji(img) as pilmoji:
                center_x, title_y = int(width / 2), 80
                pilmoji.text(
                    (center_x + 2, title_y + 2),
                    title_text,
                    font=self.title_font,
                    fill=shadow_color,
                    anchor="mm",
                    emoji_position_offset=(0, 6),
                )
                pilmoji.text(
                    (center_x, title_y),
                    title_text,
                    font=self.title_font,
                    fill=font_color,
                    anchor="mm",
                    emoji_position_offset=(0, 6),
                )

                headers = ["排名", "玩家", "总分", "正确率", "总次数"]
                col_positions_header = [40, 150, 500, 610, 720]
                title_height = pilmoji.getsize(title_text, font=self.title_font)[1]
                current_y = title_y + int(title_height / 2) + 45
                for header in headers:
                    pilmoji.text(
                        (col_positions_header.pop(0), current_y),
                        header,
                        font=self.header_font,
                        fill=header_color,
                    )

                current_y += 55
                rank_icons = ["🥇", "🥈", "🥉"]

                for i, row in enumerate(rows):
                    user_id, user_name, custom_name, score, attempts, correct_attempts = (
                        str(row[0]), row[1], row[2], str(row[3]), str(row[4]), row[5]
                    )
                    is_unbound_official = len(row) > 6 and bool(row[6])
                    preferred_name = custom_name if custom_name else user_name
                    if self.display_name_resolver:
                        display_name = self.display_name_resolver(user_id, preferred_name)
                    else:
                        display_name = preferred_name if preferred_name else "未知用户"
                    accuracy = f"{(correct_attempts * 100 / int(attempts) if int(attempts) > 0 else 0):.1f}%"

                    rank = i + 1
                    col_positions = [40, 150, 500, 610, 720]
                    rank_num_align_x = 130
                    pilmoji.text(
                        (rank_num_align_x, current_y),
                        str(rank),
                        font=self.body_font,
                        fill=font_color,
                        anchor="ra",
                    )

                    if i < 3:
                        pilmoji.text(
                            (col_positions[0], current_y - 30),
                            rank_icons[i],
                            font=self.medal_font,
                            fill=font_color,
                        )

                    name_x = col_positions[1]
                    if is_unbound_official:
                        badge_text = "未绑定QQ"
                        badge_text_width = pilmoji.getsize(
                            badge_text,
                            font=self.id_font,
                        )[0]
                        badge_width = badge_text_width + 16
                        badge_height = 26
                        badge_y = current_y + 3
                        draw = ImageDraw.Draw(img)
                        draw.rounded_rectangle(
                            [
                                name_x,
                                badge_y,
                                name_x + badge_width,
                                badge_y + badge_height,
                            ],
                            radius=8,
                            fill=(115, 125, 150, 230),
                        )
                        pilmoji.text(
                            (name_x + 8, badge_y + 4),
                            badge_text,
                            font=self.id_font,
                            fill=(255, 255, 255, 255),
                        )
                        name_x += badge_width + 10

                    max_name_width = col_positions[2] - name_x - 20
                    if self.body_font.getbbox(display_name)[2] > max_name_width:
                        while self.body_font.getbbox(display_name + "...")[2] > max_name_width and len(display_name) > 0:
                            display_name = display_name[:-1]
                        display_name += "..."

                    pilmoji.text(
                        (name_x, current_y),
                        display_name,
                        font=self.body_font,
                        fill=font_color,
                    )
                    id_text = f"{user_name} ID: {user_id}"
                    max_id_width = col_positions[2] - col_positions[1] - 20
                    if self.id_font.getbbox(id_text)[2] > max_id_width:
                        while self.id_font.getbbox(id_text + "...")[2] > max_id_width and len(id_text) > 0:
                            id_text = id_text[:-1]
                        id_text += "..."
                    pilmoji.text(
                        (col_positions[1], current_y + 32),
                        id_text,
                        font=self.id_font,
                        fill=header_color,
                    )
                    pilmoji.text(
                        (col_positions[2], current_y),
                        score,
                        font=self.body_font,
                        fill=score_color,
                    )
                    pilmoji.text(
                        (col_positions[3], current_y),
                        accuracy,
                        font=self.body_font,
                        fill=accuracy_color,
                    )
                    pilmoji.text(
                        (col_positions[4], current_y),
                        attempts,
                        font=self.body_font,
                        fill=font_color,
                    )

                    separator_y = current_y + 60
                    if i < len(rows) - 1:
                        draw = ImageDraw.Draw(img)
                        draw.line([(30, separator_y), (width - 30, separator_y)], fill=(200, 200, 210, 128), width=1)

                    current_y += 70

                footer_text = f"Generated on {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
                footer_y = height - 25
                pilmoji.text(
                    (center_x, footer_y),
                    footer_text,
                    font=self.id_font,
                    fill=header_color,
                    anchor="ms",
                )

            os.makedirs(output_dir, exist_ok=True)
            img_path = output_dir / f"ranking_{time.time_ns()}.png"
            img.save(img_path)
            return str(img_path)

        except Exception as e:
            logger.error(f"渲染排行榜图片失败: {e}", exc_info=True)
            return None

    def _draw_rounded_rect(self, draw: ImageDraw.ImageDraw, x1: int, y1: int, x2: int, y2: int, radius: int, fill: tuple, outline: tuple):
        """绘制圆角矩形"""
        # 绘制主体矩形
        draw.rectangle([x1 + radius, y1, x2 - radius, y2], fill=fill)
        draw.rectangle([x1, y1 + radius, x2, y2 - radius], fill=fill)

        # 绘制四个圆角
        draw.ellipse([x1, y1, x1 + radius * 2, y1 + radius * 2], fill=fill)
        draw.ellipse([x2 - radius * 2, y1, x2, y1 + radius * 2], fill=fill)
        draw.ellipse([x1, y2 - radius * 2, x1 + radius * 2, y2], fill=fill)
        draw.ellipse([x2 - radius * 2, y2 - radius * 2, x2, y2], fill=fill)

        # 绘制边框
        draw.arc([x1, y1, x1 + radius * 2, y1 + radius * 2], 180, 270, fill=outline)
        draw.arc([x2 - radius * 2, y1, x2, y1 + radius * 2], 270, 360, fill=outline)
        draw.arc([x1, y2 - radius * 2, x1 + radius * 2, y2], 90, 180, fill=outline)
        draw.arc([x2 - radius * 2, y2 - radius * 2, x2, y2], 0, 90, fill=outline)
        draw.line([(x1 + radius, y1), (x2 - radius, y1)], fill=outline)
        draw.line([(x1 + radius, y2), (x2 - radius, y2)], fill=outline)
        draw.line([(x1, y1 + radius), (x1, y2 - radius)], fill=outline)
        draw.line([(x2, y1 + radius), (x2, y2 - radius)], fill=outline)

    def _get_text_height(self, draw: ImageDraw.ImageDraw, text: str, font: ImageFont.FreeTypeFont) -> int:
        """获取文本高度"""
        try:
            bbox = draw.textbbox((0, 0), text, font=font)
            return bbox[3] - bbox[1]
        except AttributeError:
            try:
                bbox = font.getbbox(text)
                return bbox[3] - bbox[1]
            except AttributeError:
                return 10


class JacketDatabaseManager:
    """曲绘游戏数据库管理器"""

    @staticmethod
    def _normalize_platform_name(platform_name: Optional[str]) -> str:
        return str(platform_name or DEFAULT_PLATFORM_NAME).strip().lower()

    def __init__(self, db_path: str):
        self.db_path = db_path
        self._init_db()

    def _init_db(self):
        conn = sqlite3.connect(self.db_path, timeout=30.0)
        try:
            cursor = conn.cursor()
            cursor.execute("""
                CREATE TABLE IF NOT EXISTS jacket_user_stats (
                    user_id TEXT NOT NULL,
                    user_name TEXT,
                    custom_name TEXT,
                    platform_name TEXT NOT NULL DEFAULT 'aiocqhttp',
                    score INTEGER DEFAULT 0,
                    attempts INTEGER DEFAULT 0,
                    correct_attempts INTEGER DEFAULT 0,
                    last_play_date TEXT,
                    daily_plays INTEGER DEFAULT 0,
                    PRIMARY KEY (user_id, platform_name)
                )
            """)
            columns = {
                row[1]
                for row in cursor.execute("PRAGMA table_info(jacket_user_stats)").fetchall()
            }
            if "platform_name" not in columns:
                cursor.execute(
                    "ALTER TABLE jacket_user_stats "
                    "ADD COLUMN platform_name TEXT NOT NULL DEFAULT 'aiocqhttp'"
                )

            primary_key_columns = [
                row[1]
                for row in cursor.execute("PRAGMA table_info(jacket_user_stats)").fetchall()
                if row[5]
            ]
            if primary_key_columns != ["user_id", "platform_name"]:
                cursor.execute(
                    """
                    CREATE TABLE jacket_user_stats_new (
                        user_id TEXT NOT NULL,
                        user_name TEXT,
                        custom_name TEXT,
                        platform_name TEXT NOT NULL,
                        score INTEGER DEFAULT 0,
                        attempts INTEGER DEFAULT 0,
                        correct_attempts INTEGER DEFAULT 0,
                        last_play_date TEXT,
                        daily_plays INTEGER DEFAULT 0,
                        PRIMARY KEY (user_id, platform_name)
                    )
                    """
                )
                cursor.execute(
                    """
                    INSERT INTO jacket_user_stats_new
                    (user_id, user_name, custom_name, platform_name, score, attempts,
                     correct_attempts, last_play_date, daily_plays)
                    SELECT user_id, user_name, custom_name, platform_name, score, attempts,
                           correct_attempts, last_play_date, daily_plays
                    FROM jacket_user_stats
                    """
                )
                cursor.execute("DROP TABLE jacket_user_stats")
                cursor.execute("ALTER TABLE jacket_user_stats_new RENAME TO jacket_user_stats")

            cursor.execute("""
                CREATE TABLE IF NOT EXISTS jacket_account_bindings (
                    official_platform TEXT NOT NULL,
                    official_user_id TEXT NOT NULL,
                    qq_user_id TEXT NOT NULL,
                    bound_at TEXT NOT NULL,
                    PRIMARY KEY (official_platform, official_user_id)
                )
            """)

            legacy_rows = cursor.execute(
                "SELECT user_id FROM jacket_user_stats "
                "WHERE platform_name = ?",
                (DEFAULT_PLATFORM_NAME,),
            ).fetchall()
            for (user_id,) in legacy_rows:
                if OFFICIAL_QID_PATTERN.fullmatch(str(user_id)):
                    cursor.execute(
                        "UPDATE jacket_user_stats SET platform_name = ? "
                        "WHERE user_id = ?",
                        (OFFICIAL_PLATFORM_NAME, user_id),
                    )
            conn.commit()
        finally:
            conn.close()

    def get_user_stats(self, user_id: str, platform_name: Optional[str] = None) -> Optional[tuple]:
        conn = sqlite3.connect(self.db_path, timeout=30.0)
        try:
            cursor = conn.cursor()
            if platform_name is None:
                cursor.execute(
                    "SELECT score, attempts, correct_attempts, last_play_date, daily_plays "
                    "FROM jacket_user_stats WHERE user_id = ?",
                    (str(user_id),),
                )
            else:
                cursor.execute(
                    "SELECT score, attempts, correct_attempts, last_play_date, daily_plays "
                    "FROM jacket_user_stats WHERE user_id = ? AND platform_name = ?",
                    (str(user_id), self._normalize_platform_name(platform_name)),
                )
            return cursor.fetchone()
        finally:
            conn.close()

    def get_user_rank(self, score: int) -> int:
        conn = sqlite3.connect(self.db_path, timeout=30.0)
        try:
            cursor = conn.cursor()
            cursor.execute("SELECT COUNT(*) FROM jacket_user_stats WHERE score > ?", (score,))
            return cursor.fetchone()[0] + 1
        finally:
            conn.close()

    def resolve_user_id(self, platform_name: str, user_id: str) -> str:
        platform = self._normalize_platform_name(platform_name)
        if platform != OFFICIAL_PLATFORM_NAME:
            return str(user_id)

        conn = sqlite3.connect(self.db_path, timeout=30.0)
        try:
            row = conn.execute(
                "SELECT qq_user_id FROM jacket_account_bindings "
                "WHERE official_platform = ? AND official_user_id = ?",
                (platform, str(user_id)),
            ).fetchone()
            return str(row[0]) if row else str(user_id)
        finally:
            conn.close()

    def is_official_account_bound(self, platform_name: str, user_id: str) -> bool:
        platform = self._normalize_platform_name(platform_name)
        if platform != OFFICIAL_PLATFORM_NAME:
            return False
        conn = sqlite3.connect(self.db_path, timeout=30.0)
        try:
            return conn.execute(
                "SELECT 1 FROM jacket_account_bindings "
                "WHERE official_platform = ? AND official_user_id = ?",
                (platform, str(user_id)),
            ).fetchone() is not None
        finally:
            conn.close()

    def update_user_play(
        self,
        user_id: str,
        user_name: str,
        platform_name: str = DEFAULT_PLATFORM_NAME,
    ):
        today = time.strftime("%Y-%m-%d")
        platform = self._normalize_platform_name(platform_name)
        conn = sqlite3.connect(self.db_path, timeout=30.0)
        try:
            cursor = conn.cursor()
            cursor.execute("BEGIN IMMEDIATE")
            cursor.execute(
                """INSERT INTO jacket_user_stats
                   (user_id, user_name, platform_name, last_play_date, daily_plays)
                   VALUES (?, ?, ?, ?, 1)
                   ON CONFLICT(user_id, platform_name) DO UPDATE SET
                       user_name = excluded.user_name,
                       daily_plays = CASE
                           WHEN jacket_user_stats.last_play_date = excluded.last_play_date
                           THEN jacket_user_stats.daily_plays + 1
                           ELSE 1
                       END,
                       last_play_date = excluded.last_play_date
                """,
                (str(user_id), user_name, platform, today),
            )
            conn.commit()
        finally:
            conn.close()

    def update_user_score(
        self,
        user_id: str,
        user_name: str,
        score: int,
        correct: bool,
        platform_name: str = DEFAULT_PLATFORM_NAME,
    ):
        today = time.strftime("%Y-%m-%d")
        platform = self._normalize_platform_name(platform_name)
        conn = sqlite3.connect(self.db_path, timeout=30.0)
        try:
            cursor = conn.cursor()
            cursor.execute(
                "SELECT user_id FROM jacket_user_stats "
                "WHERE user_id = ? AND platform_name = ?",
                (str(user_id), platform),
            )
            exists = cursor.fetchone() is not None

            if exists:
                correct_increment = 1 if correct else 0
                cursor.execute(
                    """UPDATE jacket_user_stats 
                       SET score = score + ?, 
                           attempts = attempts + 1, 
                           correct_attempts = correct_attempts + ?,
                           user_name = ?
                       WHERE user_id = ? AND platform_name = ?""",
                    (score, correct_increment, user_name, str(user_id), platform),
                )
            else:
                cursor.execute(
                    "INSERT INTO jacket_user_stats "
                    "(user_id, user_name, platform_name, score, attempts, correct_attempts, last_play_date, daily_plays) "
                    "VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                    (str(user_id), user_name, platform, score, 1, 1 if correct else 0, today, 1),
                )
            conn.commit()
        finally:
            conn.close()

    def can_play_today(
        self,
        user_id: str,
        daily_limit: int,
        platform_name: str = DEFAULT_PLATFORM_NAME,
    ) -> bool:
        if daily_limit == -1:
            return True
        today = time.strftime("%Y-%m-%d")
        platform = self._normalize_platform_name(platform_name)
        conn = sqlite3.connect(self.db_path, timeout=30.0)
        try:
            cursor = conn.cursor()
            cursor.execute(
                "SELECT daily_plays, last_play_date FROM jacket_user_stats "
                "WHERE user_id = ? AND platform_name = ?",
                (str(user_id), platform),
            )
            user_data = cursor.fetchone()
            if user_data and user_data[1] == today:
                return user_data[0] < daily_limit
            return True
        finally:
            conn.close()

    def bind_official_account(
        self,
        official_platform: str,
        official_user_id: str,
        qq_user_id: str,
    ) -> bool:
        """将未绑定的 QQ 官方机器人账号合并到普通 QQ 账号。"""
        platform = self._normalize_platform_name(official_platform)
        source_id = str(official_user_id).strip()
        target_id = str(qq_user_id).strip()

        if (
            platform != OFFICIAL_PLATFORM_NAME
            or not source_id
            or not re.fullmatch(r"\d{5,12}", target_id)
            or source_id == target_id
        ):
            return False

        conn = sqlite3.connect(self.db_path, timeout=30.0)
        try:
            conn.execute("BEGIN IMMEDIATE")
            cursor = conn.cursor()

            already_bound = cursor.execute(
                "SELECT 1 FROM jacket_account_bindings "
                "WHERE official_platform = ? AND official_user_id = ?",
                (platform, source_id),
            ).fetchone()
            if already_bound:
                conn.rollback()
                return False

            source_row = cursor.execute(
                "SELECT user_name, custom_name, score, attempts, correct_attempts, "
                "last_play_date, daily_plays "
                "FROM jacket_user_stats "
                "WHERE user_id = ? AND platform_name = ?",
                (source_id, platform),
            ).fetchone()
            target_row = cursor.execute(
                "SELECT user_name, custom_name, score, attempts, correct_attempts, "
                "last_play_date, daily_plays "
                "FROM jacket_user_stats "
                "WHERE user_id = ? AND platform_name = ?",
                (target_id, DEFAULT_PLATFORM_NAME),
            ).fetchone()

            if source_row and target_row:
                source_name, source_custom, source_score, source_attempts, source_correct, source_date, source_daily = source_row
                target_name, target_custom, target_score, target_attempts, target_correct, target_date, target_daily = target_row

                source_date = source_date or ""
                target_date = target_date or ""
                if source_date == target_date:
                    merged_date = source_date or None
                    merged_daily = int(source_daily or 0) + int(target_daily or 0)
                elif source_date > target_date:
                    merged_date = source_date or None
                    merged_daily = int(source_daily or 0)
                else:
                    merged_date = target_date or None
                    merged_daily = int(target_daily or 0)

                cursor.execute(
                    "UPDATE jacket_user_stats SET "
                    "user_name = ?, custom_name = ?, score = ?, attempts = ?, "
                    "correct_attempts = ?, last_play_date = ?, daily_plays = ? "
                    "WHERE user_id = ? AND platform_name = ?",
                    (
                        target_name or source_name,
                        target_custom or source_custom,
                        int(target_score or 0) + int(source_score or 0),
                        int(target_attempts or 0) + int(source_attempts or 0),
                        int(target_correct or 0) + int(source_correct or 0),
                        merged_date,
                        merged_daily,
                        target_id,
                        DEFAULT_PLATFORM_NAME,
                    ),
                )
            elif source_row:
                source_name, source_custom, source_score, source_attempts, source_correct, source_date, source_daily = source_row
                cursor.execute(
                    "INSERT INTO jacket_user_stats "
                    "(user_id, user_name, custom_name, platform_name, score, attempts, "
                    "correct_attempts, last_play_date, daily_plays) "
                    "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
                    (
                        target_id,
                        source_name,
                        source_custom,
                        DEFAULT_PLATFORM_NAME,
                        int(source_score or 0),
                        int(source_attempts or 0),
                        int(source_correct or 0),
                        source_date,
                        int(source_daily or 0),
                    ),
                )

            cursor.execute(
                "INSERT INTO jacket_account_bindings "
                "(official_platform, official_user_id, qq_user_id, bound_at) "
                "VALUES (?, ?, ?, ?)",
                (
                    platform,
                    source_id,
                    target_id,
                    time.strftime("%Y-%m-%d %H:%M:%S"),
                ),
            )
            cursor.execute(
                "DELETE FROM jacket_user_stats "
                "WHERE user_id = ? AND platform_name = ?",
                (source_id, platform),
            )
            conn.commit()
            return True
        except sqlite3.IntegrityError:
            conn.rollback()
            return False
        except Exception as e:
            conn.rollback()
            logger.error(f"绑定官方机器人账号失败: {e}", exc_info=True)
            return False
        finally:
            conn.close()

    def set_custom_name(
        self,
        user_id: str,
        user_name: str,
        custom_name: Optional[str],
        platform_name: str = DEFAULT_PLATFORM_NAME,
    ) -> bool:
        today = time.strftime("%Y-%m-%d")
        platform = self._normalize_platform_name(platform_name)
        conn = sqlite3.connect(self.db_path, timeout=30.0)
        try:
            cursor = conn.cursor()
            cursor.execute(
                "SELECT user_id FROM jacket_user_stats "
                "WHERE user_id = ? AND platform_name = ?",
                (str(user_id), platform),
            )
            exists = cursor.fetchone() is not None

            if custom_name:
                if exists:
                    cursor.execute(
                        "UPDATE jacket_user_stats SET custom_name = ? "
                        "WHERE user_id = ? AND platform_name = ?",
                        (custom_name, str(user_id), platform),
                    )
                else:
                    cursor.execute(
                        "INSERT INTO jacket_user_stats "
                        "(user_id, user_name, custom_name, platform_name, score, attempts, "
                        "correct_attempts, last_play_date, daily_plays) "
                        "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
                        (str(user_id), user_name, custom_name, platform, 0, 0, 0, today, 0),
                    )
            elif exists:
                cursor.execute(
                    "UPDATE jacket_user_stats SET custom_name = NULL "
                    "WHERE user_id = ? AND platform_name = ?",
                    (str(user_id), platform),
                )
            else:
                return False

            conn.commit()
            return True
        finally:
            conn.close()

    def get_ranking(self, limit: int) -> list[tuple]:
        conn = sqlite3.connect(self.db_path, timeout=30.0)
        try:
            cursor = conn.cursor()
            cursor.execute(
                "SELECT s.user_id, s.user_name, s.custom_name, s.score, "
                "s.attempts, s.correct_attempts, "
                "CASE WHEN s.platform_name = ? AND b.official_user_id IS NULL "
                "THEN 1 ELSE 0 END AS is_unbound_official "
                "FROM jacket_user_stats AS s "
                "LEFT JOIN jacket_account_bindings AS b "
                "ON b.official_platform = s.platform_name "
                "AND b.official_user_id = s.user_id "
                "WHERE b.official_user_id IS NULL "
                "OR s.platform_name != ? "
                "ORDER BY s.score DESC LIMIT ?",
                (OFFICIAL_PLATFORM_NAME, OFFICIAL_PLATFORM_NAME, limit),
            )
            return cursor.fetchall()
        finally:
            conn.close()


class JacketEffectProcessor:
    """曲绘图片效果处理器 - 支持可配置效果"""

    # 默认效果配置
    DEFAULT_EFFECTS = {
        "blur": {
            "name": "模糊",
            "description": "高斯模糊效果",
            "difficulty": 1,
            "blur_radius": 35,
            "enabled": True
        },
        "random_crop": {
            "name": "随机裁切",
            "description": "随机显示图片的一小部分区域",
            "difficulty": 1,
            "crop_ratio": 0.3,
            "enabled": True
        },
        "shuffle_blocks_easy": {
            "name": "分块打乱(简易)",
            "description": "将图片分割为较大方块并随机重新排列",
            "difficulty": 1,
            "block_size": 50,
            "enabled": True
        },
        "shuffle_blocks_hard": {
            "name": "分块打乱(困难)",
            "description": "将图片分割为较小方块并随机重新排列",
            "difficulty": 3,
            "block_size": 20,
            "enabled": True
        }
    }

    def __init__(self, config: Optional[dict] = None):
        """初始化效果处理器，可传入自定义配置"""
        self.EFFECTS = self._deep_copy_effects(self.DEFAULT_EFFECTS)
        if config:
            self.update_from_config(config)
        logger.info(f"效果处理器初始化完成，启用效果数量: {len(self.get_enabled_effects())}")

    def _deep_copy_effects(self, effects: dict) -> dict:
        """深拷贝效果配置"""
        import copy
        return copy.deepcopy(effects)

    def update_from_config(self, config: dict):
        """从配置中更新效果设置"""
        effects_config = config.get("effects", {})
        logger.debug(f"加载效果配置: {effects_config}")

        for effect_name, effect_config in effects_config.items():
            if effect_name in self.EFFECTS:
                if "enabled" in effect_config:
                    self.EFFECTS[effect_name]["enabled"] = bool(effect_config["enabled"])
                    logger.debug(f"设置 {effect_name} 启用状态: {effect_config['enabled']}")
                if "difficulty" in effect_config:
                    val = effect_config["difficulty"]
                    if isinstance(val, (int, float)) and 1 <= val <= 10:
                        self.EFFECTS[effect_name]["difficulty"] = int(val)
                        logger.debug(f"设置 {effect_name} 分数: {val}")
                if "blur_radius" in effect_config:
                    val = effect_config["blur_radius"]
                    if isinstance(val, (int, float)) and 1 <= val <= 100:
                        self.EFFECTS[effect_name]["blur_radius"] = int(val)
                        logger.debug(f"设置 {effect_name} 模糊半径: {val}")
                if "crop_ratio" in effect_config:
                    val = effect_config["crop_ratio"]
                    if isinstance(val, (int, float)) and 0.1 <= val <= 1.0:
                        self.EFFECTS[effect_name]["crop_ratio"] = float(val)
                        logger.debug(f"设置 {effect_name} 裁切比例: {val}")
                if "block_size" in effect_config:
                    val = effect_config["block_size"]
                    if isinstance(val, (int, float)) and 5 <= val <= 200:
                        self.EFFECTS[effect_name]["block_size"] = int(val)
                        logger.debug(f"设置 {effect_name} 区块大小: {val}")

    def get_enabled_effects(self) -> list[str]:
        """获取所有启用的效果列表"""
        enabled = [k for k, v in self.EFFECTS.items() if v.get("enabled", True)]
        logger.debug(f"启用的效果列表: {enabled}")
        return enabled

    def apply_blur(self, img: Image.Image, radius: int) -> Image.Image:
        """应用模糊效果"""
        return img.filter(ImageFilter.GaussianBlur(radius=radius))

    def apply_shuffle_blocks(self, img: Image.Image, block_size: int = 50) -> Image.Image:
        """应用分块打乱效果，确保无空白块"""
        try:
            w, h = img.size
            result = Image.new(img.mode, (w, h))

            # 创建网格位置列表
            positions = []
            for y in range(0, h, block_size):
                for x in range(0, w, block_size):
                    positions.append((x, y))

            # 打乱位置顺序
            shuffled_positions = positions.copy()
            random.shuffle(shuffled_positions)

            # 为每个原始位置分配一个新的打乱位置
            for idx, (orig_x, orig_y) in enumerate(positions):
                # 计算当前区块的实际大小
                current_w = min(block_size, w - orig_x)
                current_h = min(block_size, h - orig_y)

                # 从原始位置切割区块
                block = img.crop((orig_x, orig_y, orig_x + current_w, orig_y + current_h))

                # 获取打乱后的新位置
                new_x, new_y = shuffled_positions[idx]

                # 确保新位置也有对应的区块大小
                new_w = min(block_size, w - new_x)
                new_h = min(block_size, h - new_y)

                # 如果大小不一致，需要调整区块大小
                if current_w != new_w or current_h != new_h:
                    try:
                        block = block.resize((new_w, new_h), LANCZOS)
                    except Exception:
                        block = block.resize((new_w, new_h))

                # 将区块粘贴到新位置
                result.paste(block, (new_x, new_y))

            return result
        except Exception as e:
            logger.error(f"分块打乱处理失败: {e}", exc_info=True)
            return img

    def apply_random_crop(self, img: Image.Image, crop_ratio: float) -> Image.Image:
        """应用随机裁切效果，只显示图片的一小部分"""
        try:
            w, h = img.size
            # 计算显示区域的大小
            crop_w = int(w * crop_ratio)
            crop_h = int(h * crop_ratio)
            
            # 随机选择显示区域的位置
            max_x = w - crop_w
            max_y = h - crop_h
            x = random.randint(0, max(0, max_x))
            y = random.randint(0, max(0, max_y))
            
            # 裁切图片
            cropped = img.crop((x, y, x + crop_w, y + crop_h))
            return cropped
        except Exception as e:
            logger.error(f"随机裁切处理失败: {e}", exc_info=True)
            return img

    def apply_effect(self, img: Image.Image, effect_name: str, **kwargs) -> tuple[Image.Image, int]:
        """应用指定效果，返回处理后的图片和难度分数"""
        if effect_name not in self.EFFECTS:
            logger.warning(f"未知效果: {effect_name}")
            return img, 1

        effect_config = self.EFFECTS[effect_name]
        difficulty = effect_config.get("difficulty", 1)

        if effect_name == "blur":
            radius = kwargs.get("blur_radius", effect_config.get("blur_radius", 20))
            return self.apply_blur(img, radius), difficulty
        elif effect_name == "random_crop":
            crop_ratio = kwargs.get("crop_ratio", effect_config.get("crop_ratio", 0.4))
            return self.apply_random_crop(img, crop_ratio), difficulty
        elif effect_name == "shuffle_blocks_easy":
            block_size = kwargs.get("block_size", effect_config.get("block_size", 65))
            return self.apply_shuffle_blocks(img, block_size), difficulty
        elif effect_name == "shuffle_blocks_hard":
            block_size = kwargs.get("block_size", effect_config.get("block_size", 20))
            return self.apply_shuffle_blocks(img, block_size), difficulty

        return img, difficulty

    def random_effect(self) -> tuple[str, str, int]:
        """随机选择一个启用的效果，允许全部效果关闭。"""
        enabled_effects = self.get_enabled_effects()
        if not enabled_effects:
            logger.info("没有启用的曲绘效果，使用无效果局。")
            return "none", "无效果", 0

        effect_name = random.choice(enabled_effects)
        effect_info = self.EFFECTS[effect_name]
        return effect_name, effect_info["name"], effect_info["difficulty"]


@register(PLUGIN_NAME, PLUGIN_AUTHOR, PLUGIN_DESCRIPTION, PLUGIN_VERSION, PLUGIN_REPO_URL)
class GuessJacketPlugin(Star):
    """PJSK 猜曲绘插件主类"""

    def __init__(self, context: Context, config: 'AstrBotConfig'):
        super().__init__(context)
        self.config = config

        self.plugin_dir = Path(os.path.dirname(__file__))
        self.resources_dir = self.plugin_dir / "res"

        self.plugin_data_path = StarTools.get_data_dir(self.name)
        self.jacket_cache_dir = self.plugin_data_path / "jacket_cache"
        self.output_dir = self.plugin_data_path / "output"
        self.local_data_dir = self.plugin_data_path / "local_data"

        self._ensure_directories()

        self.db_path = str(self.plugin_data_path / "guess_jacket_data.db")
        self.db = JacketDatabaseManager(self.db_path)

        aliases_file = self.resources_dir / "aliases.json"
        songs_file = self.resources_dir / "songs.json"
        self.data_manager = LocalDataManager(
            self.local_data_dir,
            aliases_file if aliases_file.exists() else None,
            songs_file if songs_file.exists() else None
        )

        self.cloud_jacket_loader = CloudJacketLoader(self.jacket_cache_dir, self.config)

        font_path = self.resources_dir / "font.ttf"
        self.image_generator = ImageGenerator(
            font_path if font_path.exists() else None,
            self._get_display_name,
        )

        self.active_sessions: set = set()
        self.game_sessions: dict[str, JacketGameSession] = {}
        self.session_locks: dict[str, asyncio.Lock] = {}
        self.last_game_end_time: dict[str, float] = {}
        self.songs: list[SongInfo] = []
        self.data_initialized = False
        self.auto_sessions: set = set()
        self.auto_quit_flags: set = set()

        # --- 题库服务器偏好与 master 数据自动同步 ---
        self.server_prefs_path = self.plugin_data_path / "session_servers.json"
        self.server_prefs: dict = self._load_server_prefs()
        self.master_data = MasterDataService(
            self.plugin_data_path,
            update_interval_hours=int(config.get("update_interval_hours", 24)),
        )
        self.master_data.on_songs_updated = self._on_master_updated

        logger.info(f"初始化效果处理器，效果数量: {len(self.config.get('effects', {}))}")
        self.effect_processor = JacketEffectProcessor(dict(self.config))

        self._cleanup_output_dir()
        self._cleanup_task = None
        self._init_task = None
        self._master_task = None
        self._background_tasks: set[asyncio.Task] = set()
        self._stopping = False

        try:
            asyncio.get_running_loop()
            self._cleanup_task = self._track_task(asyncio.create_task(self._periodic_cleanup()))
            self._init_task = self._track_task(asyncio.create_task(self._initialize_data()))
            self._master_task = self._track_task(asyncio.create_task(self._start_master_data()))
        except RuntimeError:
            pass

        logger.info(f"PJSK Guess Jacket Plugin initialized (v{PLUGIN_VERSION})")

    # --- 题库服务器与 master 数据同步 ---

    def _track_task(self, task: asyncio.Task) -> asyncio.Task:
        self._background_tasks.add(task)
        task.add_done_callback(self._background_tasks.discard)
        return task

    async def _start_master_data(self):
        """启动歌曲题库自动同步服务。"""
        if self._stopping:
            return
        try:
            await self.master_data.start()
        except asyncio.CancelledError:
            raise
        except Exception as e:
            logger.error(f"题库同步服务启动失败: {e}", exc_info=True)

    def _load_server_prefs(self) -> dict:
        try:
            if self.server_prefs_path.exists():
                return json.loads(self.server_prefs_path.read_text(encoding="utf-8"))
        except Exception as e:
            logger.warning(f"加载题库服务器偏好失败: {e}")
        return {}

    def _save_server_prefs(self):
        try:
            self.server_prefs_path.write_text(
                json.dumps(self.server_prefs, ensure_ascii=False, indent=1),
                encoding="utf-8",
            )
        except Exception as e:
            logger.warning(f"保存题库服务器偏好失败: {e}")

    def _server_for_session(self, session_id: str) -> str:
        saved = self.server_prefs.get(session_id)
        if saved in (SERVER_JP, SERVER_SC):
            return saved
        default = str(self.config.get("default_server", SERVER_JP)).lower()
        return SERVER_SC if default == SERVER_SC else SERVER_JP

    def _on_master_updated(self):
        """master 数据更新后重建歌名/翻译/别名映射与曲池。"""
        try:
            union: list[dict] = []
            seen: set[int] = set()
            for server in (SERVER_JP, SERVER_SC):
                for song in self.master_data.get_songs(server):
                    if song.get("id") not in seen:
                        seen.add(song.get("id"))
                        union.append(song)
            if not union:
                return
            self.data_manager.apply_master_songs(union, replace=True)
            self.songs = self.data_manager.get_all_songs()
            self.data_initialized = True
            logger.info(f"[猜曲绘] 题库已随 master 数据更新，当前曲池 {len(self.songs)} 首。")
        except Exception as e:
            logger.error(f"应用 master 题库数据失败: {e}", exc_info=True)

    def _get_songs_for_session(self, session_id: str) -> list[SongInfo]:
        """获取会话当前服务器的曲池；master 题库未就绪时回退内置曲池。"""
        server = self._server_for_session(session_id)
        master_songs = self.master_data.get_songs(server)
        if master_songs:
            return [
                SongInfo(
                    music_id=s["id"],
                    original_name=s.get("title") or str(s["id"]),
                    cn_title=s.get("cn") or None,
                )
                for s in master_songs
            ]
        return self.songs

    # --- 官机 markdown 机制（与 PJSK Wordle 一致） ---

    def _build_connect_link(self, command: str, self_id: str, show: str | None = None) -> str:
        """按配置模板生成 markdown 格式的指令连接。

        默认使用 QQ 官方机器人 markdown 消息的参数指令标签
        <qqbot-cmd-input>：点击后在聊天框填入指令，QQ 客户端发送时会自动 @ 官方机器人。
        show 为展示名（默认与指令一致，如"点击回答"/"仅退出本局"）。
        可通过 connect_link_template 配置项适配环境，模板显式置空则退回纯文本。
        """
        template = self.config.get("connect_link_template")
        if template is None or any(marker in str(template) for marker in _LEGACY_TEMPLATE_MARKERS):
            template = DEFAULT_CONNECT_TEMPLATE
        template = str(template).strip()
        if not template:
            return f"（连接：@{self_id} {command}）"
        display = show or command
        at_text = f"@{self_id} {command}"
        return template.format(
            name=command,
            command=command,
            self_id=self_id,
            at_text=at_text,
            encoded_command=quote(command, safe=""),
            encoded_name=quote(display, safe=""),
            encoded_at_text=quote(at_text, safe=""),
        )

    def _get_official_connect_id(self, event: AstrMessageEvent) -> str:
        """返回官机连接模板的兼容 ID；默认 qqbot-cmd-input 不依赖该值。"""
        return self._get_official_self_id(event) or "qq_official"

    def _get_official_self_id(self, event: AstrMessageEvent) -> str:
        return str(getattr(event.message_obj, "self_id", "") or "").strip()

    async def _send_markdown_text(self, event: AstrMessageEvent, text: str):
        """以 QQ 官方机器人 markdown 消息发送纯文本（含连接标签）。"""
        result = event.make_result()
        result.chain = [Comp.Plain(text)]
        result.use_markdown(True)
        await event.send(result)

    def _get_quick_entries(self) -> list[str]:
        """读取快捷入口配置；若列表为空则不显示快捷入口。"""
        entries = self.config.get("quick_entries")
        if not entries:
            return []
        cleaned = [str(x).strip() for x in entries if str(x).strip()]
        wordle = "Wordle"
        if wordle in cleaned:
            cleaned = [x for x in cleaned if x != wordle] + [wordle]
        return cleaned

    def _build_server_footer(self, event: AstrMessageEvent, server: str) -> list:
        """构建结算消息的题库服务器尾部：官机附 markdown 连接入口与快捷入口，普通 QQ 仅提示指令。"""
        other = SERVER_SC if server == SERVER_JP else SERVER_JP
        switch_cmd = SWITCH_COMMANDS[server]
        connect_switch_cmd = CONNECT_SWITCH_COMMANDS[server]
        lines = [f"本局题库服务器：{SERVER_LABELS[server]}"]

        if self._get_event_platform_name(event) == OFFICIAL_PLATFORM_NAME:
            self_id = self._get_official_connect_id(event)
            if self_id:
                lines.append(self._build_connect_link(connect_switch_cmd, self_id))
                account_links = ["猜曲绘绑定QQ", "猜曲绘个人分数", "猜曲绘排行榜"]
                lines.append(
                    "  ".join(self._build_connect_link(name, self_id) for name in account_links)
                )
                entries = self._get_quick_entries()
                if entries:
                    lines.append("快捷入口：")
                    lines.append(
                        "  ".join(self._build_connect_link(name, self_id) for name in entries)
                    )
                return lines
        lines.append(f"你可以使用{switch_cmd}指令切换{SERVER_LABELS[other]}题库。")
        return lines

    def _is_at_bot(self, event: AstrMessageEvent) -> bool:
        """判断消息是否 @ 了本机器人（私聊/C2C 天然面向机器人，直接放行）。

        群聊一律要求消息链中存在指向机器人的 At 组件——QQ 官方机器人
        同样可能收到未 @ 的群消息，不能因为是官方平台就无条件放行。
        """
        if not event.get_group_id():
            return True
        self_id = str(getattr(event.message_obj, "self_id", "") or "").strip()
        for comp in getattr(event.message_obj, "message", None) or []:
            if isinstance(comp, Comp.At):
                comp_qq = str(getattr(comp, "qq", ""))
                # self_id 缺失时放宽为"消息中存在任意 At"（个别适配器不回填 self_id）
                if not self_id or comp_qq == self_id:
                    return True
        return False

    async def _switch_server(self, event: AstrMessageEvent, server: str):
        """切换当前会话的题库服务器。"""
        session_id = event.unified_msg_origin
        if session_id in self.active_sessions:
            await event.send(event.plain_result("本局游戏还在进行中，结束后再切换题库服务器吧。"))
            return
        current = self._server_for_session(session_id)
        if current == server:
            await event.send(event.plain_result(f"当前题库已经是{SERVER_LABELS[server]}题库了。"))
            return
        self.server_prefs[session_id] = server
        self._save_server_prefs()
        count = self.master_data.get_song_count(server)
        version = self.master_data.get_version(server)
        await event.send(
            event.plain_result(
                f"已切换为{SERVER_BADGES[server]}（共 {count} 首，版本 {version}），下一局生效。"
            )
        )

    def _ensure_directories(self):
        """确保必要的目录存在"""
        os.makedirs(self.jacket_cache_dir, exist_ok=True)
        os.makedirs(self.output_dir, exist_ok=True)
        os.makedirs(self.local_data_dir, exist_ok=True)

    async def _initialize_data(self):
        """初始化数据"""
        try:
            self.songs = self.data_manager.get_all_songs()
            logger.info(
                f"Data initialization complete. "
                f"{len(self.data_manager.cn_map)} translations, "
                f"{len(self.songs)} songs"
            )
            self.data_initialized = True
        except Exception as e:
            logger.error(f"Failed to initialize data: {e}")

    def _cleanup_output_dir(self):
        """清理旧输出图片"""
        if not self.output_dir.exists():
            return

        now = time.time()
        try:
            for file_path in self.output_dir.iterdir():
                if file_path.is_file() and (now - file_path.stat().st_mtime) > Config.MAX_AGE_SECONDS:
                    file_path.unlink()
        except Exception as e:
            logger.error(f"Cleanup error: {e}")

    async def _periodic_cleanup(self):
        """定期清理任务"""
        while True:
            await asyncio.sleep(Config.CLEANUP_INTERVAL)
            self._cleanup_output_dir()
            self._cleanup_old_sessions()

    def _cleanup_old_sessions(self):
        """清理过期的会话数据，防止内存泄漏"""
        now = time.time()
        max_age = 3600

        expired_sessions = [
            sid for sid, last_time in self.last_game_end_time.items()
            if now - last_time > max_age
        ]
        for sid in expired_sessions:
            self.last_game_end_time.pop(sid, None)
            if sid not in self.active_sessions:
                self.session_locks.pop(sid, None)

        if expired_sessions:
            logger.info(f"Cleaned up {len(expired_sessions)} expired session data")

    def _is_group_allowed(self, event: AstrMessageEvent) -> bool:
        """检查群组是否在白名单中"""
        whitelist = {str(x) for x in self.config.get("group_whitelist", [])}
        if not whitelist:
            return True
        group_id = event.get_group_id()
        return bool(group_id and str(group_id) in whitelist)

    def _get_whitelist_reject_message(self) -> Optional[str]:
        """获取白名单拒绝提示信息"""
        msg = self.config.get("whitelist_reject_message", "")
        if msg and msg.strip():
            return msg.strip()
        return None

    def _is_user_blacklisted(self, user_id: str) -> bool:
        """检查用户是否在黑名单中"""
        return str(user_id) in {str(x) for x in self.config.get("blacklist", [])}

    @staticmethod
    def _get_event_platform_name(event: AstrMessageEvent) -> str:
        """获取事件的平台适配器名称，兼容旧版事件对象。"""
        getter = getattr(event, "get_platform_name", None)
        try:
            platform_name = getter() if callable(getter) else DEFAULT_PLATFORM_NAME
        except Exception:
            platform_name = DEFAULT_PLATFORM_NAME
        return str(platform_name or DEFAULT_PLATFORM_NAME).strip().lower()

    def _is_qq_official_event(self, event: AstrMessageEvent) -> bool:
        return self._get_event_platform_name(event) == OFFICIAL_PLATFORM_NAME

    def _get_account_identity(self, event: AstrMessageEvent) -> tuple[str, str]:
        """返回用于积分和次数统计的规范化账号 ID 与平台。"""
        platform_name = self._get_event_platform_name(event)
        raw_user_id = str(event.get_sender_id())
        resolver = getattr(self.db, "resolve_user_id", None)
        resolved_user_id = (
            resolver(platform_name, raw_user_id)
            if callable(resolver)
            else raw_user_id
        )
        if str(resolved_user_id) != raw_user_id:
            return str(resolved_user_id), DEFAULT_PLATFORM_NAME
        return raw_user_id, platform_name

    def _is_event_user_blacklisted(
        self,
        event: AstrMessageEvent,
        canonical_user_id: Optional[str] = None,
    ) -> bool:
        raw_user_id = str(event.get_sender_id())
        return self._is_user_blacklisted(raw_user_id) or (
            canonical_user_id is not None
            and self._is_user_blacklisted(canonical_user_id)
        )

    @staticmethod
    def _build_binding_confirmation_message(qq_user_id: str) -> str:
        return (
            f"你确认将账号绑定至  {qq_user_id} ？官方机作答的分数将迁移至该账号。\n"
            "发送“确认”将开始绑定。发送“取消”将取消绑定。"
        )

    def _get_display_name(self, user_id: str, original_name: Optional[str] = None) -> str:
        """获取用户显示名称，黑名单用户显示统一标识"""
        if self._is_user_blacklisted(user_id):
            return "[此用户已被BOT拉黑]"
        return original_name if original_name else "未知用户"

    def _is_super_user(self, user_id: str) -> bool:
        """检查是否为超级用户"""
        super_users = {str(x) for x in self.config.get("super_users", [])}
        return bool(super_users) and str(user_id) in super_users

    def get_random_song(self) -> Optional[SongInfo]:
        """获取随机歌曲"""
        return random.choice(self.songs) if self.songs else None

    async def _load_random_jacket(self, songs: Optional[list[SongInfo]] = None, server: str = SERVER_JP) -> Optional[tuple[SongInfo, Image.Image]]:
        """随机尝试加载曲绘，失败时换下一首歌曲并避免重复尝试。"""
        if songs is None:
            songs = self.songs
        attempted_ids: set[int] = set()
        max_attempts = min(Config.MAX_JACKET_LOAD_ATTEMPTS, len(songs))

        for attempt in range(max_attempts):
            candidates = [
                song for song in songs
                if song.music_id not in attempted_ids
            ]
            if not candidates:
                break

            correct_song = random.choice(candidates)
            attempted_ids.add(correct_song.music_id)
            jacket_img = await asyncio.to_thread(
                self.cloud_jacket_loader.load_jacket_image,
                correct_song.music_id,
                server,
            )
            if jacket_img:
                if attempt:
                    logger.info(
                        f"曲绘加载重试成功: 第{attempt + 1}次，music_id={correct_song.music_id}"
                    )
                return correct_song, jacket_img

            logger.warning(
                f"曲绘加载失败，跳过歌曲: attempt={attempt + 1}/"
                f"{max_attempts}, music_id={correct_song.music_id}"
            )

        logger.warning(
            f"本轮曲绘加载失败: attempted={len(attempted_ids)}, "
            f"max_attempts={Config.MAX_JACKET_LOAD_ATTEMPTS}"
        )
        return None

    async def _guess_jacket_impl(self, event: AstrMessageEvent, auto_mode: bool):
        """猜曲绘核心实现，支持自动模式循环"""
        session_id = event.unified_msg_origin
        user_id, user_platform = self._get_account_identity(event)

        if session_id not in self.session_locks:
            self.session_locks[session_id] = asyncio.Lock()

        async with self.session_locks[session_id]:
            if session_id in self.active_sessions:
                yield event.plain_result("当前已经有一个猜曲绘游戏在进行中啦~ 等它结束后再来玩吧！")
                return

            cooldown = self.config.get("game_cooldown_seconds", Config.DEFAULT_COOLDOWN)
            last_end_time = self.last_game_end_time.get(session_id, 0)
            time_since_last_game = time.time() - last_end_time

            if time_since_last_game < cooldown:
                remaining_time = cooldown - time_since_last_game
                time_display = f"{remaining_time:.1f}" if remaining_time < 1 else str(int(remaining_time))
                yield event.plain_result(f"让我们休息一下吧！{time_display}秒后再来玩哦~ 😊")
                return

            daily_limit = self.config.get("daily_play_limit", Config.DEFAULT_DAILY_LIMIT)
            can_play = await asyncio.to_thread(
                self.db.can_play_today,
                user_id,
                daily_limit,
                user_platform,
            )
            if not can_play:
                yield event.plain_result(f"今天的游戏次数已经用完啦~ 明天再来玩吧！每天最多可以玩{daily_limit}次哦~ ✨")
                return

            self.active_sessions.add(session_id)

        try:
            consecutive_no_answer = 0
            songs = self._get_songs_for_session(session_id)
            round_server = self._server_for_session(session_id)
            while True:
                if not songs:
                    yield event.plain_result("歌曲数据未加载，请稍后再试。")
                    return

                jacket_result = await self._load_random_jacket(songs, round_server)
                if not jacket_result:
                    yield event.plain_result("曲绘服务暂时不可用，已自动重试，请稍后再试。")
                    return

                correct_song, jacket_img = jacket_result

                effect_name, effect_display, difficulty = self.effect_processor.random_effect()

                try:
                    processed_img, actual_difficulty = await asyncio.to_thread(
                        self.effect_processor.apply_effect, jacket_img, effect_name
                    )

                    processed_path = self.output_dir / f"jacket_{time.time_ns()}.png"
                    try:
                        await asyncio.to_thread(processed_img.save, processed_path)
                    finally:
                        if processed_img is not jacket_img:
                            processed_img.close()
                        jacket_img.close()

                    game_data = JacketGameData(
                        correct_song=correct_song,
                        effect_name=effect_name,
                        effect_display_name=effect_display,
                        difficulty=actual_difficulty,
                        score=actual_difficulty
                    )

                except Exception as e:
                    logger.error(f"Failed to process jacket image: {e}")
                    yield event.plain_result("处理封面图片时出错，请稍后再试。")
                    return

                await asyncio.to_thread(
                    self.db.update_user_play,
                    user_id,
                    event.get_sender_name(),
                    user_platform,
                )

                game_session = JacketGameSession(game_data=game_data)
                self.game_sessions[session_id] = game_session

                timeout_seconds = self.config.get("answer_timeout", Config.DEFAULT_TIMEOUT)
                is_official_round = self._get_event_platform_name(event) == OFFICIAL_PLATFORM_NAME
                official_self_id = self._get_official_connect_id(event) if is_official_round else ""
                if is_official_round:
                    # 官方机器人：wordle 应答制
                    intro_text = (
                        "PJSK 猜曲绘开始！\n"
                        f"请在{timeout_seconds}秒内回答：@本机器人 + 歌名或别名\n"
                        f"效果: {effect_display}\n"
                        f"难度: {'⭐' * actual_difficulty}\n"
                        f"得分: {actual_difficulty}分\n"
                        f"提示: 支持中文名、别名回答，支持模糊匹配"
                    )
                else:
                    intro_text = (
                        f"请在{timeout_seconds}秒内输入歌曲名称回答~\n"
                        f"效果: {effect_display}\n"
                        f"难度: {'⭐' * actual_difficulty}\n"
                        f"得分: {actual_difficulty}分\n"
                        f"提示: 支持中文名、原名、别名回答，支持模糊匹配"
                    )

                if is_official_round:
                    # 官方机器人以 markdown 发送开局消息
                    if auto_mode:
                        intro_text += (
                            "\n"
                            + self._build_connect_link(" ", official_self_id, show="点击回答")
                            + "  "
                            + self._build_connect_link("退出本局", official_self_id)
                            + "  "
                            + self._build_connect_link("退出自动模式", official_self_id)
                        )
                    else:
                        intro_text += (
                            "\n"
                            + self._build_connect_link(" ", official_self_id, show="点击回答")
                            + "  "
                            + self._build_connect_link("退出本局", official_self_id)
                        )
                    try:
                        await self._send_markdown_text(event, intro_text)
                        yield event.chain_result([Comp.Image(file=str(processed_path))])
                    except Exception as e:
                        logger.error(f"发送开局消息失败: {e}", exc_info=True)
                        yield event.plain_result("发送开局消息时出错，游戏中断。")
                        return
                elif auto_mode:
                    # 自动模式（非官机）：文字提示退出方式
                    intro_text += "\n发送「退出」可结束自动模式，发送「退出本局」可提前结束这一局。"
                    yield event.chain_result([
                        Comp.Plain(intro_text),
                        Comp.Image(file=str(processed_path))
                    ])
                else:
                    # 普通模式（非官机）：提示「退出本局」指令可提前结束这一局
                    intro_text += "\n发送「退出本局」可提前结束这一局。"
                    yield event.chain_result([
                        Comp.Plain(intro_text),
                        Comp.Image(file=str(processed_path))
                    ])

                answered_correctly = False
                winner_name = None
                winner_id = None
                winner_platform = None
                winners_list = []
                first_correct_time = None
                reward_valid_time = self.config.get("reward_valid_time", 0)
                user_quit = False
                quitter_name = None
                quit_ended_round = False
                any_genuine_attempt = False
                failed_attempters = []

                logger.info(f"[猜曲绘] 奖励有效时间配置: {reward_valid_time}秒")

                @session_waiter(timeout=timeout_seconds)
                async def jacket_waiter(controller: SessionController, answer_event: AstrMessageEvent):
                    nonlocal answered_correctly, winner_name, winner_id, winner_platform, first_correct_time, winners_list, user_quit, quitter_name
                    nonlocal any_genuine_attempt, quit_ended_round

                    # 官方机器人平台：wordle 应答制，仅处理 @机器人 的消息
                    if is_official_round and not self._is_at_bot(answer_event):
                        return

                    answer_text = answer_event.message_str.strip()
                    if not answer_text:
                        return

                    # 仅退出本局：支持「仅退出本局」、「退出本局」；若非自动模式，发送「退出」也视为退出本局
                    if answer_text in ["仅退出本局", "退出本局"] or (answer_text == "退出" and not auto_mode):
                        quit_ended_round = True
                        controller.stop()
                        return

                    # 退出自动模式：任何时候可触发，本局继续、自动模式停止
                    if answer_text in ["退出自动模式", "退出"]:
                        user_quit = True
                        quitter_name = answer_event.get_sender_name()
                        if auto_mode:
                            self.auto_quit_flags.add(session_id)
                        await answer_event.send(answer_event.plain_result("已退出自动模式，本局结束后将停止猜曲绘模式。"))
                        return

                    is_correct, matched_name = self.data_manager.check_answer(
                        game_session.game_data.correct_song.music_id,
                        answer_text
                    )

                    if is_correct:
                        answerer_id, answerer_platform = self._get_account_identity(answer_event)
                        if self._is_event_user_blacklisted(answer_event, answerer_id):
                            return
                        daily_limit = self.config.get("daily_play_limit", Config.DEFAULT_DAILY_LIMIT)
                        can_play = await asyncio.to_thread(
                            self.db.can_play_today,
                            answerer_id,
                            daily_limit,
                            answerer_platform,
                        )
                        if not can_play:
                            return

                        current_time = time.time()

                        if not answered_correctly:
                            answered_correctly = True
                            winner_name = answer_event.get_sender_name()
                            winner_id = answerer_id
                            winner_platform = answerer_platform
                            first_correct_time = current_time
                            winners_list.append({
                                'user_id': answerer_id,
                                'platform_name': answerer_platform,
                                'user_name': answer_event.get_sender_name(),
                                'answer_time': current_time,
                                'is_first': True
                            })

                            if reward_valid_time > 0:
                                logger.info(f"[猜曲绘] 第一个答对者: {winner_name}，启动{reward_valid_time}秒奖励有效时间")
                                async def stop_after_delay():
                                    await asyncio.sleep(reward_valid_time)
                                    controller.stop()
                                asyncio.create_task(stop_after_delay())
                            else:
                                controller.stop()
                        else:
                            time_since_first_correct = current_time - first_correct_time
                            if time_since_first_correct <= reward_valid_time and reward_valid_time > 0:
                                if not any(w['user_id'] == answerer_id for w in winners_list):
                                    winners_list.append({
                                        'user_id': answerer_id,
                                        'platform_name': answerer_platform,
                                        'user_name': answer_event.get_sender_name(),
                                        'answer_time': current_time,
                                        'is_first': False
                                    })
                                    logger.info(f"[猜曲绘] 奖励有效时间内额外答对: {answer_event.get_sender_name()} (+{time_since_first_correct:.2f}s)")
                    else:
                        # 精确命中其他歌曲名才算真实作答，闲聊不计入统计
                        if self.data_manager.is_known_song_name(answer_text):
                            any_genuine_attempt = True
                            answerer_id, answerer_platform = self._get_account_identity(answer_event)
                            if not self._is_event_user_blacklisted(answer_event, answerer_id):
                                if not any(
                                    w['user_id'] == answerer_id and w['platform_name'] == answerer_platform
                                    for w in failed_attempters
                                ):
                                    failed_attempters.append({
                                        'user_id': answerer_id,
                                        'platform_name': answerer_platform,
                                        'user_name': answer_event.get_sender_name(),
                                    })

                try:
                    await jacket_waiter(event)
                except TimeoutError:
                    game_session.game_ended_by_timeout = True

                # 有人答对或有人真实作答都算本局有回答，仅整局无人作答才累计
                if answered_correctly or any_genuine_attempt:
                    consecutive_no_answer = 0
                else:
                    consecutive_no_answer += 1

                correct_song = game_session.game_data.correct_song
                correct_name = correct_song.display_name

                # 真实答错的玩家按本人记一次失败尝试（每局每人最多一次）
                for failed in failed_attempters:
                    await asyncio.to_thread(
                        self.db.update_user_score,
                        failed['user_id'],
                        failed['user_name'],
                        0,
                        False,
                        failed['platform_name'],
                    )

                if quit_ended_round:
                    result_text = f"本局已结束（仅退出本局）\n正确答案: {correct_name}"
                elif game_session.game_ended_by_timeout:
                    result_text = f"⏰ 时间到！\n正确答案: {correct_name}"
                elif answered_correctly:
                    if len(winners_list) == 1:
                        result_text = f"🎉 {winner_name}答对了！获得{game_session.game_data.score}分！\n正确答案: {correct_name}"
                        await asyncio.to_thread(
                            self.db.update_user_score,
                            winner_id,
                            winner_name,
                            game_session.game_data.score,
                            True,
                            winner_platform,
                        )
                    else:
                        winner_names = [w['user_name'] for w in winners_list]
                        result_text = (
                            f"🎉 恭喜以下玩家答对！每人获得{game_session.game_data.score}分！\n"
                            f"{'、'.join(winner_names)}\n\n"
                            f"正确答案: {correct_name}"
                        )

                        for winner in winners_list:
                            await asyncio.to_thread(
                                self.db.update_user_score,
                                winner['user_id'],
                                winner['user_name'],
                                game_session.game_data.score,
                                True,
                                winner['platform_name'],
                            )
                else:
                    result_text = f"❌ 无人答对！\n正确答案: {correct_name}"

                if not answered_correctly and not any_genuine_attempt:
                    # 整局无任何真实作答时，才由发起者承担本局的失败记录
                    await asyncio.to_thread(
                        self.db.update_user_score,
                        user_id,
                        event.get_sender_name(),
                        0,
                        False,
                        user_platform,
                    )

                if user_quit and not quit_ended_round:
                    result_text += "\n已退出自动模式，本局结束后将停止猜曲绘模式"
                elif consecutive_no_answer >= 3 and auto_mode:
                    self.auto_quit_flags.add(session_id)
                    result_text += f"\n连续{consecutive_no_answer}局无人回答，自动猜曲绘已停止"
                elif auto_mode and session_id not in self.auto_quit_flags:
                    result_text += "\n自动猜曲绘模式：3秒后开始下一局，发送「退出自动模式」可停止"

                if auto_mode and session_id not in self.auto_quit_flags and not user_quit:
                    # 自动模式：只显示结果与歌名，随后自动开始下一局，不出现 markdown 按钮
                    yield event.plain_result(result_text)
                else:
                    result_text += "\n" + "\n".join(
                        self._build_server_footer(event, round_server)
                    )
                    if is_official_round:
                        # 官方机器人以 markdown 渲染结算消息，附切换/绑定/查分/排行榜连接与快捷入口
                        await self._send_markdown_text(event, result_text)
                    else:
                        yield event.plain_result(result_text)

                original_jacket_img = await asyncio.to_thread(
                    self.cloud_jacket_loader.load_jacket_image, correct_song.music_id, round_server
                )
                if original_jacket_img:
                    original_path = self.output_dir / f"original_{time.time_ns()}.png"
                    try:
                        await asyncio.to_thread(original_jacket_img.save, original_path)
                        yield event.image_result(str(original_path))
                    finally:
                        original_jacket_img.close()


                self.active_sessions.discard(session_id)
                self.game_sessions.pop(session_id, None)
                self.last_game_end_time[session_id] = time.time()

                if not auto_mode or session_id in self.auto_quit_flags:
                    break

                # 自动模式间隙：等待并检测退出
                quit_in_gap = False
                gap_quitter_name = None

                @session_waiter(timeout=3)
                async def gap_waiter(controller: SessionController, gap_event: AstrMessageEvent):
                    nonlocal quit_in_gap, gap_quitter_name
                    # 官方机器人平台仅响应 @机器人 的指令
                    if self._get_event_platform_name(gap_event) == OFFICIAL_PLATFORM_NAME and not self._is_at_bot(gap_event):
                        return
                    if gap_event.message_str.strip() in ["退出自动模式", "退出"]:
                        quit_in_gap = True
                        gap_quitter_name = gap_event.get_sender_name()
                        self.auto_quit_flags.add(session_id)
                        controller.stop()

                try:
                    await gap_waiter(event)
                except TimeoutError:
                    pass

                if quit_in_gap:
                    yield event.plain_result(f"已退出自动猜曲绘模式~")
                    break

                self.last_game_end_time.pop(session_id, None)

        finally:
            self.active_sessions.discard(session_id)
            self.game_sessions.pop(session_id, None)
            self.last_game_end_time[session_id] = time.time()
            self.auto_sessions.discard(session_id)
            self.auto_quit_flags.discard(session_id)

    @filter.command("猜曲绘切换国服题库", alias={"猜曲绘切换国服"})
    async def switch_to_sc(self, event: AstrMessageEvent):
        """切换为国服题库。"""
        await self._switch_server(event, SERVER_SC)

    @filter.command("猜曲绘切换日服题库", alias={"猜曲绘切换日服"})
    async def switch_to_jp(self, event: AstrMessageEvent):
        """切换为日服题库。"""
        await self._switch_server(event, SERVER_JP)

    @filter.command("猜曲绘绑定", alias={"pjsk猜曲绘绑定", "曲绘猜曲绑定", "猜曲绘绑定QQ"})
    async def bind_jacket_account(self, event: AstrMessageEvent):
        """QQ 官方机器人账号绑定到普通 QQ 账号。"""
        if not self._is_qq_official_event(event):
            yield event.plain_result("此绑定功能仅支持 QQ 官方机器人使用。")
            return

        parts = event.message_str.strip().split(maxsplit=1)
        qq_user_id = parts[1].strip() if len(parts) > 1 else ""
        if not re.fullmatch(r"\d{5,12}", qq_user_id):
            yield event.plain_result("请按“猜曲绘绑定 QQ号”的格式输入，例如：猜曲绘绑定 21555762216。")
            return

        official_user_id = str(event.get_sender_id())
        current_user_id = await asyncio.to_thread(
            self.db.resolve_user_id,
            OFFICIAL_PLATFORM_NAME,
            official_user_id,
        )
        if str(current_user_id) != official_user_id:
            yield event.plain_result(f"当前官方机器人账号已经绑定至 QQ号 {current_user_id}。")
            return

        yield event.plain_result(
            self._build_binding_confirmation_message(qq_user_id)
        )

        decision = None

        @session_waiter(timeout=60)
        async def binding_waiter(
            controller: SessionController,
            answer_event: AstrMessageEvent,
        ):
            nonlocal decision
            answer_text = answer_event.message_str.strip()
            if answer_text == "确认":
                decision = "confirm"
                controller.stop()
            elif answer_text == "取消":
                decision = "cancel"
                controller.stop()

        try:
            await binding_waiter(
                event,
                session_filter=BindingSessionFilter(
                    event.unified_msg_origin,
                    official_user_id,
                ),
            )
        except TimeoutError:
            yield event.plain_result("绑定确认已超时，绑定操作已取消。")
            return

        if decision == "cancel":
            yield event.plain_result("已取消绑定。")
            return
        if decision != "confirm":
            yield event.plain_result("未收到有效的绑定确认，绑定操作已取消。")
            return

        bound = await asyncio.to_thread(
            self.db.bind_official_account,
            OFFICIAL_PLATFORM_NAME,
            official_user_id,
            qq_user_id,
        )
        if bound:
            yield event.plain_result(
                f"绑定成功！官方机的历史分数已迁移至 QQ号 {qq_user_id}。"
            )
        else:
            yield event.plain_result("绑定失败：该官方账号可能已绑定，请稍后重试。")

    @filter.command("猜曲绘", alias={"pjsk猜曲绘", "曲绘猜曲", "猜封面"})
    async def start_guess_jacket(self, event: AstrMessageEvent):
        """开始猜曲绘游戏"""
        if not self.data_initialized:
            yield event.plain_result("数据正在初始化中，请稍后再试...")
            return

        if not self._is_group_allowed(event):
            reject_msg = self._get_whitelist_reject_message()
            if reject_msg:
                yield event.plain_result(reject_msg)
            return

        canonical_user_id, _ = self._get_account_identity(event)
        if self._is_event_user_blacklisted(event, canonical_user_id):
            yield event.plain_result("抱歉，你已被禁止使用此功能 😔")
            return

        async for result in self._guess_jacket_impl(event, auto_mode=False):
            yield result

    @filter.command("自动猜曲绘", alias={"自动猜封面"})
    async def start_auto_guess_jacket(self, event: AstrMessageEvent):
        """开始自动猜曲绘游戏"""
        if not self.data_initialized:
            yield event.plain_result("数据正在初始化中，请稍后再试...")
            return

        if not self._is_group_allowed(event):
            reject_msg = self._get_whitelist_reject_message()
            if reject_msg:
                yield event.plain_result(reject_msg)
            return

        canonical_user_id, _ = self._get_account_identity(event)
        if self._is_event_user_blacklisted(event, canonical_user_id):
            yield event.plain_result("抱歉，你已被禁止使用此功能 😔")
            return

        session_id = event.unified_msg_origin
        self.auto_sessions.add(session_id)
        self.auto_quit_flags.discard(session_id)

        yield event.plain_result("已开启自动猜曲绘模式！发送「退出自动模式」可随时停止~")

        async for result in self._guess_jacket_impl(event, auto_mode=True):
            yield result

    @filter.command("退出自动模式", alias={"退出"})
    async def quit_auto_mode(self, event: AstrMessageEvent):
        """退出自动猜曲绘模式（对局进行中时由对局等待器处理）"""
        session_id = event.unified_msg_origin
        if session_id not in self.auto_sessions and session_id not in self.active_sessions:
            return
        self.auto_sessions.discard(session_id)
        self.auto_quit_flags.add(session_id)
        yield event.plain_result("已退出自动猜曲绘模式。")

    @filter.command("猜曲绘分数", alias={"pjsk猜曲绘分数", "曲绘猜曲分数", "猜曲绘个人分数"})
    async def show_jacket_score(self, event: AstrMessageEvent):
        """显示猜曲绘分数"""
        if not self._is_group_allowed(event):
            reject_msg = self._get_whitelist_reject_message()
            if reject_msg:
                yield event.plain_result(reject_msg)
            return

        raw_user_id = str(event.get_sender_id())
        raw_platform_name = self._get_event_platform_name(event)
        user_id, platform_name = self._get_account_identity(event)
        user_name = event.get_sender_name()

        platform_display_name = {
            OFFICIAL_PLATFORM_NAME: "QQ官方机器人",
            DEFAULT_PLATFORM_NAME: "普通QQ",
        }.get(raw_platform_name, raw_platform_name)
        identity_lines = [
            f"👤 用户ID: {raw_user_id}",
            f"🌐 平台: {platform_display_name}（{raw_platform_name}）",
        ]
        if raw_platform_name == OFFICIAL_PLATFORM_NAME:
            if user_id != raw_user_id:
                identity_lines.append(f"🔗 统计账号: {user_id}")
            else:
                identity_lines.extend([
                    "当前官方机器人账号尚未绑定QQ号。",
                    "如需将官方机分数迁移到普通QQ账号，请发送：猜曲绘绑定 QQ号",
                ])
        identity_text = "\n".join(identity_lines)

        user_data = await asyncio.to_thread(
            self.db.get_user_stats,
            user_id,
            platform_name,
        )
        if not user_data:
            yield event.plain_result(
                f"{identity_text}\n\n"
                f"{user_name}，你还没有参与过猜曲绘游戏哦！快来一起玩呀~ 🎮"
            )
            return

        score, attempts, correct_attempts, last_play_date, daily_plays = user_data
        accuracy = (correct_attempts * 100 / attempts) if attempts > 0 else 0
        rank = await asyncio.to_thread(self.db.get_user_rank, score)

        daily_limit = self.config.get("daily_play_limit", Config.DEFAULT_DAILY_LIMIT)
        today = time.strftime("%Y-%m-%d")

        if daily_limit == -1:
            remaining_plays = "无限次数"
        elif last_play_date == today:
            remaining = daily_limit - daily_plays
            remaining_plays = f"{remaining}次" if remaining > 0 else "0次"
        else:
            remaining_plays = f"{daily_limit}次"

        stats_text = (
            f"🎨 {user_name} 的猜曲绘数据 🎨\n"
            f"{identity_text}\n"
            f"🏆 总分: {score} 分\n"
            f"🎯 正确率: {accuracy:.1f}%\n"
            f"🎮 游戏次数: {attempts} 次\n"
            f"✅ 答对次数: {correct_attempts} 次\n"
            f"🏅 当前排名: 第 {rank} 名\n"
            f"📅 今日剩余: {remaining_plays}\n"
        )

        yield event.plain_result(stats_text)

    @filter.command(
        "猜曲绘排行榜",
        alias={
            "pjsk猜曲绘排行榜",
            "曲绘猜曲排行",
            "猜曲绘排行",
            "本地猜曲绘排行榜",
        },
    )
    async def show_jacket_ranking(self, event: AstrMessageEvent):
        """显示猜曲绘排行榜"""
        if not self._is_group_allowed(event):
            reject_msg = self._get_whitelist_reject_message()
            if reject_msg:
                yield event.plain_result(reject_msg)
            return

        self._cleanup_output_dir()

        ranking_count = self.config.get("ranking_display_count", 10)
        ranking_count = max(1, min(int(ranking_count), 50))
        rows = await asyncio.to_thread(self.db.get_ranking, ranking_count)

        if not rows:
            yield event.plain_result("还没有人参与过猜曲绘游戏呢~ 快来一起玩呀！✨")
            return

        try:
            img_path = await asyncio.to_thread(
                self.image_generator.create_ranking_image, rows, self.output_dir
            )
            if img_path:
                yield event.image_result(str(img_path))
            else:
                yield event.plain_result("生成排行榜图片时出错，请联系管理员。")
        except Exception as e:
            logger.error(f"使用Pilmoji生成排行榜图片失败: {e}", exc_info=True)
            yield event.plain_result("生成排行榜图片时出错，请联系管理员。")

    @filter.command("猜曲绘自定义名称", alias={"猜曲绘昵称", "曲绘自定义名称"})
    async def set_jacket_custom_name(self, event: AstrMessageEvent):
        """设置猜曲绘自定义名称"""
        if not self._is_group_allowed(event):
            reject_msg = self._get_whitelist_reject_message()
            if reject_msg:
                yield event.plain_result(reject_msg)
            return

        sender_id, platform_name = self._get_account_identity(event)
        parts = event.message_str.strip().split(maxsplit=1)
        custom_name = parts[1].strip() if len(parts) > 1 else None

        if custom_name:
            if len(custom_name) > 20:
                yield event.plain_result("自定义名称过长，请限制在20个字符以内哦~")
                return
            if any(c in custom_name for c in ['\n', '\r', '\t', '\0']):
                yield event.plain_result("自定义名称包含非法字符，请重新输入~")
                return
            await asyncio.to_thread(
                self.db.set_custom_name,
                sender_id,
                event.get_sender_name(),
                custom_name,
                platform_name,
            )
            yield event.plain_result(f"好的！你的猜曲绘自定义名称已设置为：{custom_name} ✨")
        else:
            result = await asyncio.to_thread(
                self.db.set_custom_name,
                sender_id,
                event.get_sender_name(),
                None,
                platform_name,
            )
            if result:
                yield event.plain_result("好的！你的猜曲绘自定义名称已清除 ✨")
            else:
                yield event.plain_result("你还没有参与过猜曲绘游戏哦~ 🎮")

    @filter.command("猜曲绘帮助", alias={"pjsk猜曲绘帮助"})
    async def show_help(self, event: AstrMessageEvent):
        """显示帮助信息"""
        if not self._is_group_allowed(event):
            reject_msg = self._get_whitelist_reject_message()
            if reject_msg:
                yield event.plain_result(reject_msg)
            return

        # 获取当前启用的效果列表
        enabled_effects = self.effect_processor.get_enabled_effects()
        effects_text = "\n".join([
            f"- {self.effect_processor.EFFECTS[e]['name']}: {'⭐' * self.effect_processor.EFFECTS[e]['difficulty']} ({self.effect_processor.EFFECTS[e]['difficulty']}分)"
            for e in enabled_effects
        ]) if enabled_effects else "暂无启用的效果"

        help_text = (
            "🎨 PJSK 猜曲绘指南 🎨\n\n"
            "【猜曲绘】\n"
            "猜曲绘 - 随机一首歌曲，展示处理后的封面，猜出歌名！\n"
            "自动猜曲绘 - 开启自动模式，一局结束后自动开始下一局\n"
            "猜曲绘切换日服题库/猜曲绘切换国服题库 - 切换题库服务器（下一局生效）\n"
            "猜曲绘绑定 QQ号 - QQ官方机器人绑定到你的QQ号，需发送“确认”\n"
            "猜曲绘分数 - 查看自己的游戏数据统计\n"
            "猜曲绘排行榜 - 查看总分排行榜\n"
            "猜曲绘自定义名称 - 设置你的个性化ID\n\n"
            "【管理员指令】\n"
            "刷新本地数据 - 重新加载本地别名数据\n\n"
            "【当前启用的效果】\n"
            f"{effects_text}"
        )
        yield event.plain_result(help_text)

    @filter.command("刷新本地数据", alias={"重载本地数据", "刷新数据"})
    async def reload_local_data(self, event: AstrMessageEvent):
        """刷新本地数据"""
        if not self._is_group_allowed(event):
            reject_msg = self._get_whitelist_reject_message()
            if reject_msg:
                yield event.plain_result(reject_msg)
            return

        if not self._is_super_user(event.get_sender_id()):
            yield event.plain_result("只有管理员才能使用此命令哦~")
            return

        yield event.plain_result("正在刷新本地数据，请稍候...")

        try:
            self.data_manager.reload_data()
            self.songs = self.data_manager.get_all_songs()

            # master 题库已同步时，重新套用（保证刷新后仍是同步数据优先）
            if self.master_data.is_ready(SERVER_JP) or self.master_data.is_ready(SERVER_SC):
                self._on_master_updated()

            # 重新加载效果配置
            self.effect_processor = JacketEffectProcessor(dict(self.config))

            yield event.plain_result(
                f"刷新完成！\n"
                f"本地歌曲: {len(self.songs)}\n"
                f"中文翻译: {len(self.data_manager.cn_map)}\n"
                f"别名数据: {len(self.data_manager.aliases_map)}\n"
                f"启用的效果: {len(self.effect_processor.get_enabled_effects())}个"
            )
        except Exception as e:
            logger.error(f"Failed to reload data: {e}")
            yield event.plain_result(f"刷新失败: {e}")

    async def init(self):
        """插件初始化后的异步钩子"""
        if self._cleanup_task is None:
            self._cleanup_task = self._track_task(asyncio.create_task(self._periodic_cleanup()))
        if self._init_task is None:
            self._init_task = self._track_task(asyncio.create_task(self._initialize_data()))
        if self._master_task is None:
            self._master_task = self._track_task(asyncio.create_task(self._start_master_data()))

    async def terminate(self):
        """插件终止时取消任务并释放题库资源。"""
        logger.info("Closing PJSK Guess Jacket Plugin...")
        self._stopping = True

        tasks = [task for task in self._background_tasks if task is not asyncio.current_task()]
        for task in tasks:
            task.cancel()
        if tasks:
            await asyncio.gather(*tasks, return_exceptions=True)
        self._background_tasks.clear()
        self.session_locks.clear()

        try:
            await self.master_data.terminate()
        except Exception as e:
            logger.warning(f"停止题库同步服务时出错: {e}")
