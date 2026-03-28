import asyncio
import json
import random
import time
import os
import sqlite3
import urllib.request
import urllib.error
import io
from datetime import datetime
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

from PIL import Image, ImageDraw, ImageFont, ImageFilter

from astrbot.api import logger

try:
    from astrbot.api.event import filter, AstrMessageEvent
    from astrbot.api.star import Context, Star, register, StarTools
    import astrbot.api.message_components as Comp
    from astrbot.core.utils.session_waiter import session_waiter, SessionController
    from astrbot.api import AstrBotConfig
    from astrbot.core.utils.astrbot_path import get_astrbot_data_path
except ImportError:
    logger.error("Failed to import from astrbot.api, attempting fallback.")
    from astrbot.core.plugin import Plugin as Star, Context, register, filter, AstrMessageEvent
    import astrbot.core.message_components as Comp
    from astrbot.core.utils.session_waiter import session_waiter, SessionController

    class StarTools:
        @staticmethod
        def get_data_dir(plugin_name: str) -> Path:
            return Path(__file__).parent.parent.parent.parent / 'data' / 'plugins_data' / plugin_name

    def get_astrbot_data_path() -> Path:
        return Path(__file__).parent.parent.parent.parent / 'data'


try:
    from PIL.Image import Resampling
    LANCZOS = Resampling.LANCZOS
except ImportError:
    LANCZOS = 1


PLUGIN_NAME = "pjsk_guess_jacket"
PLUGIN_AUTHOR = "慵懒午睡"
PLUGIN_DESCRIPTION = "PJSK猜曲绘插件"
PLUGIN_VERSION = "1.0.0"
PLUGIN_REPO_URL = "https://github.com/yonglanws/astrbot_plugin_pjsk_guess_jacket"


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

        if len(answer) >= 4:
            for name in all_names:
                name_lower = name.lower()
                if len(name_lower) >= 4:
                    if answer in name_lower or name_lower in answer:
                        return True, name

        if len(answer) >= 5:
            for name in all_names:
                if self._similar(answer, name.lower(), threshold=0.85):
                    return True, name

        if len(answer) >= 6:
            for name in all_names:
                if self._fuzzy_match(answer, name.lower()):
                    return True, name

        if len(answer) >= 5:
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

        if len(s1) < 4 or len(s2) < 4:
            return False

        s1_chars = set(s1)
        s2_chars = set(s2)
        common_chars = s1_chars & s2_chars

        if len(common_chars) == 0:
            return False

        similarity = len(common_chars) / min(len(s1_chars), len(s2_chars))
        if similarity >= 0.8:
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
        check_len = max(3, int(min_len * 0.5))

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

        if len(s1_normalized) >= 3 and len(s2_normalized) >= 3:
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
    """云端曲绘加载器"""

    BASE_URL = "https://snowyassets.exmeaning.com/startapp/music/jacket/jacket_s_{id}/jacket_s_{id}.png"
    MAX_FILE_SIZE = 10 * 1024 * 1024
    MAX_IMAGE_DIMENSION = 4096
    MAX_PIXELS = 50 * 1024 * 1024

    def __init__(self, cache_dir: Optional[Path] = None):
        self.cache_dir = cache_dir
        if cache_dir:
            cache_dir.mkdir(parents=True, exist_ok=True)

    def _format_jacket_id(self, music_id: int) -> str:
        """
        格式化曲绘ID

        规则：
        - 1-99: 格式化为3位数字，前补零（如 001, 089）
        - 100-732: 直接使用数字本身
        """
        if 1 <= music_id <= 99:
            return f"{music_id:03d}"
        elif 100 <= music_id <= 732:
            return str(music_id)
        else:
            return str(music_id)

    def get_jacket_url(self, music_id: int) -> Optional[str]:
        """获取曲绘的云端URL"""
        if 1 <= music_id <= 732:
            formatted_id = self._format_jacket_id(music_id)
            return self.BASE_URL.format(id=formatted_id)
        return None

    def load_jacket_image(self, music_id: int) -> Optional[Image.Image]:
        """从云端加载曲绘图片"""
        if self.cache_dir:
            cache_file = self.cache_dir / f"{music_id}.png"
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

        url = self.get_jacket_url(music_id)
        if not url:
            return None

        try:
            req = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0'})
            with urllib.request.urlopen(req, timeout=10) as response:
                img_data = response.read()
                if len(img_data) > self.MAX_FILE_SIZE:
                    logger.warning(f"Image file too large for music_id {music_id}: {len(img_data)} bytes")
                    return None

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
                        cache_file = self.cache_dir / f"{music_id}.png"
                        img.save(cache_file)
                    except Exception as e:
                        logger.warning(f"Failed to cache jacket: {e}")

                return img
        except Exception as e:
            logger.warning(f"Failed to load jacket from cloud for music_id {music_id}: {e}")
            return None


class ImageGenerator:
    """图片生成器"""

    def __init__(self, font_path: Optional[Path] = None):
        self.font_path = font_path
        self.title_font: ImageFont.FreeTypeFont
        self.option_font: ImageFont.FreeTypeFont
        self.small_font: ImageFont.FreeTypeFont
        self.card_title_font: ImageFont.FreeTypeFont
        self.card_subtitle_font: ImageFont.FreeTypeFont
        self._load_fonts()

    def _load_fonts(self):
        """加载字体"""
        default_font = ImageFont.load_default()

        if self.font_path and self.font_path.exists():
            try:
                self.title_font = ImageFont.truetype(str(self.font_path), Config.Image.FontSize.TITLE)
                self.option_font = ImageFont.truetype(str(self.font_path), Config.Image.FontSize.OPTION)
                self.small_font = ImageFont.truetype(str(self.font_path), Config.Image.FontSize.SMALL)
                self.card_title_font = ImageFont.truetype(str(self.font_path), Config.Image.FontSize.CARD_TITLE)
                self.card_subtitle_font = ImageFont.truetype(str(self.font_path), Config.Image.FontSize.CARD_SUBTITLE)
                return
            except Exception as e:
                logger.error(f"Failed to load fonts: {e}")

        self.title_font = default_font
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
        """渲染排行榜图片（精美卡片式设计，白色色调）"""
        try:
            width = Config.Ranking.WIDTH
            card_width = Config.Ranking.CARD_WIDTH
            card_height = Config.Ranking.CARD_HEIGHT
            card_gap = Config.Ranking.CARD_GAP
            header_height = Config.Ranking.HEADER_HEIGHT
            footer_height = Config.Ranking.FOOTER_HEIGHT

            height = header_height + len(rows) * (card_height + card_gap) + footer_height

            img = Image.new("RGB", (width, height), Config.Color.BG_WHITE)
            draw = ImageDraw.Draw(img)

            for y in range(height):
                r = int(Config.Color.GRADIENT_START[0] - 8 * y / height)
                g = int(Config.Color.GRADIENT_START[1] - 8 * y / height)
                b = int(Config.Color.GRADIENT_START[2] - 8 * y / height)
                draw.line([(0, y), (width, y)], fill=(r, g, b))

            title_text = "猜曲绘排行榜"
            title_width = self._get_text_width(draw, title_text, self.title_font)
            draw.text(((width - title_width) // 2, Config.Ranking.TITLE_Y), title_text, font=self.title_font, fill=Config.Color.TITLE)

            subtitle = f"共 {len(rows)} 位玩家"
            subtitle_width = self._get_text_width(draw, subtitle, self.small_font)
            draw.text(((width - subtitle_width) // 2, Config.Ranking.SUBTITLE_Y), subtitle, font=self.small_font, fill=Config.Color.SUBTITLE)

            current_y = header_height

            card_x = (width - card_width) // 2
            card_right_edge = card_x + card_width

            FIXED_ATTEMPTS_X = card_right_edge - Config.Ranking.ATTEMPTS_X_OFFSET
            FIXED_ACCURACY_X = card_right_edge - Config.Ranking.ACCURACY_X_OFFSET
            FIXED_SCORE_X = card_right_edge - Config.Ranking.SCORE_X_OFFSET

            medal_colors = [
                Config.Color.MEDAL_GOLD_RANK,
                Config.Color.MEDAL_SILVER,
                Config.Color.MEDAL_BRONZE
            ]

            for i, row in enumerate(rows):
                user_id, user_name, custom_name, score, attempts, correct_attempts = row
                display_name = custom_name if custom_name else user_name
                accuracy = f"{(correct_attempts * 100 / attempts if attempts > 0 else 0):.1f}%"

                self._draw_rounded_rect(draw, card_x, current_y, card_x + card_width, current_y + card_height, 14, Config.Color.CARD_BG, Config.Color.CARD_BORDER)

                rank_circle_x = card_x + Config.Ranking.CIRCLE_X_OFFSET
                rank_circle_y = current_y + card_height // 2
                circle_radius = Config.Ranking.CIRCLE_RADIUS

                if i < 3:
                    draw.ellipse([rank_circle_x - circle_radius, rank_circle_y - circle_radius,
                                  rank_circle_x + circle_radius, rank_circle_y + circle_radius],
                                 fill=medal_colors[i])
                    rank_text = str(i + 1)
                    rank_text_width = self._get_text_width(draw, rank_text, self.option_font)
                    draw.text((rank_circle_x - rank_text_width // 2, rank_circle_y - 15),
                              rank_text, font=self.option_font, fill=Config.Color.TEXT_WHITE)
                else:
                    draw.ellipse([rank_circle_x - circle_radius, rank_circle_y - circle_radius,
                                  rank_circle_x + circle_radius, rank_circle_y + circle_radius],
                                 fill=Config.Color.RANK_BG)
                    rank_text = str(i + 1)
                    rank_text_width = self._get_text_width(draw, rank_text, self.option_font)
                    draw.text((rank_circle_x - rank_text_width // 2, rank_circle_y - 15),
                              rank_text, font=self.option_font, fill=Config.Color.TEXT_RANKING_DARK)

                name_x = card_x + Config.Ranking.NAME_X_OFFSET
                name_y = current_y + Config.Ranking.NAME_Y_OFFSET
                name_display = str(display_name)[:Config.Ranking.NAME_MAX_LENGTH]
                name_width = self._get_text_width(draw, name_display, self.option_font)
                if name_width > Config.Ranking.NAME_MAX_WIDTH:
                    name_display = self._truncate_text(draw, name_display, self.option_font, Config.Ranking.NAME_MAX_WIDTH - 10) + "..."
                draw.text((name_x, name_y), name_display, font=self.option_font, fill=Config.Color.TEXT_RANKING_DARK)

                draw.text((name_x, name_y + 32), f"ID: {user_id}", font=self.small_font, fill=Config.Color.TEXT_RANKING_GRAY)

                attempts_str = str(attempts)
                attempts_label = "次"
                attempts_str_width = self._get_text_width(draw, attempts_str, self.card_title_font)
                attempts_label_width = self._get_text_width(draw, attempts_label, self.small_font)
                attempts_y = current_y + Config.Ranking.DATA_Y_OFFSET
                draw.text((FIXED_ATTEMPTS_X - attempts_str_width, attempts_y), attempts_str, font=self.card_title_font, fill=Config.Color.ATTEMPTS)
                draw.text((FIXED_ATTEMPTS_X + 5, attempts_y + 6), attempts_label, font=self.small_font, fill=Config.Color.TEXT_RANKING_GRAY)

                acc_label = "正确率"
                acc_str_width = self._get_text_width(draw, accuracy, self.card_title_font)
                acc_label_width = self._get_text_width(draw, acc_label, self.small_font)
                acc_y = current_y + Config.Ranking.DATA_Y_OFFSET
                draw.text((FIXED_ACCURACY_X - acc_str_width, acc_y), accuracy, font=self.card_title_font, fill=Config.Color.ACCURACY)
                draw.text((FIXED_ACCURACY_X - acc_label_width // 2 - 40, acc_y + 30), acc_label, font=self.small_font, fill=Config.Color.TEXT_RANKING_GRAY)

                score_str = str(score)
                score_label = "分"
                score_str_width = self._get_text_width(draw, score_str, self.card_title_font)
                score_label_width = self._get_text_width(draw, score_label, self.small_font)
                score_y = current_y + Config.Ranking.DATA_Y_OFFSET
                draw.text((FIXED_SCORE_X - score_str_width, score_y), score_str, font=self.card_title_font, fill=Config.Color.SCORE)
                draw.text((FIXED_SCORE_X + 5, score_y + 6), score_label, font=self.small_font, fill=Config.Color.TEXT_RANKING_GRAY)

                current_y += card_height + card_gap

            # 绘制页脚
            footer_text = f"Generated on {datetime.now().strftime('%Y-%m-%d %H:%M')}"
            footer_width = self._get_text_width(draw, footer_text, self.small_font)
            draw.text(((width - footer_width) // 2, height - 30), footer_text, font=self.small_font, fill=(180, 180, 190))

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

    def __init__(self, db_path: str):
        self.db_path = db_path
        self._init_db()

    def _init_db(self):
        with sqlite3.connect(self.db_path, timeout=30.0) as conn:
            cursor = conn.cursor()
            cursor.execute("""
                CREATE TABLE IF NOT EXISTS jacket_user_stats (
                    user_id TEXT PRIMARY KEY,
                    user_name TEXT,
                    custom_name TEXT,
                    score INTEGER DEFAULT 0,
                    attempts INTEGER DEFAULT 0,
                    correct_attempts INTEGER DEFAULT 0,
                    last_play_date TEXT,
                    daily_plays INTEGER DEFAULT 0
                )
            """)
            conn.commit()

    def get_user_stats(self, user_id: str) -> Optional[tuple]:
        with sqlite3.connect(self.db_path, timeout=30.0) as conn:
            cursor = conn.cursor()
            cursor.execute(
                "SELECT score, attempts, correct_attempts, last_play_date, daily_plays FROM jacket_user_stats WHERE user_id = ?",
                (user_id,)
            )
            return cursor.fetchone()

    def get_user_rank(self, score: int) -> int:
        with sqlite3.connect(self.db_path, timeout=30.0) as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT COUNT(*) FROM jacket_user_stats WHERE score > ?", (score,))
            return cursor.fetchone()[0] + 1

    def update_user_play(self, user_id: str, user_name: str):
        today = time.strftime("%Y-%m-%d")
        with sqlite3.connect(self.db_path, timeout=30.0) as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT last_play_date, daily_plays FROM jacket_user_stats WHERE user_id = ?", (user_id,))
            user_data = cursor.fetchone()

            if user_data:
                last_play_date, daily_plays = user_data
                new_daily_plays = daily_plays + 1 if last_play_date == today else 1
                cursor.execute(
                    "UPDATE jacket_user_stats SET user_name = ?, last_play_date = ?, daily_plays = ? WHERE user_id = ?",
                    (user_name, today, new_daily_plays, user_id)
                )
            else:
                cursor.execute(
                    "INSERT INTO jacket_user_stats (user_id, user_name, last_play_date, daily_plays) VALUES (?, ?, ?, ?)",
                    (user_id, user_name, today, 1)
                )
            conn.commit()

    def update_user_score(self, user_id: str, user_name: str, score: int, correct: bool):
        today = time.strftime("%Y-%m-%d")
        with sqlite3.connect(self.db_path, timeout=30.0) as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT score, attempts, correct_attempts, last_play_date, daily_plays FROM jacket_user_stats WHERE user_id = ?", (user_id,))
            user_data = cursor.fetchone()

            if user_data:
                new_score = user_data[0] + score
                new_attempts = user_data[1] + 1
                new_correct = user_data[2] + (1 if correct else 0)
                last_play_date = user_data[3]
                daily_plays = user_data[4]
                new_daily_plays = daily_plays + 1 if last_play_date == today else 1
                cursor.execute(
                    "UPDATE jacket_user_stats SET score = ?, attempts = ?, correct_attempts = ?, user_name = ?, last_play_date = ?, daily_plays = ? WHERE user_id = ?",
                    (new_score, new_attempts, new_correct, user_name, today, new_daily_plays, user_id)
                )
            else:
                cursor.execute(
                    "INSERT INTO jacket_user_stats (user_id, user_name, score, attempts, correct_attempts, last_play_date, daily_plays) VALUES (?, ?, ?, ?, ?, ?, ?)",
                    (user_id, user_name, score, 1, 1 if correct else 0, today, 1)
                )
            conn.commit()

    def can_play_today(self, user_id: str, daily_limit: int) -> bool:
        if daily_limit == -1:
            return True
        today = time.strftime("%Y-%m-%d")
        with sqlite3.connect(self.db_path, timeout=30.0) as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT daily_plays, last_play_date FROM jacket_user_stats WHERE user_id = ?", (user_id,))
            user_data = cursor.fetchone()
            if user_data and user_data[1] == today:
                return user_data[0] < daily_limit
            return True

    def set_custom_name(self, user_id: str, user_name: str, custom_name: Optional[str]) -> bool:
        today = time.strftime("%Y-%m-%d")
        with sqlite3.connect(self.db_path, timeout=30.0) as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT user_id FROM jacket_user_stats WHERE user_id = ?", (user_id,))
            exists = cursor.fetchone() is not None

            if custom_name:
                if exists:
                    cursor.execute("UPDATE jacket_user_stats SET custom_name = ? WHERE user_id = ?", (custom_name, user_id))
                else:
                    cursor.execute(
                        "INSERT INTO jacket_user_stats (user_id, user_name, custom_name, score, attempts, correct_attempts, last_play_date, daily_plays) VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                        (user_id, user_name, custom_name, 0, 0, 0, today, 0)
                    )
            elif exists:
                cursor.execute("UPDATE jacket_user_stats SET custom_name = NULL WHERE user_id = ?", (user_id,))
            else:
                return False

            conn.commit()
            return True

    def get_ranking(self, limit: int) -> list[tuple]:
        with sqlite3.connect(self.db_path, timeout=30.0) as conn:
            cursor = conn.cursor()
            cursor.execute(
                "SELECT user_id, user_name, custom_name, score, attempts, correct_attempts FROM jacket_user_stats ORDER BY score DESC LIMIT ?",
                (limit,)
            )
            return cursor.fetchall()


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
        "glitch": {
            "name": "损坏效果",
            "description": "模拟图片撕裂、噪点或数据损坏的视觉表现",
            "difficulty": 2,
            "glitch_intensity": 1.0,
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
                if "glitch_intensity" in effect_config:
                    val = effect_config["glitch_intensity"]
                    if isinstance(val, (int, float)) and 0.1 <= val <= 5.0:
                        self.EFFECTS[effect_name]["glitch_intensity"] = float(val)
                        logger.debug(f"设置 {effect_name} 损坏强度: {val}")
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

    def apply_glitch(self, img: Image.Image, intensity: float = 1.0) -> Image.Image:
        """应用损坏效果，参考猜曲卡插件的实现"""
        try:
            w, h = img.size
            pixels = img.load()
            result = img.copy()
            result_pixels = result.load()
            
            # 增加损坏强度
            num_glitches = int(h * intensity)
            
            # 1. 增加撕裂效果
            for _ in range(num_glitches):
                rand_val = random.random()
                if rand_val < 0.3:
                    # 更大范围的水平撕裂
                    y = random.randint(0, h - 1)
                    shift = random.randint(-30, 30)
                    if 0 <= y + shift < h:
                        # 撕裂整行
                        for x in range(w):
                            result_pixels[x, y] = pixels[x, (y + shift) % h]
                elif rand_val < 0.4:
                    # 水平扫描线撕裂
                    y = random.randint(0, h - 1)
                    # 撕裂多行
                    height = random.randint(1, 10)
                    shift = random.randint(-25, 25)
                    for dy in range(height):
                        if 0 <= y + dy < h:
                            for x in range(w):
                                result_pixels[x, y + dy] = pixels[x, (y + dy + shift) % h]
                elif rand_val < 0.5:
                    # 增强垂直撕裂
                    x = random.randint(0, w - 1)
                    # 增加垂直撕裂的范围
                    shift = random.randint(-35, 35)
                    if 0 <= x + shift < w:
                        # 撕裂整列
                        for y_col in range(h):
                            result_pixels[x, y_col] = pixels[(x + shift) % w, y_col]
                elif rand_val < 0.85:
                    # 垂直扫描线撕裂
                    x = random.randint(0, w - 1)
                    # 撕裂多列
                    width = random.randint(1, 10)
                    shift = random.randint(-30, 30)
                    for dx in range(width):
                        if 0 <= x + dx < w:
                            for y_col in range(h):
                                result_pixels[x + dx, y_col] = pixels[(x + dx + shift) % w, y_col]
                else:
                    # 2. 增加大量噪点
                    # 随机块噪点，确保小尺寸图片也能正常处理
                    max_y_offset = max(0, h - 30)
                    max_x_offset = max(0, w - 30)
                    y = random.randint(0, max_y_offset)
                    x = random.randint(0, max_x_offset)
                    max_block_size = min(30, h - y, w - x)
                    if max_block_size >= 10:
                        block_size = random.randint(10, max_block_size)
                        for dy in range(block_size):
                            for dx in range(block_size):
                                if img.mode == 'RGB':
                                    result_pixels[x + dx, y + dy] = (random.randint(0, 255), random.randint(0, 255), random.randint(0, 255))
                                elif img.mode == 'RGBA':
                                    result_pixels[x + dx, y + dy] = (random.randint(0, 255), random.randint(0, 255), random.randint(0, 255), random.randint(0, 255))
                                else:
                                    result_pixels[x + dx, y + dy] = random.randint(0, 255)
            
            # 3. 增加额外的噪点层
            # 随机像素噪点
            num_noise_pixels = int(w * h * intensity * 0.1)
            for _ in range(num_noise_pixels):
                x = random.randint(0, w - 1)
                y = random.randint(0, h - 1)
                if img.mode == 'RGB':
                    result_pixels[x, y] = (random.randint(0, 255), random.randint(0, 255), random.randint(0, 255))
                elif img.mode == 'RGBA':
                    result_pixels[x, y] = (random.randint(0, 255), random.randint(0, 255), random.randint(0, 255), random.randint(0, 255))
                else:
                    result_pixels[x, y] = random.randint(0, 255)
            
            # 4. 减弱色彩偏移效果，降低饱和度
            for _ in range(int(h * intensity * 0.3)):  # 减少色彩偏移的数量
                y = random.randint(0, h - 1)
                offset = random.randint(-3, 3)
                for x in range(w):
                    if 0 <= x + offset < w:
                        if img.mode == 'RGB':
                            r, g, b = pixels[x, y]
                            # 减弱色彩偏移，降低饱和度
                            result_pixels[x, y] = ((r + random.randint(-15, 15)) % 256, 
                                                (g + random.randint(-15, 15)) % 256, 
                                                (b + random.randint(-15, 15)) % 256)
                        elif img.mode == 'RGBA':
                            r, g, b, a = pixels[x, y]
                            result_pixels[x, y] = ((r + random.randint(-15, 15)) % 256, 
                                                (g + random.randint(-15, 15)) % 256, 
                                                (b + random.randint(-15, 15)) % 256, a)
            
            # 5. 整体降低饱和度
            if img.mode == 'RGB' or img.mode == 'RGBA':
                # 转换为灰度图
                grayscale = result.convert('L')
                # 转换回彩色模式，保持灰度效果
                if img.mode == 'RGB':
                    result = Image.merge('RGB', (grayscale, grayscale, grayscale))
                elif img.mode == 'RGBA':
                    alpha = result.split()[-1]
                    result = Image.merge('RGBA', (grayscale, grayscale, grayscale, alpha))
            
            return result
        except Exception as e:
            logger.error(f"损坏效果处理失败: {e}", exc_info=True)
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
        elif effect_name == "glitch":
            intensity = kwargs.get("glitch_intensity", effect_config.get("glitch_intensity", 1.0))
            return self.apply_glitch(img, intensity), difficulty
        elif effect_name == "shuffle_blocks_easy":
            block_size = kwargs.get("block_size", effect_config.get("block_size", 65))
            return self.apply_shuffle_blocks(img, block_size), difficulty
        elif effect_name == "shuffle_blocks_hard":
            block_size = kwargs.get("block_size", effect_config.get("block_size", 20))
            return self.apply_shuffle_blocks(img, block_size), difficulty

        return img, difficulty

    def random_effect(self) -> tuple[str, str, int]:
        """随机选择一个启用的效果"""
        enabled_effects = self.get_enabled_effects()
        if not enabled_effects:
            logger.warning("没有启用的效果，使用默认模糊")
            return "blur", self.EFFECTS["blur"]["name"], self.EFFECTS["blur"]["difficulty"]

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

        self.cloud_jacket_loader = CloudJacketLoader(self.jacket_cache_dir)

        font_path = self.resources_dir / "font.ttf"
        self.image_generator = ImageGenerator(font_path if font_path.exists() else None)

        self.active_sessions: set = set()
        self.game_sessions: dict[str, JacketGameSession] = {}
        self.session_locks: dict[str, asyncio.Lock] = {}
        self.last_game_end_time: dict[str, float] = {}
        self.songs: list[SongInfo] = []
        self.data_initialized = False

        logger.info(f"初始化效果处理器，效果数量: {len(self.config.get('effects', {}))}")
        self.effect_processor = JacketEffectProcessor(dict(self.config))

        self._cleanup_output_dir()
        self._cleanup_task = asyncio.create_task(self._periodic_cleanup())
        self._init_task = asyncio.create_task(self._initialize_data())

        logger.info(f"PJSK Guess Jacket Plugin initialized (v{PLUGIN_VERSION})")

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

    def _is_user_blacklisted(self, user_id: str) -> bool:
        """检查用户是否在黑名单中"""
        return str(user_id) in {str(x) for x in self.config.get("blacklist", [])}

    def _is_super_user(self, user_id: str) -> bool:
        """检查是否为超级用户"""
        super_users = {str(x) for x in self.config.get("super_users", [])}
        return bool(super_users) and str(user_id) in super_users

    def get_random_song(self) -> Optional[SongInfo]:
        """获取随机歌曲"""
        return random.choice(self.songs) if self.songs else None

    @filter.command("猜曲绘", alias={"pjsk猜曲绘", "曲绘猜曲", "猜封面"})
    async def start_guess_jacket(self, event: AstrMessageEvent):
        """开始猜曲绘游戏"""
        if not self.data_initialized:
            yield event.plain_result("数据正在初始化中，请稍后再试...")
            return

        if not self._is_group_allowed(event):
            return

        user_id = event.get_sender_id()
        if self._is_user_blacklisted(user_id):
            yield event.plain_result("抱歉，你已被禁止使用此功能 😔")
            return

        session_id = event.unified_msg_origin

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
            can_play = await asyncio.to_thread(self.db.can_play_today, user_id, daily_limit)
            if not can_play:
                yield event.plain_result(f"今天的游戏次数已经用完啦~ 明天再来玩吧！每天最多可以玩{daily_limit}次哦~ ✨")
                return

            self.active_sessions.add(session_id)

        try:
            if not self.songs:
                yield event.plain_result("歌曲数据未加载，请稍后再试。")
                return

            correct_song = self.get_random_song()
            if not correct_song:
                yield event.plain_result("没有可用的歌曲数据。")
                return

            jacket_img = await asyncio.to_thread(
                self.cloud_jacket_loader.load_jacket_image, correct_song.music_id
            )
            if not jacket_img:
                yield event.plain_result("该歌曲没有封面图片，请重试。")
                return

            effect_name, effect_display, difficulty = self.effect_processor.random_effect()

            try:
                processed_img, actual_difficulty = await asyncio.to_thread(
                    self.effect_processor.apply_effect, jacket_img, effect_name
                )

                processed_path = self.output_dir / f"jacket_{time.time_ns()}.png"
                await asyncio.to_thread(processed_img.save, processed_path)

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

            await asyncio.to_thread(self.db.update_user_play, user_id, event.get_sender_name())

            game_session = JacketGameSession(game_data=game_data)
            self.game_sessions[session_id] = game_session

            timeout_seconds = self.config.get("answer_timeout", Config.DEFAULT_TIMEOUT)
            intro_text = (
                f"🎨 猜曲绘游戏 🎨\n"
                f"请在{timeout_seconds}秒内输入歌曲名称回答~\n"
                f"效果: {effect_display}\n"
                f"难度: {'⭐' * actual_difficulty}\n"
                f"得分: {actual_difficulty}分\n"
                f"提示: 支持中文名、原名、别名回答，支持模糊匹配"
            )

            yield event.chain_result([
                Comp.Plain(intro_text),
                Comp.Image(file=str(processed_path))
            ])

            answered_correctly = False
            winner_name = None
            winner_id = None  # 记录答对者的ID

            @session_waiter(timeout=timeout_seconds)
            async def jacket_waiter(controller: SessionController, answer_event: AstrMessageEvent):
                nonlocal answered_correctly, winner_name, winner_id

                answer_text = answer_event.message_str.strip()
                if not answer_text:
                    return

                is_correct, matched_name = self.data_manager.check_answer(
                    game_session.game_data.correct_song.music_id,
                    answer_text
                )

                if is_correct:
                    answerer_id = answer_event.get_sender_id()
                    if self._is_user_blacklisted(answerer_id):
                        return
                    daily_limit = self.config.get("daily_play_limit", Config.DEFAULT_DAILY_LIMIT)
                    can_play = await asyncio.to_thread(self.db.can_play_today, answerer_id, daily_limit)
                    if not can_play:
                        return
                    answered_correctly = True
                    winner_name = answer_event.get_sender_name()
                    winner_id = answerer_id
                    controller.stop()

            try:
                await jacket_waiter(event)
            except TimeoutError:
                game_session.game_ended_by_timeout = True

            correct_song = game_session.game_data.correct_song
            correct_name = correct_song.display_name
            original_name = correct_song.original_name
            aliases = self.data_manager.get_aliases(correct_song.music_id)

            aliases_text = ""
            if aliases:
                aliases_text = "\n别名: " + " | ".join(aliases[:10])
                if len(aliases) > 10:
                    aliases_text += f" ...等{len(aliases)}个别名"

            if game_session.game_ended_by_timeout:
                result_text = f"⏰ 时间到！\n正确答案: {correct_name}\n原名: {original_name}{aliases_text}"
                await asyncio.to_thread(self.db.update_user_score, user_id, event.get_sender_name(), 0, False)
            elif answered_correctly:
                result_text = f"🎉 {winner_name}答对了！获得{game_session.game_data.score}分！\n正确答案: {correct_name}\n原名: {original_name}{aliases_text}"
                await asyncio.to_thread(self.db.update_user_score, winner_id, winner_name, game_session.game_data.score, True)
            else:
                result_text = f"❌ 无人答对！\n正确答案: {correct_name}\n原名: {original_name}{aliases_text}"
                await asyncio.to_thread(self.db.update_user_score, user_id, event.get_sender_name(), 0, False)

            yield event.plain_result(result_text)

            original_jacket_img = await asyncio.to_thread(
                self.cloud_jacket_loader.load_jacket_image, correct_song.music_id
            )
            if original_jacket_img:
                original_path = self.output_dir / f"original_{time.time_ns()}.png"
                original_jacket_img.save(original_path)
                yield event.image_result(str(original_path))

        finally:
            self.active_sessions.discard(session_id)
            self.game_sessions.pop(session_id, None)
            self.last_game_end_time[session_id] = time.time()

    @filter.command("猜曲绘分数", alias={"pjsk猜曲绘分数", "曲绘猜曲分数"})
    async def show_jacket_score(self, event: AstrMessageEvent):
        """显示猜曲绘分数"""
        if not self._is_group_allowed(event):
            return

        user_id = event.get_sender_id()
        user_name = event.get_sender_name()

        user_data = await asyncio.to_thread(self.db.get_user_stats, user_id)
        if not user_data:
            yield event.plain_result(f"{user_name}，你还没有参与过猜曲绘游戏哦！快来一起玩呀~ 🎮")
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
            f"🏆 总分: {score} 分\n"
            f"🎯 正确率: {accuracy:.1f}%\n"
            f"🎮 游戏次数: {attempts} 次\n"
            f"✅ 答对次数: {correct_attempts} 次\n"
            f"🏅 当前排名: 第 {rank} 名\n"
            f"📅 今日剩余: {remaining_plays}\n"
        )

        yield event.plain_result(stats_text)

    @filter.command("猜曲绘排行榜", alias={"pjsk猜曲绘排行榜", "曲绘猜曲排行"})
    async def show_jacket_ranking(self, event: AstrMessageEvent):
        """显示猜曲绘排行榜"""
        if not self._is_group_allowed(event):
            return

        self._cleanup_output_dir()

        ranking_count = self.config.get("ranking_display_count", 10)
        ranking_count = max(1, min(int(ranking_count), 50))
        rows = await asyncio.to_thread(self.db.get_ranking, ranking_count)

        if not rows:
            yield event.plain_result("还没有人参与过猜曲绘游戏呢~ 快来成为第一个玩家吧！✨")
            return

        try:
            img_path = await asyncio.to_thread(
                self.image_generator.create_ranking_image, rows, self.output_dir
            )
            if img_path:
                yield event.image_result(str(img_path))
            else:
                yield event.plain_result("生成排行榜图片时出错。")
        except Exception as e:
            logger.error(f"Failed to render jacket ranking: {e}")
            yield event.plain_result("生成排行榜图片时出错。")

    @filter.command("猜曲绘自定义名称", alias={"猜曲绘昵称", "曲绘自定义名称"})
    async def set_jacket_custom_name(self, event: AstrMessageEvent):
        """设置猜曲绘自定义名称"""
        if not self._is_group_allowed(event):
            return

        sender_id = event.get_sender_id()
        parts = event.message_str.strip().split(maxsplit=1)
        custom_name = parts[1].strip() if len(parts) > 1 else None

        if custom_name:
            if len(custom_name) > 20:
                yield event.plain_result("自定义名称过长，请限制在20个字符以内哦~")
                return
            if any(c in custom_name for c in ['\n', '\r', '\t', '\0']):
                yield event.plain_result("自定义名称包含非法字符，请重新输入~")
                return
            await asyncio.to_thread(self.db.set_custom_name, sender_id, event.get_sender_name(), custom_name)
            yield event.plain_result(f"好的！你的猜曲绘自定义名称已设置为：{custom_name} ✨")
        else:
            result = await asyncio.to_thread(self.db.set_custom_name, sender_id, event.get_sender_name(), None)
            if result:
                yield event.plain_result("好的！你的猜曲绘自定义名称已清除 ✨")
            else:
                yield event.plain_result("你还没有参与过猜曲绘游戏哦~ 🎮")

    @filter.command("猜曲绘帮助", alias={"pjsk猜曲绘帮助"})
    async def show_help(self, event: AstrMessageEvent):
        """显示帮助信息"""
        if not self._is_group_allowed(event):
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
            return

        if not self._is_super_user(event.get_sender_id()):
            yield event.plain_result("只有管理员才能使用此命令哦~")
            return

        yield event.plain_result("正在刷新本地数据，请稍候...")

        try:
            self.data_manager.reload_data()
            self.songs = self.data_manager.get_all_songs()

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

    async def terminate(self):
        """插件终止时的清理"""
        logger.info("Closing PJSK Guess Jacket Plugin...")
        
        # 取消后台任务
        if hasattr(self, '_cleanup_task') and self._cleanup_task:
            self._cleanup_task.cancel()
            try:
                await self._cleanup_task
            except asyncio.CancelledError:
                pass
        
        if hasattr(self, '_init_task') and self._init_task:
            self._init_task.cancel()
            try:
                await self._init_task
            except asyncio.CancelledError:
                pass
