# astrbot_plugin_pjsk_guess_jacket

《初音未来 缤纷舞台》（Project SEKAI）**猜曲绘**娱乐插件。插件展示经过特殊效果处理的歌曲封面图片，玩家根据封面猜出歌曲名称。

## 特性

- 🎨 **多样图片效果**：模糊、随机裁切、分块打乱（简易/困难）等，难度越高得分越多（支持 WebUI 自定义启用、分数与参数）
- 🔄 **题库自动同步**：歌曲题库自 Haruki master（`musics.json`）+ 中文翻译 + 社区别名每 24 小时自动同步，新歌随游戏版本更新自动入库，版本未变跳过大文件下载
- 🌐 **多服务器题库**：支持日服 / 国服题库自由切换，按群独立记忆
- 🏆 **精美数据面板**：内置积分排行榜（Pillow 本地渲染横向表格，与猜卡面同款视觉规范，支持自定义名称、未绑定 QQ 徽章）、个人战绩查询、每日次数限制与冷却
- 🤖 **QQ 官方机器人支持**：@机器人 应答制，开局附「点击回答 / 仅退出本局 / 退出自动模式」连接，结算附切换题库/绑定/查分/排行榜连接；快捷入口由 `quick_entries` 配置控制（默认关闭）；支持绑定普通 QQ 迁移分数
- ⚡ **双模式退出**：`仅退出本局` 与 `退出自动模式` 严格分离，自动模式精简无扰
- 🔍 **智能容错匹配**：支持中文名、别名回答，内置拼写容错与模糊匹配算法；结算精简只显示中文名

## 指令

### 猜曲绘游戏

| 指令 | 别名 | 说明 |
| --- | --- | --- |
| `猜曲绘` | `pjsk猜曲绘`、`曲绘猜曲`、`猜封面` | 开始一轮猜曲绘游戏 |
| `自动猜曲绘` | `自动猜封面` | 自动模式：每局结束后自动开始下一局 |

### 题库与账号

| 指令 | 说明 |
| --- | --- |
| `猜曲绘切换日服题库` / `猜曲绘切换国服题库` | 切换本群题库服务器（下一局生效） |
| `猜曲绘绑定 QQ号` | 将 QQ 官方机器人账号绑定到普通 QQ 号，分数自动迁移（需发送"确认"，每个QQ号最多绑定2个官机） |
| `猜曲绘解绑` | 解除当前官机账号与 QQ 号的绑定，释放绑定名额（需发送"确认"） |

### 数据与帮助

| 指令 | 别名 | 说明 |
| --- | --- | --- |
| `猜曲绘排行榜` | `猜曲绘排行`、`pjsk猜曲绘排行榜`、`本地猜曲绘排行榜` | 查看总分排行榜 |
| `猜曲绘分数` | `pjsk猜曲绘分数`、`曲绘猜曲分数`、`猜曲绘个人分数` | 查看自己的游戏数据统计 |
| `猜曲绘自定义名称 [名称]` | `猜曲绘昵称`、`曲绘自定义名称` | 设置自定义 ID（不带参数可清除） |
| `猜曲绘帮助` | `pjsk猜曲绘帮助` | 显示帮助信息 |

### 管理员指令

| 指令 | 说明 |
| --- | --- |
| `刷新本地数据` | 重新加载本地别名与翻译数据 |

### 退出机制说明

- **`仅退出本局`**：仅在游玩中生效，立即结束当前对局并公布答案（自动模式继续开下一局）。
- **`退出自动模式`**（别名：`退出`）：任何时候可触发，停止自动续局（当前对局继续打完）。
- **自动模式精简**：自动模式期间全程不出现 markdown 连接按钮，结算只显示结果、歌名与下一局提示，退出自动模式后恢复完整结算面板。
- **QQ 官方机器人平台**：开局消息为 markdown 格式，附「点击回答 / 仅退出本局 / 退出自动模式」连接；回答需 @机器人 + 歌名。普通 QQ 环境行为不变（直接发送歌名即可），无任何 markdown 按钮。

## 配置说明

通过 AstrBot WebUI 界面进行配置：

| 配置项 | 类型 | 默认值 | 说明 |
| --- | --- | --- | --- |
| `default_server` | string | `jp` | 默认题库服务器（`jp`=日服 / `sc`=国服） |
| `update_interval_hours` | int | `24` | master 题库自动更新间隔（小时） |
| `connect_link_template` | string | （官方标签） | QQ 官方机器人结算连接的 markdown 模板 |
| `quick_entries` | list | `[]` | 结算快捷入口列表（若为空则不显示快捷入口） |
| `jp_resource_url_base` | string | `https://storage.exmeaning.com/sekai-jp-assets` | 日服曲绘资源根地址 |
| `sc_resource_url_base` | string | `https://storage.exmeaning.com/sekai-sc-assets` | 国服曲绘资源根地址 |
| `answer_timeout` | int | `30` | 答题超时时间（秒） |
| `daily_play_limit` | int | `10` | 每日游戏次数上限（-1 为无限制） |
| `game_cooldown_seconds` | int | `30` | 游戏冷却时间（秒） |
| `ranking_display_count` | int | `10` | 排行榜显示人数（建议 5-20） |
| `reward_valid_time` | int | `0` | 首位答对后的奖励有效时间（秒，0 为禁用） |
| `group_whitelist` | list | `[]` | 群聊白名单（为空则所有群可用） |
| `whitelist_reject_message`| string | （提示语） | 非白名单群聊提示语（留空不提示） |
| `super_users` | list | `[]` | 管理员用户 ID 列表 |
| `blacklist` | list | `[]` | 黑名单用户 ID 列表 |
| `effects` | object | `{...}` | 各图片效果的启用、分数与详细参数配置 |

## 资源

- 日服master：[Team-Haruki/haruki-sekai-master](https://github.com/Team-Haruki/haruki-sekai-master)
- 国服master：[Team-Haruki/haruki-sekai-sc-master](https://github.com/Team-Haruki/haruki-sekai-sc-master)
- 中文译名：`translation.exmeaning.com`（Moesekai 翻译源）
- 歌曲别名：`moe.exmeaning.com/data/music_alias`（Moesekai 别名源）+ `neo-api.haruki.seiunx.com`（Haruki 别名源，自动合并）
- 日服曲绘资源：`https://storage.exmeaning.com/sekai-jp-assets/music/jacket`
- 国服曲绘资源：`https://storage.exmeaning.com/sekai-sc-assets/music/jacket`

优先走 GitHub Contents API，失败时回退 jsDelivr CDN。数据持久化于 `data/plugin_data/pjsk_guess_jacket/`。

## 依赖

`Pillow`、`pilmoji`、`aiohttp`。图片全部使用 Pillow 本地渲染。

## 致谢

部分代码及灵感参考自 [astrbot_plugin_pjsk_guess_song](https://github.com/nichinichisou0609/astrbot_plugin_pjsk_guess_song)。在此致谢。

完整更新历史见 [CHANGELOG.md](CHANGELOG.md)。
