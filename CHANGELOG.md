# 更新日志

### v1.1.0
- **双服资源路由**：曲绘资源随当前题库服务器自动切换：日服使用 `https://storage.exmeaning.com/sekai-jp-assets`，国服使用 `https://storage.exmeaning.com/sekai-sc-assets`；缓存按服务器隔离；新增 `jp_resource_url_base` / `sc_resource_url_base` 配置项

- **题库 master 数据自动同步**：曲库改从 Haruki master 数据（`musics.json`）+ 中文翻译 + 社区别名自动拉取，每 24 小时检查一次，新歌随游戏版本更新自动入库；GitHub API 不可用时回退 jsDelivr，dataVersion 未变化时跳过大文件下载
- **新增日服/国服题库切换**：`猜曲绘切换日服题库` / `猜曲绘切换国服题库`，按群独立记忆，结算显示当前题库服务器
- **新增 QQ 官方机器人 markdown 机制**：官方平台改为 @机器人 应答制（开局附「点击回答 / 仅退出本局 / 退出自动模式」连接）；结算以 markdown 渲染，附切换题库、绑定QQ、个人分数、排行榜连接与快捷入口
- **结算精简**：正确答案只显示中文名，删除"原名"和"别名"行
- **统一退出机制**：`仅退出本局` 只结束当前对局（自动模式继续），`退出自动模式` 停止自动续局（本局继续打完），任何时候可触发；旧的 `退出` 指令废除
- **自动模式优化**：自动模式期间不出现任何 markdown 按钮，结算只显示结果、歌名与下一局提示，退出自动模式后恢复
- 曲绘封面 URL 解除歌曲 id ≤ 732 的旧上限（新歌 id 已到 800+）
- 新增 `default_server`、`update_interval_hours`、`connect_link_template` 配置项

### v1.0.0

- 实现基本功能
