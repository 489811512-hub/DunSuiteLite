# DunSuite Lite

中性黑白灰界面的 Windows 轻量性能工具，无需登录或联网。只读写 Lite 自身配置，不导入或清理其他软件的数据。

## DunOS 系统探索版

DunSuite Lite 是 **DunOS 系统探索版**的轻量性能工具与开源实践项目，延续其系统调校和低延迟探索方向，以独立、精简的形式开放源码。

了解 DunOS 系统探索版：<https://dunos.vip/home>

## 功能

- 计时器：自动调优、手动设定、自身精度异常维护、DPC 延迟图与内核解锁。
- 待机内存：手动、智能、定时清理及全局热键。
- 进程调优：时间片、硬/软核心隔离、设备中断落点、首核调度、Win32 分离值。
- 调度预设导入导出、开机自启、托盘常驻。

进程列表只有「时间片 / 核心规则 / 首核」三列。

## 直接运行

仓库附带已构建的 [DunSuiteLite.exe](dist/DunSuiteLite.exe)，下载后可直接运行。

## 运行环境

- Windows 10/11 x64
- 管理员权限（进程调度、DPC 驱动与内存清理由此授权）
- 不建议与其他计时器调优软件同时运行

## 构建

先按 [THIRD_PARTY.md](THIRD_PARTY.md) 准备 `dpc.sys`。该第三方驱动不以独立文件形式随源码分发；仓库中的成品 EXE 已内嵌，可直接运行。

未混淆构建：

```powershell
powershell -File build.ps1 -Test
```

简单混淆发布构建：

```powershell
# 将 Confuser.CLI.exe 放到 tools\ConfuserEx\，或先设置 CONFUSEREX_CLI
powershell -File build.ps1
```

成品输出到 `dist\DunSuiteLite.exe`。混淆仅使用 `anti ildasm + constants + rename`，不含 anti-tamper、控制流或反调试。

## 数据与诊断

- 配置：`%ProgramData%\DunSuiteLite\config.ini`
- 自启项：`DunSuiteLite`
- 单实例：`Global\DunSuiteLite_Single`
- ETW：`DunSuiteLite-Process`
- DPC 服务：`DunSuiteLiteDpc`
- 日志：`%TEMP%\dunsuitelite_*.txt/log`

`-show` 显窗；`--tray` 后台；`-tab 1..3` 指定页面；`-selftest` 计时器自动调优自检；`-isotopo` 拓扑；`-isowatch` 进程事件；`-irqenum` 设备枚举。

带写操作的诊断：`-purge`、`-purgelow`、`-tsapply`、`-isotest`、`-isoengage`、`-irqset`、`-fcapply`。

## 许可证

源码采用 [MIT License](LICENSE)。第三方组件及其授权边界见 [THIRD_PARTY.md](THIRD_PARTY.md)。
