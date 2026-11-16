# Third-party components

## DPC Latency Checker driver

The DPC graph and kernel unlock features use the signed `dpclat_x64.sys` driver from Thesycon's DPC Latency Checker.

Official product page: <https://www.thesycon.de/eng/latency_check.shtml>

The standalone driver file is **not distributed in this repository**. To build DunSuite Lite, obtain it from the official package, rename a copy to `dpc.sys`, and place it beside `build.ps1`. The build embeds it as a managed resource. The prebuilt `dist/DunSuiteLite.exe` included in this repository already contains the signed driver and can be run directly. The MIT license in this repository applies to the DunSuite Lite source code, not to this third-party driver.

Without `dpc.sys`, compilation stops early with an explanatory error. Do not substitute an unsigned or modified driver.

## ConfuserEx

Release builds use ConfuserEx for lightweight obfuscation. ConfuserEx is a separate build-time dependency and is not included in this repository.

Either place `Confuser.CLI.exe` and its accompanying files under `tools\ConfuserEx\`, or set the `CONFUSEREX_CLI` environment variable to the executable's full path. The `-Test` build skips ConfuserEx entirely.
