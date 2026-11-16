param([switch]$Test)
$ErrorActionPreference = 'Stop'
Set-Location $PSScriptRoot
$fw = 'C:\Windows\Microsoft.NET\Framework64\v4.0.30319'
$env:TEMP = "$PSScriptRoot\_buildtemp"
$env:TMP = $env:TEMP
New-Item -ItemType Directory -Force $env:TEMP | Out-Null
New-Item -ItemType Directory -Force "$PSScriptRoot\dist" | Out-Null

if (-not (Test-Path "$PSScriptRoot\dpc.sys")) {
    throw 'dpc.sys is missing. Obtain the driver as described in THIRD_PARTY.md, then place it beside build.ps1.'
}

$out = if ($Test) { 'DunSuiteLite_test.exe' } else { 'DunSuiteLite.exe' }
& "$fw\csc.exe" -nologo -target:winexe -platform:anycpu -unsafe -out:$out Program.cs Scheduling\IrqOriginalStore.cs `
    -r:"$fw\WPF\PresentationFramework.dll" -r:"$fw\WPF\PresentationCore.dll" `
    -r:"$fw\WPF\WindowsBase.dll" -r:"$fw\System.Xaml.dll" `
    -r:"$fw\System.Drawing.dll" `
    -resource:dpc.sys `
    -win32icon:app.ico -win32manifest:app.manifest
if ($LASTEXITCODE) { throw 'csc failed' }

if ($Test) {
    Write-Host 'BUILD OK -> DunSuiteLite_test.exe (no obfuscation)'
    return
}

$confuser = $env:CONFUSEREX_CLI
if (-not $confuser) { $confuser = "$PSScriptRoot\tools\ConfuserEx\Confuser.CLI.exe" }
if (-not (Test-Path $confuser)) {
    throw 'ConfuserEx not found. Set CONFUSEREX_CLI or place Confuser.CLI.exe under tools\ConfuserEx\. Use -Test to build without obfuscation.'
}
& $confuser -n confuser.crproj | Select-Object -Last 2
if ($LASTEXITCODE) { throw 'confuser failed' }
Copy-Item 'confused\DunSuiteLite.exe' 'dist\DunSuiteLite.exe' -Force
Write-Host 'BUILD OK -> dist\DunSuiteLite.exe'
