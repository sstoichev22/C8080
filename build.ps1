# Builds build/c8080.jar (compiler + bundled stdlib). Needs ..\intel8080 (built on demand) and ..\vulcanos\stdlib.
$ErrorActionPreference = 'Stop'
$here = Split-Path -Parent $MyInvocation.MyCommand.Path
$jdk = Get-ChildItem -LiteralPath (Join-Path $env:ProgramFiles 'Java') -Directory -Filter 'jdk*' -ErrorAction SilentlyContinue |
    Where-Object { Test-Path (Join-Path $_.FullName 'bin\javac.exe') } | Select-Object -Last 1
if ($jdk) { $bin = Join-Path $jdk.FullName 'bin'; $javac = "$bin\javac.exe"; $jar = "$bin\jar.exe" }
else { $javac = (Get-Command javac).Source; $jar = (Get-Command jar).Source }
$cpuJar = Join-Path $here '..\intel8080\build\intel8080.jar'
if (-not (Test-Path $cpuJar)) { & (Join-Path $here '..\intel8080\build.ps1') }
$classes = Join-Path $here 'build\classes'
if (Test-Path $classes) { Remove-Item $classes -Recurse -Force }
New-Item -ItemType Directory -Force $classes | Out-Null
$sources = Get-ChildItem (Join-Path $here 'src') -Recurse -Filter *.java | ForEach-Object FullName
& $javac --release 17 -encoding UTF-8 -cp $cpuJar -d $classes @sources
if ($LASTEXITCODE -ne 0) { throw 'Compilation failed.' }
foreach ($d in 'include','lib') { Copy-Item (Join-Path $here "..\vulcanos\stdlib\$d") (Join-Path $classes "stdlib\$d") -Recurse -Force }
& $jar --create --file (Join-Path $here 'build\c8080.jar') -C $classes .
if ($LASTEXITCODE -ne 0) { throw 'Packaging failed.' }
'Created build\c8080.jar'
