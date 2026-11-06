# Builds a distributable Windows x86_64 Rush release.
#
# Usage:
#   ./scripts/package-windows.ps1                 # host toolchain, build + package
#   ./scripts/package-windows.ps1 -SkipBuild      # package the existing binary
#   ./scripts/package-windows.ps1 -SkipSmokeTest  # do not compile examples/hello.rush
#
# Artifacts are written to dist/:
#   rush-v<version>-<target>.zip
#   rush-v<version>-<target>.zip.sha256

[CmdletBinding()]
param(
    [string]$Target = "",
    [switch]$SkipBuild,
    [switch]$SkipSmokeTest
)

$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

$Root = Split-Path -Parent $PSScriptRoot
Push-Location $Root
try {
    $Metadata = cargo metadata --no-deps --format-version 1 | ConvertFrom-Json
    $Package = $Metadata.packages | Where-Object { $_.name -eq "rush" } | Select-Object -First 1
    if (-not $Package) {
        throw "cargo metadata did not list the rush package"
    }
    $Version = $Package.version

    if (-not $Target) {
        $hostLine = rustc -vV | Where-Object { $_ -like "host: *" }
        $Target = $hostLine.Substring("host: ".Length).Trim()
    }
    if ($Target -notmatch "^x86_64-pc-windows-(gnu|msvc)$") {
        throw "this script packages Windows x86_64 only, not '$Target'"
    }
    $Abi = $Matches[1]

    $Dist = Join-Path $Root "dist"
    $Name = "rush-v$Version-$Target"
    $Stage = Join-Path $Dist $Name
    $Zip = Join-Path $Dist "$Name.zip"
    $Checksum = "$Zip.sha256"

    if (-not $SkipBuild) {
        Write-Host "building rush $Version for $Target"
        $buildArgs = @("build", "--release", "--locked", "--target", $Target)
        & cargo @buildArgs
        if ($LASTEXITCODE -ne 0) {
            throw "cargo build failed"
        }
    }

    $Exe = Join-Path $Root "target/$Target/release/rush.exe"
    if (-not (Test-Path -LiteralPath $Exe)) {
        throw "missing $Exe; run without -SkipBuild first"
    }

    $printed = (& $Exe --version).Trim()
    if ($printed -ne "rush $Version") {
        throw "unexpected version output '$printed' (expected 'rush $Version')"
    }

    if (Test-Path -LiteralPath $Stage) {
        Remove-Item -LiteralPath $Stage -Recurse -Force
    }
    New-Item -ItemType Directory -Path $Stage | Out-Null
    New-Item -ItemType Directory -Path (Join-Path $Stage "examples") | Out-Null

    Copy-Item -LiteralPath $Exe -Destination $Stage
    foreach ($file in "README.md", "CHANGELOG.md") {
        Copy-Item -LiteralPath (Join-Path $Root $file) -Destination $Stage
    }
    $license = Get-ChildItem -LiteralPath $Root -File | Where-Object { $_.Name -match "^(LICENSE|COPYING|NOTICE)" } | Select-Object -First 1
    if ($license) {
        Copy-Item -LiteralPath $license.FullName -Destination $Stage
    }
    Copy-Item -LiteralPath (Join-Path $Root "examples/hello.rush") -Destination (Join-Path $Stage "examples")

    # The GNU toolchain normally links these statically, but a locally built
    # binary may still import them. Bundle whichever ones are actually needed.
    if ($Abi -eq "gnu") {
        $wanted = @("libgcc_s_seh-1.dll", "libwinpthread-1.dll", "libssp-0.dll")
        $needed = @()
        $objdump = Get-Command objdump -ErrorAction SilentlyContinue | Select-Object -First 1
        if ($objdump) {
            foreach ($line in (& $objdump.Source -p $Exe)) {
                if ($line -match "DLL Name:\s*(\S+)") {
                    $needed += $Matches[1]
                }
            }
            $needed = $needed | Where-Object { $wanted -contains $_ } | Sort-Object -Unique
        } else {
            # Without objdump, bundle the usual GNU support DLLs conservatively.
            $needed = $wanted
        }
        $sysroot = (rustc --print sysroot).Trim()
        $dirs = @(
            (Join-Path $sysroot "lib/rustlib/$Target/bin"),
            (Join-Path $sysroot "bin")
        )
        foreach ($dll in $needed) {
            $source = $null
            foreach ($dir in $dirs) {
                $candidate = Join-Path $dir $dll
                if (Test-Path -LiteralPath $candidate) {
                    $source = $candidate
                    break
                }
            }
            if ($source) {
                Copy-Item -LiteralPath $source -Destination $Stage
                Write-Host "bundled $dll"
            } else {
                Write-Warning "rush.exe imports $dll but it was not found in the Rust sysroot"
            }
        }
    }

    if (-not $SkipSmokeTest) {
        $staged = Join-Path $Stage "rush.exe"
        $compiler = Get-Command gcc, clang, cc -ErrorAction SilentlyContinue | Select-Object -First 1
        if (-not $compiler) {
            Write-Warning "no C compiler on PATH; skipping the example smoke test"
        } else {
            $tmp = Join-Path ([System.IO.Path]::GetTempPath()) ("rush-smoke-" + [guid]::NewGuid().ToString("N"))
            New-Item -ItemType Directory -Path $tmp | Out-Null
            try {
                Copy-Item -LiteralPath (Join-Path $Root "examples/hello.rush") -Destination $tmp
                $output = & $staged run (Join-Path $tmp "hello.rush") 2>&1
                $code = $LASTEXITCODE
                if ($code -ne 0) {
                    throw "packaged compiler failed to build the example (exit $code):`n$($output -join "`n")"
                }
                if (($output -join "`n") -notmatch "Hello from Rush!") {
                    throw "the example did not print its greeting:`n$($output -join "`n")"
                }
                Write-Host "smoke test ok: packaged compiler built and ran examples/hello.rush"
            } finally {
                Remove-Item -LiteralPath $tmp -Recurse -Force -ErrorAction SilentlyContinue
            }
        }
    }

    if (Test-Path -LiteralPath $Zip) {
        Remove-Item -LiteralPath $Zip -Force
    }
    Compress-Archive -Path (Join-Path $Stage "*") -DestinationPath $Zip -CompressionLevel Optimal
    $hash = (Get-FileHash -LiteralPath $Zip -Algorithm SHA256).Hash.ToLowerInvariant()
    [System.IO.File]::WriteAllText($Checksum, "$hash  $(Split-Path -Leaf $Zip)`n", [System.Text.Encoding]::ASCII)

    Write-Host ""
    Write-Host "package:  $Zip"
    Write-Host "checksum: $Checksum"
} finally {
    Pop-Location
}
