param([string]$Tectonic = "tectonic")

$ErrorActionPreference = "Stop"
$paperRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot ".."))
$buildDir = Join-Path $paperRoot "build"
$compiler = Get-Command $Tectonic -ErrorAction Stop

# Tectonic resolves references by rerunning TeX and retains diagnostic logs.
& $compiler.Source --keep-logs --keep-intermediates --outdir $buildDir (Join-Path $buildDir "main.tex")
if ($LASTEXITCODE -ne 0) {
    throw "Tectonic failed with exit code $LASTEXITCODE"
}
Copy-Item -LiteralPath (Join-Path $buildDir "main.pdf") -Destination (Join-Path $paperRoot "paper.pdf") -Force
Write-Output (Join-Path $paperRoot "paper.pdf")
