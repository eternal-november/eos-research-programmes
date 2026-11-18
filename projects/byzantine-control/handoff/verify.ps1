param([string]$LeanExecutable)

$ErrorActionPreference = 'Stop'
$proofFile = Join-Path $PSScriptRoot 'Foundations.lean'
$toolchain = (Get-Content -LiteralPath (Join-Path $PSScriptRoot 'lean-toolchain') -Raw).Trim()

if (-not $LeanExecutable) {
    $elanCommand = Get-Command elan -ErrorAction SilentlyContinue
    $elanRoots = @()
    if ($env:ELAN_HOME) { $elanRoots += $env:ELAN_HOME }
    if ($elanCommand) { $elanRoots += Split-Path (Split-Path $elanCommand.Source -Parent) -Parent }
    $toolchainDirectory = $toolchain.Replace('/', '--').Replace(':', '---')
    foreach ($elanRoot in $elanRoots) {
        $candidate = Join-Path $elanRoot "toolchains/$toolchainDirectory/bin/lean.exe"
        if (Test-Path -LiteralPath $candidate -PathType Leaf) {
            $LeanExecutable = $candidate
            break
        }
    }
}

if (-not $LeanExecutable) {
    throw "The pinned installed toolchain was not found. Pass -LeanExecutable with the path to its lean binary. This script does not install a toolchain."
}

$version = & $LeanExecutable --version
if ($LASTEXITCODE -ne 0) { throw 'Lean version check failed.' }
Write-Output $version
if ($version -notmatch 'version 4\.33\.0[,)]') {
    throw 'Expected Lean 4.33.0. Review compatibility before changing lean-toolchain and the verification record.'
}

$proofOutput = & $LeanExecutable $proofFile 2>&1
$proofExitCode = $LASTEXITCODE
Write-Output $proofOutput
if ($proofExitCode -ne 0) { throw 'Foundations.lean did not pass Lean checking.' }
$allowedAxioms = @('propext', 'Classical.choice', 'Quot.sound')
foreach ($outputLine in $proofOutput) {
    if ([string]$outputLine -match 'depends on axioms: \[(.*?)\]') {
        foreach ($axiomName in ($Matches[1] -split ',\s*')) {
            if ($axiomName -notin $allowedAxioms) { throw "Unexpected proof dependency: $axiomName" }
        }
    }
}
Write-Output 'Foundations.lean passed. Inspect the axiom reports and the semantic scope in VERIFICATION.md.'
