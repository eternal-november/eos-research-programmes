param([string]$LeanExecutable, [string]$PythonExecutable = 'python')
$ErrorActionPreference = 'Stop'
if (-not $LeanExecutable) {
    $elanCommand = Get-Command elan -ErrorAction Stop
    $elanRootForProgram = Split-Path (Split-Path $elanCommand.Source -Parent) -Parent
    $LeanExecutable = Join-Path $elanRootForProgram 'toolchains/leanprover--lean4---v4.33.0/bin/lean.exe'
}
$version = (& $LeanExecutable --version | Out-String).Trim()
if ($LASTEXITCODE -ne 0 -or $version -notmatch 'version 4\.33\.0[,)]' -or $version -notmatch 'd8b18978322d') {
    throw 'The packet requires Lean 4.33.0, commit d8b18978322d.'
}
Write-Output $version
$buildRootForProgram = Join-Path $PSScriptRoot '.program-build'
New-Item -ItemType Directory -Force -Path $buildRootForProgram | Out-Null
$buildForProgram = Join-Path $buildRootForProgram ('run-' + [guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Path $buildForProgram | Out-Null
$beforeHashesForProgram = @(& $PythonExecutable -B (Join-Path $PSScriptRoot 'program_check.py') --fingerprints-only)
if ($LASTEXITCODE -ne 0) { throw 'Cannot capture unoptimized source fingerprints.' }
$oldLeanPathForProgram = $env:LEAN_PATH
$env:LEAN_PATH = $buildForProgram
$modulesForProgram = [ordered]@{Control=14; Execution=19; Evidence=19; Institution=16; Digital=19; TimedRecovery=19; QuorumAlignment=8; Foundations=15}
$logForProgram = [System.Collections.Generic.List[string]]::new()
$totalForProgram = 0
Push-Location $PSScriptRoot
try {
    foreach ($moduleForProgram in $modulesForProgram.Keys) {
        $sourcePathForProgram = if ($moduleForProgram -eq 'Foundations') { Join-Path $PSScriptRoot '../handoff/Foundations.lean' } else { Join-Path $PSScriptRoot "$moduleForProgram.lean" }
        $sourceForProgram = Get-Content -LiteralPath $sourcePathForProgram -Raw
        $declaredForProgram = @([regex]::Matches($sourceForProgram, '(?m)^\s*(?:theorem|lemma)\s+([A-Za-z0-9_]+)') | ForEach-Object { $_.Groups[1].Value })
        $printedForProgram = @([regex]::Matches($sourceForProgram, '(?m)^#print axioms\s+([A-Za-z0-9_.]+)') | ForEach-Object { $_.Groups[1].Value })
        foreach ($declarationForProgram in $declaredForProgram) {
            if ($declarationForProgram -notin @($printedForProgram | ForEach-Object { ($_ -split '\.')[-1] })) { throw "Missing axiom report: $moduleForProgram.$declarationForProgram" }
        }
        if ($sourceForProgram -match '(?m)^\s*axiom\s+') { throw "Custom axiom declaration in $moduleForProgram" }
        if ($printedForProgram.Count -ne $modulesForProgram[$moduleForProgram]) { throw "Unexpected report manifest for $moduleForProgram" }
        if ($moduleForProgram -eq 'Foundations') {
            $proofForProgram = @(& $LeanExecutable $sourcePathForProgram 2>&1)
        } else {
            $proofForProgram = @(& $LeanExecutable -o (Join-Path $buildForProgram "$moduleForProgram.olean") $sourcePathForProgram 2>&1)
        }
        $exitForProgram = $LASTEXITCODE
        foreach ($lineForProgram in $proofForProgram) { $logForProgram.Add([string]$lineForProgram) }
        if ($exitForProgram -ne 0) { Write-Output $proofForProgram; throw "$moduleForProgram failed." }
        $reportsForProgram = @($proofForProgram | Where-Object { [string]$_ -match 'does not depend on any axioms|depends on axioms:' })
        if ($reportsForProgram.Count -ne $modulesForProgram[$moduleForProgram]) { throw "Wrong emitted report count for $moduleForProgram" }
        foreach ($lineForProgram in $reportsForProgram) {
            if ([string]$lineForProgram -match 'depends on axioms: \[(.*?)\]') {
                foreach ($axiomForProgram in ($Matches[1] -split ',\s*')) {
                    if ($axiomForProgram -notin @('propext','Classical.choice','Quot.sound')) { throw "Unapproved axiom: $axiomForProgram" }
                }
            } elseif ([string]$lineForProgram -notmatch 'does not depend on any axioms') {
                throw "Unparsed axiom report: $lineForProgram"
            }
        }
        $totalForProgram += $reportsForProgram.Count
        Write-Output "$moduleForProgram : $($reportsForProgram.Count) checked declarations"
    }
    $actualForProgram = @(& $PythonExecutable -B (Join-Path $PSScriptRoot 'program_check.py'))
    if ($LASTEXITCODE -ne 0) { throw 'Program executable checks failed.' }
    $expectedForProgram = Get-Content -LiteralPath (Join-Path $PSScriptRoot 'program_results.json') -Raw
    if (($actualForProgram -join "`n").Trim() -ne $expectedForProgram.Replace("`r`n", "`n").Trim()) {
        throw 'Reproduced program results differ from committed program_results.json.'
    }
    $afterHashesForProgram = @(& $PythonExecutable -B (Join-Path $PSScriptRoot 'program_check.py') --fingerprints-only)
    if ($LASTEXITCODE -ne 0 -or [String]::Join([Environment]::NewLine,$beforeHashesForProgram) -ne [String]::Join([Environment]::NewLine,$afterHashesForProgram)) {
        throw 'Sources changed across proof compilation and executable verification; discard this run.'
    }
    Write-Output "$totalForProgram research/foundation declarations and all executable checks passed."
    Write-Output 'program_results.json reproduced exactly, including normalized source digests.'
    Write-Output 'Proof compilation and finite checks do not mechanize the analytic proofs or validate physical trust roots. See PROGRAM-AUDIT.md.'
} finally {
    [IO.File]::WriteAllLines((Join-Path $buildRootForProgram 'lean-axioms.log'), $logForProgram)
    $env:LEAN_PATH = $oldLeanPathForProgram
    Pop-Location
}
