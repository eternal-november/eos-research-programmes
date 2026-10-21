param([string]$LeanExecutable, [string]$PythonExecutable = 'python')
$ErrorActionPreference = 'Stop'
if (-not $LeanExecutable) {
    $elanCommand = Get-Command elan -ErrorAction Stop
    $elanRootForResearch = Split-Path (Split-Path $elanCommand.Source -Parent) -Parent
    $LeanExecutable = Join-Path $elanRootForResearch 'toolchains/leanprover--lean4---v4.33.0/bin/lean.exe'
}
$version = & $LeanExecutable --version
if ($LASTEXITCODE -ne 0 -or $version -notmatch 'version 4\.33\.0[,)]') { throw 'Lean 4.33.0 required.' }
Write-Output $version
$proof = & $LeanExecutable (Join-Path $PSScriptRoot 'Control.lean') 2>&1
$proofExit = $LASTEXITCODE
Write-Output $proof
if ($proofExit -ne 0) { throw 'Control.lean failed.' }
$reports = 0
foreach ($line in $proof) {
    if ([string]$line -match "does not depend on any axioms|depends on axioms:") { $reports++ }
    if ([string]$line -match 'depends on axioms: \[(.*?)\]') {
        foreach ($axiom in ($Matches[1] -split ',\s*')) {
            if ($axiom -notin @('propext','Classical.choice','Quot.sound')) { throw "Unapproved axiom: $axiom" }
        }
    }
}
if ($reports -ne 14) { throw "Expected 14 axiom reports, saw $reports." }
$actualJson = & $PythonExecutable (Join-Path $PSScriptRoot 'check_models.py')
if ($LASTEXITCODE -ne 0) { throw 'Finite model checks failed.' }
$expectedJson = Get-Content -LiteralPath (Join-Path $PSScriptRoot 'results.json') -Raw
if (($actualJson -join "`n").Trim() -ne $expectedJson.Replace("`r`n", "`n").Trim()) { throw 'Reproduced results differ from committed results.json.' }
Write-Output '14 Lean declarations and all finite checks passed; results.json reproduced exactly.'
Write-Output 'See COMPLETION.md for semantic review and unproved implementation premises.'
