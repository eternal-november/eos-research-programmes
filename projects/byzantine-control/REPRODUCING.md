# Reproducing Byzantine-control results

From this project's `exclusive-service` directory, run unoptimized Python 3.12 with `python -B check_cover.py`, `python -B carrier_case.py` and `python -B quorum_case.py`. Run `lean ExclusiveService.lean` with Lean 4.33.0. The adjacent [contextual-composition project](../contextual-composition/) contains the manuscripts assessed in [IMPORTS](exclusive-service/IMPORTS.md).

## Frozen scientific checks

The [97-check receipt](portability/PROGRAM-VERIFICATION.json) applies to the Git objects and original paths named in it. Use an isolated original-layout clone for historical reproduction. Run the following PowerShell commands from the research-programmes repository root with Git, Python 3.12 and Lean 4.33.0 installed. Choose an unused path for the clone and a new output filename for each run. The archive branch must be available in the repository you clone.

```powershell
$research = (git rev-parse --show-toplevel)
git show-ref --verify --quiet refs/heads/archive/byzantine-control-evidence
if ($LASTEXITCODE -ne 0) {
    git fetch --no-tags origin refs/heads/archive/byzantine-control-evidence:refs/heads/archive/byzantine-control-evidence
    if ($LASTEXITCODE -ne 0) { throw 'The evidence archive is unavailable from origin.' }
}
if ((git rev-parse refs/heads/archive/byzantine-control-evidence) -ne '5803f72336f92bfd24d2955b6141e73ef5c52eec') { throw 'Unexpected evidence archive revision.' }
$replay = Join-Path ([IO.Path]::GetTempPath()) ('byzantine-verification-' + [guid]::NewGuid().ToString('N'))
git clone --no-local --single-branch --no-tags --branch archive/byzantine-control-evidence $research $replay
git -C $replay switch --detach cb358a77f0bcbfd42f92422aa2367e2323f08bc3
Push-Location (Join-Path $replay 'theories-and-designs/byzantine-control/portability')
python -B program_replay.py --at cb358a77f0bcbfd42f92422aa2367e2323f08bc3 --freeze-commit 6069e2b55d9642063813117b30f7f86ec928d1a4 --selection-commit 35418fde54f73e46ccc3d766025e0337d1b6ba24 --lean (Get-Command lean).Source --research-repo $research --jobs 4 --output (Join-Path $replay 'byzantine-verification-result.json')
Pop-Location
```

The archive keeps the original research tip `7906283bd435eee9bfb7720d7f192d5747e47497` and the off-branch source trees used by the historical checkers. Use the original tip for inspections by original eos-garden commit ID. The [concurrent-activity comparison](local-control/COMPOSITION.md) cites tracked source at `6fd7b83123de03ceb1c47f8d2d5f014b089976bd`, also retained there. Inspect it with `git ls-tree -r --name-only 6fd7b83123de03ceb1c47f8d2d5f014b089976bd -- theories-and-designs/concurrent-activity`. The comparison also mentions untracked exploratory material. That material has no Git identity at the cited revision.
