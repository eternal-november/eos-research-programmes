# B1/B2 verification toolchain recovery

Status at 2026-10-24 22:42 UTC: PASS. Official Lean and all pinned dependencies/cache restored; complete original export verification passed, exit code 0.

## Confirmed configuration

- Source: `/workspace/shared/witnessed_B_20261024/witnessed_decompositions`
- Toolchain pin: `leanprover/lean4:v4.35.0`
- mathlib pin: `56a005855ea17e0b0958f73ec801ae140b0a1679`
- Transitive dependencies: exact revisions in `lake-manifest.json`; do not run `lake update`.
- Host: Linux x86_64; Python 3.12.14; curl, wget, tar, zstd, git, sha256sum available.
- Initially no existing `lean`, `lake`, or `elan` binary, compiler tar archive, `Mathlib.olean`, or `.ltar` cache found by allowed-filesystem search. Denied session paths were explicitly excluded.
- Following explicit user approval, normal direct networking successfully retrieved the official compiler archive; no denial was encountered.

## Restored compiler

Official source: `https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst`.

SHA256: `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`, verified against the `digest` of the matching asset in the official GitHub release API response, retained at `downloads/lean-v4.35.0-release.json`.

Unmodified official archive extracted to `lean-4.35.0-linux/`. Verified outputs:

```text
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
```

No global install or shell-profile edits. To use:

```sh
source /workspace/shared/witnessed_B_20261024/toolchain_recovery/env.sh
```

An independent baseline source copy is at `toolchain_recovery/baseline`. Restoration and baseline verification have finished. Main project `.lake/packages` links to its stable `.lake/packages`; project build directories remain separate. mathlib checkout was confirmed at the exact pinned commit, with the official upstream remote and a clean git worktree.

## Fresh verified baseline

Command:

```sh
cd /workspace/shared/witnessed_B_20261024/witnessed_decompositions
set -o pipefail
bash ./verify_export.sh --finite-only 2>&1 | tee \
  /workspace/shared/witnessed_B_20261024/toolchain_recovery/baseline-finite-20261024T2236Z.log
```

Exit code: 0. Export bytes, unchanged completion contract, accepted logs, all 43 retained accepted-source snapshot entries, and all 35 Lean placeholder/custom-axiom/oracle screens passed. All four included finite certificates matched (ignoring only timing fields).

Result: `../witnessed_decompositions/reproduction/20261024T223558.808239Z/result.json` relative to this directory's parent. Canonical absolute location:
`/workspace/shared/witnessed_B_20261024/witnessed_decompositions/reproduction/20261024T223558.808239Z/result.json`.

This is bounded computational and integrity evidence, not fresh Lean evidence or an unrestricted mathematical proof.

## Complete baseline verification receipt

All 9 package revisions and upstream URLs matched `lake-manifest.json`; details are in `dependency-pin-verification.json`. The default official `https://cache.mathlib.org/mathlib4-master` cache supplied all 9031 artifacts. Cache use is disclosed: dependency binaries were not all rebuilt from source.

Commands (exit 0):

```sh
source /workspace/shared/witnessed_B_20261024/toolchain_recovery/env.sh
cd /workspace/shared/witnessed_B_20261024/toolchain_recovery/baseline
lake exe cache get
bash ./verify_export.sh
```

Full verification passed the public library build, explicit recompilation of exported theorem sources, full Mathlib smoke, adversarial/negative-typing tests, all named axiom closures, fresh A4 representative compilation/tests, and all four finite certificates. Original export integrity was checked before and after.

Receipts retained:

- `baseline-cache-get-20261024T2238Z.log`
- `baseline-full-20261024T2240Z.log`
- `baseline/reproduction/20261024T224050.552738Z/result.json` and all detailed logs
- `restoration.json` (metadata and receipt SHA256 values)

This is fresh verification of the original source checkpoint, not acceptance of new B1/B2 work or A4's open integration gate. No original theorem source, completion contract, dependency manifest, or historical evidence was edited.

## Reuse for B1/B2 work

```sh
source /workspace/shared/witnessed_B_20261024/toolchain_recovery/env.sh
cd /workspace/shared/witnessed_B_20261024/witnessed_decompositions
lake build
lake env lean <new-source.lean>
```

The main project's generated `.lake/packages` symlink reuses restored dependencies while `.lake/build` is independent. Coordinate build ownership with the implementation worker. Do not run `lake update` or mutate the shared dependency sources.
