# Targeted independent portability addendum

**PASS — the actual current-checkout symlink failure is repaired and was
independently reproduced successfully.** This addendum concerns harness,
documentation and evidence metadata only. The original
`Lean_Independent_Review.md` remains unchanged at SHA256
`70177873e61ac33eb3ae80245423cf597f7be5f41c559396e86074ce8a5ebf58`.
Its mathematical, P/L-boundary and nonacceptance-of-scientific-significance
verdicts remain in force.

Reviewer: `/root/verify_integration_lean_slice`; 25 October 2026.

## Frozen repair

- `lean/build.py`:
  `80879b843dfedbb96eb021f53b4e37c6a993048495525d5da63b7f4c2f9f9d0e`.
- `lean/HarnessRealpath.diff`:
  `7ef46095127b13053c751a2737f05fc0cb10c9000909edb9d856a67b3225dede`.
- Revised `lean/SourceSnapshot.sha256`:
  `a068d9258c255cdac6cf3380cfe6676db00cdeb6bddd21acf6a9264909208e60`.
- `lean/HarnessPortability.json`:
  `2c110676783f6b4d8b1342e45dcac3b3b3ac989e82426f3aeb72a49b3505980d`.

All manifest entries were verified. All 77 Lean sources copied for the original
independent review still match their reviewed bytes, including the new three
modules and audit. All 811 inherited files still match the baseline manifest.
No mathematical source change or full mathematical re-review is implicated.

## Observed failure and repair inspection

The preserved `lean/harness_failures/current_checkout_symlink_failure.json`
records a real first-import failure, not a mathematical counterexample. The
old filter compared lexical absolute package paths against the real paths
returned by Lake when the checkout's `.lake/packages` directory was a symlink.
It incorrectly rejected the installed package paths.

The diff now resolves the compiler library, selected package root, project
build root and every candidate search path before comparison. It admits only
canonical paths beneath the selected package root or the compiler library,
while explicitly rejecting the canonical selected-project build tree. It also
requires at least one accepted package path, so accepting only the compiler
library cannot conceal the former defect.

The new provenance checks require actual Git HEAD to match each locked
revision and require a clean tracked worktree when package-owned Git metadata
is available. They reject mismatch/errors rather than treating them as passes.
Unavailable metadata is explicitly recorded `GIT_METADATA_UNAVAILABLE_LOCK_ONLY`.
This is a disclosed trust distinction, not proof that an unavailable Git tree
matches its lock. Read-only Git checks do not modify the packages.

## Independent replay of the previously failing route

With only the documented `toolchain_recovery/env.sh` sourced, and
`WITNESSED_TOOLCHAIN_ROOT`, `WITNESSED_LAKE_PROJECT`, and
`WITNESSED_USE_RECOVERY` explicitly removed from the environment, the reviewer
ran the repaired wrapper in the actual fresh reproduction checkout:

`/workspace/shared/witnessed_integration_20261025/reproduction/fresh_source/witnessed_decompositions`.

That checkout's `.lake/packages` is an actual symlink to the pinned dependency
installation. The result selected `current_source_checkout`, not an override
or historical fallback. It freshly compiled **23 modules**, verified **31
axiom reports**, checked **all nine actual package Git HEADs and clean tracked
worktrees**, and preserved **811 baseline files before/after**. The canonical
project build path was rejected. The result and all compilation logs are copied
into `review/lean_portability_addendum_20261025/current_source_replay/`.

The prior author current-source and explicit-project route evidence, the
preserved failed run, README's precise path/trust description, and revised
source/theorem/dependency metadata were inspected and hash-bound. This addendum's
new independent full replay exercises the previously failing automatic route;
it does not mislabel author executions as independent runs.

## Configuration fault injection

`configuration_checks.py` extracts and executes the **exact parsed**
`configure_environment` function without running its build top level. It uses
the actual current checkout and packages, with explicitly mocked subprocess
responses only for named faults. The separate full Lean replay above has no
mocks. Five checks pass:

1. Actual current-source configuration accepts all nine clean pinned packages.
2. An incorrect actual Git HEAD is rejected.
3. A dirty tracked package worktree is rejected.
4. A symlink alias to the old project build plus compiler library, with no valid
   package path, is rejected rather than admitting stale project outputs.
5. Missing package Git metadata is explicitly reported lock-only, never
   reported as verified actual HEAD/worktree provenance.

The review-only extraction harness initially omitted `json` from its supplied
globals; its preserved first-attempt log records that harness error. Adding the
required module to the execution globals and rerunning all five checks passed.
This did not require any change to the author harness or theorem sources.

## Limits and conclusion

Git source provenance and a clean tracked worktree do **not** validate generated
external `.olean` bytes or untracked files. Those external caches and the
compiler remain the disclosed reused trusted base; no dependency/Lean source
rebuild or cache hash attestation is claimed. All nine packages in the actual
reviewed run had available Git metadata and passed its stronger check.

The repaired harness passes this targeted review. The old snapshot in the
original report remains historical; the revised manifest above supersedes it
for harness/docs/metadata only. No new scientific acceptance, direct Lean graph
adapter, full `Comp` formalization, or obligation closure follows from this
portability repair.
