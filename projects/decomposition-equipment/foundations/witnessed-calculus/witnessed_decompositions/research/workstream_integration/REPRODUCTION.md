# Reproduce the integrated technical checkpoint

This is a reproducibility procedure, not scientific acceptance. The unchanged
contract is v0.1, SHA256
`47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
Frozen technical target:
`2f8cc8b77165ef9d5fe915799e5291089067b10f0683f82d9f878ba1da1c7f7b`.
Frozen new finite domain:
`d01495686d5f3f01cc635061d7789f64ab0cf5a370571d144971cb819dba52fa`.

## Dependencies and clean source

Use Python 3 with its standard library and Lean 4.35.0. The delivered
`lean-toolchain` and `lake-manifest.json` are unchanged; mathlib is pinned to
`56a005855ea17e0b0958f73ec801ae140b0a1679`, with the other package revisions
recorded in that manifest. Install those public dependencies through the
normal Lake workflow. Fetching public packages/compiler is a separate access
requirement; this report does not pretend a private installation is portable.

Extract the final source archive into a NEW directory. Do not copy a previous
project `.lake/build` or cached project `.olean` files. Public dependency
objects may be reused at their pinned revisions, with the stated trust limit:
Lean and all of mathlib are not rebuilt from source by this checkpoint. In the
recorded final environment all nine actual dependency Git HEADs and clean
tracked worktrees were additionally checked. Generated external `.olean`
cache bytes remain reused and are not independently source-bootstrapped.

The new Lean harness accepts `WITNESSED_TOOLCHAIN_ROOT` and
`WITNESSED_LAKE_PROJECT` for explicit installations. Without an override it
prefers the current checkout's packages. Symlinked package roots are resolved
canonically; the selected project's own old build path is always rejected.
The historical convenience cache is available only with explicit
`WITNESSED_USE_RECOVERY=1`, never a silent fallback. Read lean/README.md for
exact examples and the lock-only disclosure when package Git metadata is
unavailable. The inherited full-chain drivers require the pinned compiler on
PATH and the current checkout's installed Lake packages.

## Complete technical replay

From the project root:

```
bash verify_workstream_integration.sh
```

The default driver checks all 811 inherited files, the contract, target,
domain and new mathematical source snapshot; reruns the ENTIRE unchanged
A/B/C1/C2/C3 verification chain; compiles the new Lean representative and its
31 named axiom closures from fresh project objects; copies the new finite
sources into a clean directory; reruns the full author domain, formula/source
verification, all five actual source mutations, and targeted bare/contextual/nullary probes; and reruns the separate
no-author-import reviewer checker on its explicitly smaller mixed/named
supplement and full critical-shape domain. It checks the deterministic
mathematical results against the frozen certificates and checks hashes again.
New logs/results are written under `reproduction_integration/<timestamp>/`.
No accepted source or prior certificate is overwritten.

For a single already-running clean-source verification, the driver can reuse
a completed C3-chain result from that SAME checkout using
`--completed-fresh-inherited-result <path>`. It still verifies all inherited
source bytes and records the original execution interval/hash and the reuse
explicitly. This avoids repeating an identical completed fresh baseline while
new integration-only checks finish. It is not permission to substitute old
project proof objects or an unrelated author-local build for clean evidence.

## Standalone checks and evidence boundaries

* `python3 research/workstream_integration/lean/build.py` checks the bounded
  L slice. It proves neither all-N/K/M in Lean nor the categorical completion.
* Copy `finite/model.py`, `check_integration.py`, `run_mutations.py`,
  `mutation_probes.py`, `smoke_integration.py`, `verify_certificate.py`, and
  `DOMAIN.md` to a new directory; run the main
  checker, then certificate verifier, then mutations. `finite/REPRODUCTION.md`
  describes each domain and intentional rejection. Do not run the mutations
  before the unmutated final source has passed.
* Copy reviewer `check_noimport.py`, `targeted_mutation_probes.py`, and
  `REVIEW_DOMAIN.md` together to a new
  directory and run the former. That independently coded representation
  checks its stated domain without author imports. It is NOT falsely claimed
  to duplicate every author X/H/F case; the full author domain is separately
  replayed and source-audited by the non-author reviewer. Run the targeted
  reviewer mutation supplement with the fresh finite directory as its argument
  after the five mutant directories have been created.

The P dossiers are complete written proofs with independent mathematical
review; a script does not certify them. The new public-API and located-graph
Lean slices are joined by the explicitly inherited P adapter, not a claimed
new direct Lean graph `Calc` or full `Comp` implementation. Finite C covers
exact stated bounds, while unrestricted generality is P. Named axiom closures
use only the disclosed standard principles; no sorry/custom desired-result
axiom or unchecked native oracle establishes a claimed theorem.

All review is agent-managed non-author review with correlated-model/tooling
limitations, not external human certification. Strongest-baseline analysis
finds a useful checked specialization/integration but no established new
scientific increment. Full §3.6, B4 and future F/D/E/G/I gates remain open.

## Recorded aggregate evidence versus running the wrapper

The final evidence manifest binds separately executed fresh components: the
complete unchanged inherited chain, the new representative (including actual
public-API imports), and the final independently replayed C sources. When those
exact final bytes have already passed, the parent permits reconciling their
receipts instead of a third identical full C run. The command

```
bash verify_workstream_integration.sh --check-receipts
```

checks all source hashes, each named evidence receipt, Python orchestration
syntax and the shell wrapper syntax only. Its result is explicitly
`PASS_RECEIPT_CHECK_NOT_REEXECUTION`. It does not rerun proofs or turn a
partial component into a pass. The final report states whether the default
all-component wrapper was executed as a whole; component-level fresh
execution and a receipt check are not mislabeled as that execution. The
actual mathematical/import comparison remains supplied by the source-bound
component runs and independent reviews.

The default driver's control flow was additionally smoke-tested in a temporary
copy by `python3 scripts/check_integration_orchestration.py`: its seven
expensive subprocesses and source-invariant call were explicitly stubbed with
already executed receipts. This catches copy/dispatch/comparison plumbing, not
mathematics. The resulting simulated PASS files were deleted with the temporary
directory; the retained receipt is labelled
`PASS_CONTROL_FLOW_WITH_STUBBED_COMMANDS_ONLY`. A separate clean-copy import
closure check loaded the finite modules without executing their domains.
Neither check is represented as a full default-wrapper run.
