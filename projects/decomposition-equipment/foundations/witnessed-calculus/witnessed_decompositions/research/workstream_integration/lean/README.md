# Checked integration representative — exact scope

Contract v0.1: `47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
Cleared target: `2f8cc8b77165ef9d5fe915799e5291089067b10f0683f82d9f878ba1da1c7f7b`.
Author evidence only; independent review and parent acceptance remain separate.

## What is new and checked

`QuotientArrowCertificates.lean` imports the **actual** accepted A3
`Presentation.quotient`, `Presentation.Derives`, strict projection and the
**actual** B2 `SemanticRefinement.Arrow`/`comp`. It proves that equality of two
arrows with common endpoints is equivalent to derivability between independently
chosen raw representatives at every original source occurrence. Each chosen
representative is proved to have the entry's whole prescribed typed path.
Consequently each entry profile is retained, not only the concatenated target
profile. Entrywise certificates respect the actual B2 composition. The strict
projection's identity/composition statements are checked against that API.

The optional `arrow_eq_iff_entry_codes` bridge takes a proved **operation-level**
code completeness equivalence and derives an exact arrow-code equivalence. It
is explicitly conditional on that object-level theorem. It does not assume
arrow fullness, faithfulness, liftability, or categorical coherence. It is not
itself the implementation of a particular graph normalizer or a decision
procedure on a noncomputable quotient representation. Choice of raw quotient
representatives is noncomputable and uses the standard `Classical.choice`.

`PublicExampleBridge.lean` instantiates this criterion in the existing genuine
mixed-interface associative quotient. Its two actual B2 arrows have equal
substituted endpoints but are not entrywise derivable. This is an integration
regression of accepted B2 distinctions, not a newly claimed general phenomenon.

`GraphForestNormalForms.lean` works on the actual A4 `FrontierForest` type,
whose finite index is the ordered frontier list, not a component-name lookup.
For every valid finite source tree on the six-vertex ambient ordered graph and
three-interface chain, it normalizes each independent forest entry. It proves:

1. validity, idempotence, and equality iff entrywise independently generated E;
2. equality iff every **full standardized local cut** agrees, including the
   retained local whole, ordered local blocks, intermediate arrows and value;
3. entrywise equations imply equations after the actual occurrence-dispatch
   graft, using the full arbitrary-forest traversal theorem; this proof needs
   hypotheses only at actual leaves, and treats nullaries without fake leaves;
4. graph-valid normalized grafts and representative mixed examples;
5. an actual four-slot forest on the six-vertex mixed path whose repeated
   nonempty middle components receive values 1 and 2 in Z/3: the final graft
   agrees with the identity-forest graft, but the normalized forest tuples are
   unequal; and a nonzero labelled nullary has empty frontier without losing
   its value.

The local implementation uses additive notation: 0 is the monoid identity and
Z/3 addition is witness aggregation. This is the same convention as the
inherited representative, not a change to the multiplicative P theorem.

## Matched slices and the honest P/L boundary

There is **no existing general Lean adapter** packaging all A4 graph generators
as a public `Signature` and `Calc`; the prior deliverable expressly supplies
that bridge in P. We do not invent one or assume its conclusion. The two checked
slices are connected by the inherited, reviewed proofs:

* `research/workstream_A/rewrite/LOCATED_SYNTAX_COMPARISON.md`: two-sided
  located/raw graph syntax comparison with exact occurrence dispatch;
* `research/workstream_A/rewrite/A3_LOCAL_COMPARISON.md`: actual finite
  declaration set, equality with the independently generated congruence,
  independent full flat-cut calculus and actual A3 quotient isomorphism.

The new public-code theorem can be instantiated through that P linkage. Such
an instantiation is **P using L components**, not an additional Lean-checked
full graph/refinement-category comparison. General K,N,M, the independent
category Comp, ordinary equation-path coherence, MOut/MIn path equalities,
completion equivalence, transport and all uniform factorization statements
remain the explicitly separate P dossier. No full categorical completion has
been encoded here, and the graph E proposition is not confused with equality
of equation paths. In particular this does not formalize B3 by defining arrows
to be semantic tuples.

The mandatory preexisting A4 normalizer and B1/B2 categories remain the main
bounded Lean slice. These new lemmas connect and stress-test the exact APIs;
they are not a novel theory, do not increase a mathematical completion
percentage, and do not settle the scientific product/pullback baseline issue.
A4/C5 positive-only obligations, B3 permitted branches and §3.6 gates remain
as stated in the target. No B4/D/E/F/G/I phase is activated.

## Reproduce

Portable default: from the delivered project root, put Lean/lake 4.35.0 on
PATH and install the dependencies fixed by its unchanged `lake-manifest.json`
into the current checkout. The script then prefers this checkout's Lake
environment:

```
python3 research/workstream_integration/lean/build.py
```

Optional explicit overrides (no historical path is needed on another machine):

```
WITNESSED_TOOLCHAIN_ROOT=/absolute/path/to/lean-4.35.0-linux \
WITNESSED_LAKE_PROJECT=/absolute/path/to/checkout-with-matching-pinned-packages \
python3 research/workstream_integration/lean/build.py
```

`WITNESSED_TOOLCHAIN_ROOT` accepts either a Lean distribution containing
`bin/lean` and `bin/lake`, or the documented recovery-root layout containing
`lean-4.35.0-linux/bin/`. Omit it to use tools already on PATH. The optional
`WITNESSED_LAKE_PROJECT` selects only dependency package paths; every delivered
locked dependency revision must match. Where each package has its own Git
metadata, its actual Git HEAD must also equal the lock revision and its tracked
worktree must be clean; these are read-only checks. Missing Git metadata is
explicitly reported as lock-only rather than claimed verified. These source
provenance checks do not rebuild or independently hash-match generated external
package oleans. Its old project build path is rejected,
not reused. Without that override the current source checkout is preferred
when its packages directory exists. The helper does not fetch dependencies or
silently choose a different checkout.

For this particular task's ready, documented recovery installation only, the
historical fallback must be selected explicitly:

```
WITNESSED_USE_RECOVERY=1 python3 research/workstream_integration/lean/build.py
```

This opt-in route points to
`/workspace/shared/witnessed_B_20261024/toolchain_recovery`; it is a convenience
for reproducing here, not a required external-machine path. The selected
project, compiler version, matched package revisions, accepted external paths
and rejected project paths are recorded in the result. Package roots and all
LEAN_PATH candidates are compared by canonical realpath, so an installed
`.lake/packages` symlink works without admitting old project build directories.

The script creates a new `lean/runs/<UTC>/fresh/` directory; reconstructs the
actual project dependency closure from source imports; compiles all those
project modules and the three inherited A4 modules from source; compiles the
new modules and audit; verifies the number and standard whitelist of all 31
explicit transitive axiom reports; screens the new theorem sources for
placeholders/custom axioms/native oracles; and checks all 811 inherited file
hashes before and after. It does NOT read old project `.olean` paths. Only
pinned external package caches and the compiler's standard library are reused,
with exact paths recorded. This is not a source rebuild of Lean/mathlib.

`AxiomReport.json`, `TheoremIndex.json`, `SourceSnapshot.sha256` and the final
run `result.json` bind the author-checked sources. Allowed axioms are only
`propext`, `Classical.choice`, `Quot.sound`; the actual per-declaration closures
are listed, not merely a blanket permitted set. Kernel `decide`/`norm_num`
proofs are used in finite examples; there is no `native_decide`, custom axiom,
`sorry`, or unchecked external calculation in a theorem.

## Development history

The first complete two-module fresh build passed. A subsequent stronger
four-entry forest example initially failed elaboration because the numeral 1
could not synthesize `OfNat (FrontierIndex rightBare)`. The repair supplies the
explicit index `⟨1, by decide⟩`; it does not change the theorem or target.
`graph_revision_01.log` preserves the failed elaboration and
`graph_revision_02.log` the successful repair. The final fresh build supersedes
those development runs. The first aggregate wrapper passed all Lean compilations
but failed its audit call because it passed the log text instead of a log Path;
the wrapper was corrected and rerun from a new build directory. That failure
is retained, not counted as a complete pass. No historical baseline source
was edited. A later portability-only harness revision added the explicit
environment overrides above and rejected implicit historical fallback; theorem
source bytes and all 31 audit statements remained unchanged.

## Current-checkout symlink failure and repair

The parent's first automatic-current-checkout run on the fresh reproduction
source failed before any project theorem compiled: Lake returned resolved
package paths while the harness compared them with an unresolved symlink path.
The resulting search path lacked Mathlib. The exact failed log/result and
pre-repair harness are preserved under `harness_failures/`; this failure was
never counted as a mathematical failure or a complete reproduction pass.

The repair canonicalizes the package root, standard-library root, candidates
and excluded project-build directory with realpath, and rejects a path under
the selected project build even if it otherwise qualifies. It also now checks
actual package Git HEAD/clean tracked worktrees when Git metadata is available,
rather than describing matching manifests alone as verified source revisions.
Theorems and all 31 audit statements are byte-identical. The actual fresh
current-checkout route and an explicit-project route were then rerun; their
complete results and exact verified/unverified boundaries are recorded in
`HarnessPortability.json`.
