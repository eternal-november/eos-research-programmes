# Ordered-group refunds and exact bounded observation windows

This is a hand-written Lean 4.35.0 formalization extending the existing `ResourceObservationIff` development. It uses only Lean's bundled `Std`; no package installation or mathlib is needed. The existing two dependency sources are copied byte-for-byte into `dependencies/` and freshly compiled by the validation script.

## Verified conclusions

### 1. Full ordered abelian-group obstruction

`OrderedGroupRefunds.lean` defines `OrderedAbelianGroupData G` with ordinary algebraic and order laws: addition, zero, inverse, associativity, commutativity, identities, reflexivity, transitivity, antisymmetry, and translation monotonicity. No observation/congruence property occurs in this structure. Translation reflection is derived using inverses.

For an arbitrary predicate B on G, the main theorem is:

> UniversalProductAgreement(add, ≤, B) iff ∀ b, B(b) → ∀ x, B(x).

Here universal product agreement has exactly the previously formalized meaning: all pairs of upward profiles agreeing locally on B have products agreeing on B; the product is the upward closure of additive composition. Thus any nonempty universally compositional observation region is all of G. The proof uses the existing equivalence with observed factor domination. Choose v = −u+b; the condition supplies observed a≥u and c≥v with a+c≤u+v; cancellation and antisymmetry force a=u.

The generic constructive theorem and its nonempty/proper impossibility corollary have **no axiom dependencies**. A literal “B is empty OR B is all” formulation requires an extra logical step. We provide:

- An axiom-free disjunction theorem with an explicit `Decidable (∃ b, B b)` input.
- The exact unrestricted disjunction in `ClassicalGroupCorollary.lean`, using Lean's standard classical logic. Its dependencies are `propext`, `Classical.choice`, and `Quot.sound`.

This distinction is real: on a singleton group, the unrestricted disjunction for arbitrary B would yield excluded middle for any proposition.

### 2. Integer refund counterexample

The standard integers instantiate the full group interface. With B={b | b≤0}, the upward sets U={b | 2≤b} and U'={b | 3≤b} agree on B, while composing each with V={b | −2≤b} gives different answers at 0. B is proved downward closed. Thus downward closure is insufficient when unrestricted refunds are allowed.

These concrete integer theorems depend on Lean's standard `propext`, not on a new axiom. They should **not** be described as axiom-free.

### 3. Exact two-stage bounded-refund theorem

`BoundedRefunds.lean` proves a necessary and sufficient threshold theorem for **two stages, one integer resource dimension**. Fix known integer lower bounds l,r, a total cap C, and arbitrary local observation regions A,B. Profiles are independent upward sets U,U',V,V' with U,U'⊆↑l and V,V'⊆↑r. Composition is the existing existential additive product, observed throughout [l+r,C].

> Universal agreement on the output interval [l+r,C] iff A contains every point of [l,C−r] and B contains every point of [r,C−l].

The upper thresholds are shifted by the **other** stage's known lower bound, not by its cost observed after the fact. The proof takes these lower bounds as explicit premises. Sufficiency uses bounds on every feasible pair, not upward closure. Necessity compares principal profiles with their observation-generated upward subsets; these remain within the lower-bounded class.

C≥l+r is not needed for the statement as formulated: if C<l+r, both required local windows and the output window are empty, and the theorem correctly becomes vacuous. The nonempty operational case is C≥l+r. This does not infer lower bounds from data, assume executable physical compensation, model shared hidden correlations, or claim prefix-capacity safety. Independent Cartesian choice of components and additive ledger cost are encoded in the product definition.

The report's numerical example is checked: l=−2, r=1, C=3 gives local windows [−2,2] and [1,5], with output [−1,3]. A separate theorem proves that applying cap 3 to both local stages fails. This is a universal observation-domain lower bound, not a lower bound on query count for any single instance or optimum certificate.

The bounded integer theorems use standard `propext` and `Quot.sound` through integer arithmetic and Lean's `omega` proofs. **They are not axiom-free.** There are no new axioms and no `sorry`/`admit` placeholders.

### 4. Antisymmetry control

`PreorderControl.lean` proves that Bool with XOR is an abelian group and that the indiscrete relation is a translation-invariant preorder but is not antisymmetric. The nonempty proper region {true} is universally compositional for that preorder. All these control theorems have no axiom dependencies. Therefore replacing “partial order” by an arbitrary preorder would invalidate the literal set-membership conclusion.

## Verification and scope

Extract the archive and enter its `lean_refunds` directory. Use Python 3 and Lean 4.35.0. No third-party Python packages are required. Set `LEAN_BIN` to your Lean executable, or put `lean` on `PATH`. The validators check the Lean version and use only the included dependencies. Run:

```sh
python validate.py
python check_finite_windows.py
```

`validate.py` removes and rebuilds its own `.build/`, confirms the two dependency copies match the recorded SHA-256 hashes from the preceding development, compiles the seven positive source/audit files, rejects three deliberately false/broken controls, checks no theorem depends on `sorryAx`, and writes exact hashes and axiom dependencies to `validation.json`. No network is used. Compiler: Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc.

`AuditSignatures.lean.log` contains elaborated theorem signatures, the full group structure fields, the bounded universal predicate, and axiom audits. In particular the main IFFs have algebraic data, bounds, and observation regions as inputs, not their conclusions hidden among assumptions.

The three expected failures remove the essential monotone factor transport, replace the left threshold C−r by C+r, and attempt to use the correct shifted-window theorem to certify the false uniform-cap example. These compile failures supplement, rather than replace, the formal mathematical counterexamples. The deliberately rejected files are never imported into accepted modules; their error-recovery logs can mention `sorryAx`, whereas all accepted theorem audits exclude it.

Finite sanity tests cover 539 triples (l,r,C), including 200 empty-output cases, and reject omission of every required point across those triples. See `finite_checks.json` for the actual counts. Finite tests do not establish the universal theorem; Lean does.

**Not formalized here:** the full n-stage/vector/rational-weight theorem, finite query counts, minimum-cost algorithm, unbounded iteration, executable refund semantics, or prefix-capacity composition. These remain outside this artifact's verified scope. No novelty claim is made.

## Independent review

`independent_review.md` records an independent source-level mathematical review and clean rebuild in a separate directory. Verdict: **PASS**, with no semantic defect or circular hypothesis found within the stated scope. Reproduce it with:

```sh
python independent_validate.py
```

The reviewer added `IndependentAudit.lean` without changing the theorem sources. It formally checks empty windows, failure when a required upper endpoint alone is missing, and extension of output agreement from [l+r,C] to every budget ≤C (budgets below l+r cannot be feasible). It also proves, with no axioms, that a literal empty/all classification for every observation predicate implies excluded middle. The independent build results and source hashes are in `independent_audit.json`.

## Portable release and log provenance

All accepted Lean theorem and audit sources are byte-identical to the independently reviewed originals. `SOURCE_HASHES.json` records their original SHA-256 hashes. Only packaging text and validation scripts were adapted for portability. The fixed dependency hashes let the package rebuild without the earlier development directory.

The included compiler logs and validation JSON were freshly regenerated during the portable replay, with source filenames passed relative to the package directory. They are direct captures from that replay, not the original first-run logs and not path-sanitized versions of those logs. Each validator records stdout followed by stderr. The review document records the original independent review; the portable replay does not replace that review.

`MANIFEST.json` records every distributed file hash except its own. Generated `.build` and `.independent_build` directories are excluded from the archive and recreated locally. A clean extraction was tested using both the explicit `LEAN_BIN` route and PATH-based compiler discovery. No environment-specific workspace paths are required.
