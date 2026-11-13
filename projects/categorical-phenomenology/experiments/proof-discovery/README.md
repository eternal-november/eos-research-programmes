# Checked lemma discovery: exploratory list-theory diagnostic

## Result

The program does learn and reuse a lemma that was absent from its initial library. It does **not** show an advantage for failure-guided discovery over ordinary completion.

Starting from four recursive list definitions, both enumerators discovered

> reverse(reverse(X) ++ Y) = reverse(Y) ++ X.

A separate checker accepted its structural-induction certificate. The intermediate law is then used in certificates for larger, previously unpresented equations. However, failure-guided ranking adds work without improving the early-stop result. Ordinary full completion proves more of the fixed test workload for fewer instrumented operations than the guided early-stop variant. Identically stopped full-completion variants also favor ordinary ordering on this operation measure.

This is a small, constructed, **exploratory mechanism test**, not an established benchmark, new mathematics, or evidence for a new categorical/phenomenological principle. The test theory, training target, and candidate language were chosen by a person. It learns proof-library entries, not a new datatype, semantics, induction principle, or hypothesis language.

## Reproduce

Requirements: Python 3 standard library only. No installation, network, Lean, or mathlib is used. Lean and Lake were not on PATH, and a shallow workspace search found no ready Lean project.

From this directory:

```sh
python -m unittest test_kernel -v
python experiment.py --method all --budget 10000000
python experiment.py --method all --budget 1000000
python experiment.py --method all --budget 100000
python experiment.py --method random --seed 11 --budget 10000000
python experiment.py --method random --seed 23 --budget 10000000
python experiment.py --method random --seed 47 --budget 10000000
python run_timing.py
python audit_results.py
python kernel.py results/guided_10000000_proofs.json
```

Deterministic costs and proof success should reproduce exactly. CPU/wall times will vary. `REPRODUCE.py` runs the deterministic checks and comparisons without replacing the included timing measurements.

## Theory and semantics

Lists are finite lists over an arbitrary element type. The constructors are `nil` and `cons`. `append` and `reverse` have only these four defining axioms:

1. append(nil, Y) = Y.
2. append(cons(a, X), Y) = cons(a, append(X, Y)).
3. reverse(nil) = nil.
4. reverse(cons(a, X)) = append(reverse(X), cons(a, nil)).

Statements are universally quantified, well-typed list equations. Every reported success has an equality certificate checked against these definitions plus earlier checked lemmas. Counterexample testing can reject proposals; it never certifies them.

### Trusted checking boundary

`kernel.check_bundle` is the public trusted boundary. It checks library entries sequentially before checking held-out proofs. Calling `check_equation` with arbitrary unverified library statements would be unsound use of that internal API: its library argument intentionally assumes previously established theorems.

The checker supports equality by rewriting under congruence and structural induction on one universally quantified list variable. The induction certificate has:

- A nil case.
- A cons case with a fresh element and a fresh tail.
- An induction hypothesis with the tail **rigid**. Other original parameters remain universally quantified and may be instantiated.

The rigid-tail condition prevents the invalid move of applying the induction hypothesis to the very cons-list being proved. It is explicitly tested. Substitution is sort checked; unbound replacement variables, unknown or circular dependencies, invalid paths, and freshness violations are rejected. There are no admissions, external equality oracles, finite-model acceptance rules, or unchecked induction schemas.

Soundness argument: the primitive equations hold by the recursive definitions; typed substitution and congruence preserve equality; sequentially certified lemmas preserve this invariant; and the two checked branches justify finite structural induction with generalized parameters. This is a mathematical argument plus code review/tests, **not** a machine-verified proof of the Python checker.

## Discovery algorithm

Training presents only `reverse(reverse(X)) = X`. Direct simplification and one-variable induction first fail. The system records failed normal forms.

The candidate grammar contains X, Y, Z, nil, unary reverse, and binary append, with at most five AST nodes per term. There are 308 raw terms. The program evaluates them on all 343 assignments of X, Y, Z to lists of length at most two over {0,1}, groups equal signatures, pairs terms, identifies variable renamings, and orients equations with a lexicographic path order. It obtains 416 candidates. These numbers are outcomes of generic enumeration, not a supplied lemma list.

Each candidate is attempted by the same simplification-plus-induction search. Failed candidates can be retried after a checked theorem is added. The ordinary order is expression size followed by a deterministic syntactic tie-break. The guided order prioritizes candidates whose left sides match recorded failed subterms. Neither ordering sees held-out equations. All test-time retained libraries are frozen; test successes do not add lemmas.

The learned combined reversal law can be proved without first knowing reverse-of-append: induction on X generalizes Y. In the step, associativity exposes `reverse(reverse(tail) ++ (singleton(head) ++ Y))`, allowing the induction hypothesis with a larger parameter Y. This illustrates useful strengthening of a theorem within a fixed candidate language.

## Comparisons

- **Definitions only:** one-variable induction and primitive simplification. This is an intentionally weak but transparent baseline.
- **Training theorem only:** charge ordinary discovery and all dependency checks, but expose only the proved training theorem to held-out search. The intermediate dependency certificates remain private evidence, not usable rewrite rules.
- **Ordinary / guided early stop:** stop discovery when training succeeds, retain its certificate and every discovered lemma.
- **Ordinary / guided full completion:** same candidate pool and proof machinery, but continue until no remaining candidate adds a theorem. Both immediately retain the proved training theorem. This controls for stopping behavior.
- **Cold rediscovery:** run fresh discovery for each actual target, with no library retention across targets. This is an amortization ablation, not the strongest competitor. Its acquisition costs are charged every time.
- **Random order:** same automatic machinery with fixed seeds 11, 23, 47.
- **Supplied normalizer:** four human-selected standard list laws, each proved and checked from the definitions. Human selection cost is not measured, so this is a non-competing diagnostic upper bound, not evidence of discovery efficiency.

## Fixed workload and exploratory amendments

`fixed_cases_before_run.json` froze the original twelve transfer equations and eight definition-only controls before the first run. `audit_results.py` checks that the current workload is unchanged. There is one training target. No held-out equation is used to construct candidates or guide search.

After seeing the first run, weaknesses in retention and baselines were corrected. Original code and outcomes remain under `snapshots/v0`, `snapshots/v1`, and `snapshots/v2`; `amendments.json` lists every substantive change. This is **not external preregistration**.

The initial twelve transfer equations included equations that the generic enumerator could itself propose. Therefore the report also uses a **post-hoc, exploratory compositional subset**: the eight original equations for which at least one side exceeds the frozen five-node grammar bound. None is exactly a learned library statement. All original twelve-equation outcomes are still reported. The subset rule is uniform across algorithms and size based, but choosing it after the first outcome prevents a confirmatory claim. These are compositional syntactic holdouts, not independent-domain or semantic out-of-distribution tests.

## Accounting

A counter charges grammar construction, every finite evaluation call, signature handling, candidate construction/canonicalization, ordering, guidance ranking, rule indexing, matching, substitution, proof attempts (including failures), traversal, and each independent certificate check. All discovery, failed attempts, learning, validation, and test search phases are included.

The sum is an **instrumented-operation proxy**, not CPU instructions, FLOPs, or a claim that different operation types cost the same. Python hashing, comparison, allocation, tuple concatenation, variable-set extraction, and sort internals are not individually instrumented. End-to-end CPU and wall times include these operations. Final artifact serialization and redundant external auditing are excluded from algorithm timing; every acceptance check used by the algorithm is included.

Every method receives the same 100k, 1m, or 10m proxy cap. A completed method need not waste unused budget. A phase may stop just below its cap if its next atomic charge would exceed it. An independently completed certificate that exceeds the cap is not retained as a success. CPU-capped tests additionally use identical 0.05, 0.25, and 0.5 CPU-second allowances, checked every 128 proxy operations. Actual CPU usage and small cap overruns are recorded; these are not hard-real-time limits. An unchanged algorithm's five timing repetitions are reported without significance claims.

## Negative transfer and scope limits

On the eight definition-only controls, all completed solvers prove all eight equations. Learned libraries add dispatch/matching overhead: ordinary full completion uses 885 test-only proxy units versus 745 for definitions only (+18.8%), even before acquisition. At a 100k all-in cap, every discovery variant exhausts its allowance before evaluation, while definitions-only still proves the eight controls. Reuse is therefore not uniformly beneficial.

The strongest positive conclusion is that machine-proposed, independently checked intermediate lemmas transfer to new composite equations in this small theory. The failed stronger claim is that this failure-guided ordering improves the tradeoff over reasonable automatic completion. Three fixed random orders also solve all eight compositional cases, further weakening any claim specific to failure guidance.

Limits include a hand-chosen easy theory and grammar, one training theorem, small correlated test set, incomplete induction search, no learned new vocabulary, no real theorem-library benchmark, exploratory amendments, and a custom trusted checker. Results do not establish a general discovery mechanism or distinguish any categorical formulation from conventional inductive theorem discovery.

## Files

- `RESULTS.md`: actual outcomes and timing summary.
- `kernel.py`: independent proof checker.
- `experiment.py`: enumeration, search, accounting, and methods.
- `test_kernel.py`: 16 adversarial/unit tests.
- `audit_results.py`: frozen-workload, certificate, and reuse audit.
- `results/`: raw runs, proof bundles, timing repetitions/caps, and audit outputs.
- `protocol_before_run.json`, `fixed_cases_before_run.json`, `amendments.json`: design provenance.
- `snapshots/`: all earlier reported versions, not discarded failures.
- `FINAL_SOURCE_SHA256.txt`: hashes of final executable sources.

### Independent accounting qualifications

An external audit identified two boundaries worth making explicit. Timers stop before the final redundant bundle replay; they cover the algorithm's acquisition/search and its per-certificate checking, not that additional audit. Also, a verification runs atomically before its charge is accepted: if that last charge exceeds the budget, `cost.total` can omit performed-but-rejected verification work. `audit_accounting.py` wraps the unchanged algorithm and checks this boundary. In all 24 reported deterministic method/cap combinations, performed-but-uncharged kernel work was **zero**. CPU-capped runs can still slightly overrun and must be read using their actual measured CPU times, not as exact hard caps.

Cold rediscovery first pays for the same training episode and then discards what it learned before each actual held-out target. It is the no-retention learner on the same training-plus-test sequence, not the cheapest solver that starts directly with a test goal.


## Separate follow-up and conceptual prior

`screening_followup/RESULTS.md` reports a new, pre-run-frozen synthetic workload designed after this initial diagnostic. It compares reduced versus exhaustive finite screening for both full-completion methods. The reduction improves the operation proxy but worsens randomized repeated CPU/wall time; it does not rescue a distinctive failure-guidance advantage. The original source and outcomes above remain unchanged.

Rawson, Wernhard, and Zombori's [Learning to Identify Useful Lemmas from Failure](https://aitp-conference.org/2023/abstract/AITP_2023_paper_18.pdf) is a relevant conceptual prior. Their three-page 2023 abstract proposes learning from failed attempts; its then-current experiments concern successful-attempt unit lemmas, while failure/Horn extraction was still being implemented. This small heuristic-ordering experiment is neither a replication of their neural selector nor evidence that the general idea is new.

The initial source hashes in `protocol_before_run.sha256` apply to `snapshots/v0`, not the amended final source. Use `FINAL_SOURCE_SHA256.txt` for the final executable version.
