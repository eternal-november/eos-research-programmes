# Finite integration: final reproduction and evidence

## Frozen scope and status

The final author full-domain run **PASSed**, with terminal exit 0, in 893.87
seconds. Formula/source verification and the five actual-source mutation replays,
including the separately targeted probes, also terminated with exit 0. This is
finite C support for the separately proved A4/C5/B3 package, not an unrestricted
proof or author acceptance of its own evidence.

Read the unchanged `DOMAIN.md` (SHA256
`d01495686d5f3f01cc635061d7789f64ab0cf5a370571d144971cb819dba52fa`),
`CoverageChecklist.md`, and both release records first. Initial domain execution
was released at 2026-10-25T01:01:45Z. After two stopped partial executions and
literal-domain coverage repairs, the parent released the final exact-source
replay at 2026-10-25T01:22:08Z (`FullRunRelease.json`). AuthorRun03 began at
01:22:18Z. The six executable source files remained unchanged through the full
run, formula verification and final mutations. `SOURCE_SHA256SUMS` binds their
exact bytes plus DOMAIN. No domain was narrowed after observing results.

Contract v0.1 remains unchanged, SHA256
`47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`;
technical target SHA256
`2f8cc8b77165ef9d5fe915799e5291089067b10f0683f82d9f878ba1da1c7f7b`.
Scientific significance is NOT accepted by these computations. The monoid
extension is a standard scalar enrichment. Later B4/C4/D/E/F/G/I obligations
and whole-bundle gates are not activated or discharged by this directory.

## Fresh-copy reproduction

Only Python's standard library is required. Copy **all six** Python files:
`model.py`, `check_integration.py`, `run_mutations.py`, `mutation_probes.py`,
`smoke_integration.py`, and `verify_certificate.py`, plus `DOMAIN.md` and
`SOURCE_SHA256SUMS`. The mutation runner copies both `mutation_probes.py` and
`smoke_integration.py` unconditionally, even in the final non-smoke mode.
Do not copy bytecode caches or old generated certificates into the fresh run.
From this source directory, on a POSIX system:

```sh
src="$PWD"
out=$(mktemp -d)
cp "$src"/{model.py,check_integration.py,run_mutations.py,mutation_probes.py,smoke_integration.py,verify_certificate.py,DOMAIN.md,SOURCE_SHA256SUMS} "$out/"
cd "$out"
sha256sum -c SOURCE_SHA256SUMS
export PYTHONDONTWRITEBYTECODE=1
python -u check_integration.py > AuthorRun.log 2>&1 &&
python -u verify_certificate.py > AuthorVerification.log 2>&1 &&
python -u run_mutations.py > MutationRun.log 2>&1
```

Require exit 0 from every command and PASS in `AuthorCertificate.json`,
`AuthorVerification.json`, and `MutationCertificate.json`. Mutation replay is
valid only after the complete unmutated run passes at the same source hashes;
the runner enforces that dependency. It writes actual modified sources,
stdout/stderr tracebacks, and targeted probe results beneath `mutations/`.
Elapsed times, certificate byte hashes that include those times, and absolute
traceback paths can vary on fresh replay. Compare all mathematical counts,
T-row formulas, the trace digest, exact source/domain hashes, intended mutation
classifications, and targeted probe contents, not elapsed-time bytes.

The final full checker took about 15 minutes here. The last factorization stage
intentionally brute-enumerates intermediate graphs/outer profiles; the named
six-vertex examples dominate runtime. It may produce no intermediate output
for several minutes. `DiagnosticPrefix.py/.json` is a separately labelled tiny
throughput diagnostic, not accepted mathematical evidence and not a required
reproduction input. It did not modify or replace any frozen checker stage.

## Actual final counts

All figures below are **executed counts from AuthorCertificate.json**, not
formula predictions substituted for execution. The verifier independently
recomputes the stated T/H-source/F/six-value formulas from finite domain sizes.

| Check | Executed |
|---|---:|
| All 18 critical-shape rows T | 112,785 |
| One-step reduct checks | 267,764 |
| Arising-label redex source/target restoration checks | 1,158 |
| Unique bare labels, Z3 / E2 / One | 147 / 102 / 67 |
| MIn contextual/forest squares | 54,028 |
| MOut forward / inverse squares | 217,661 / 217,661 |
| Ordinary disjoint / variable squares | 316 / 568 |
| Named raw forest composition / raw-then-equation paths | 1,736 / 1,736 |
| Exhaustive H source witnesses | 2,802 |
| H hom-set pairs / arrows | 233,562 / 463,222 |
| H empty hom sets / nonthin hom sets | 175,993 / 46,337 |
| Hcomp composable pairs, each checked by actual raw forests | 118,950 |
| Exhaustive proper-interval factorization cases | 27,270 |
| Factorization cases including named six-vertex cases | 27,300 |
| Factorization fibre elements | 63,700 |
| Full/unary probes / empty-interval probes | 180 / 180 |
| Unary-to-nullary value pairs | 42 |
| Six-vertex unary source/local value tuples | 276 |
| Six-vertex positional split value assignments (both splits per assignment) | 276 |
| d_0 towers, all five source occurrences and heights 0 through 8 | 135 |
| Transport raw edges / transport maps | 935,200 / 38,800 |
| Object-map composites / monoid-map composites | 175,200 / 8,256 |
| Nested graph restrictions / coordinate restrictions | 5,148 / 5,148 |
| Graph coordinate inverse pairs / interface rename inverse pairs | 1,314 / 438 |

The 112,785 T, 2,802 H-source, 27,270 exhaustive F, 27,300 total F, and 276
six-value expectations agree with execution. Historical partial MIn planning
counts based only on the original seven singleton recipes (including 17,804
squares) were **not the full frozen domain**. The final catalog contains the
original 106 unique templates plus 210 additional labels extracted from actual
nested X redexes. The full 316-template union gives 54,028 MIn squares and is
also used for ordinary disjoint/variable squares. There was no outcome-based
shrinking. Earlier partial logs and exact source snapshots remain under
`history/`; smoke certificates are explicitly preflight subsets, not final
acceptance. See `FailureRegister.md` for the chronology.

## Independent routines and what they establish

Three implementations compare meanings: recursive local tree substitution,
root-address leaf traversal, and operation-only flat substitution. H compares
local-operation catalog tuples against an independently coded target-run
hom decoder. Every Hcomp pair is reified as raw trees, composed by positional
forest grafting, and compared to independent flat substitution. Factorization
compares brute candidate intermediate graphs/partitions to a forced-union
decoder. These are same-author redundant implementations; non-author clean
replay and no-author-import checks are recorded separately in
`../review/finite_independent_20261025/`.

Path normal forms retain the raw forest at the ORIGINAL source occurrences.
Tests validate addressed instances of the independently declared relations and
the 18 explicit joining rule words. They do not define categorical arrow
equality as semantic tuple equality, or prove global ordinary/mixed coherence.
The unrestricted theorem remains P; no term-depth/arity bound on it is inferred
from this finite suite. Whole graphs/grades and every entry's profile,
partition, interface arrows and scalar value remain in the arrow data.

## Actual-source negative controls

The final runner executed all five edited-source mutants. Each exited 1 at
its **named intended AssertionError and detecting function**; SyntaxError,
TypeError, NameError, ImportError, arbitrary nonzero exit, or the wrong
assertion would fail the runner. Exact edits, before/after hashes, and retained
traceback hashes are in `MutationCertificate.json`.

| Mutant | Intended detected defect |
|---|---|
| `omit_MIn` | MIn certificate unavailable to the syntactic relation basis |
| `merge_repeated_occurrences` | Positional raw graft disagrees with flat substitution |
| `erase_nullary_value` | Recursive value disagrees with independent address evaluation |
| `erase_entry_profile` | Full-entry profile collision |
| `corrupt_MOut_residual` | Well-typed wrong residual at equal-color, distinct occurrences |

A first intentional failure does not execute all later checker sites. Therefore
separate targeted mutated-copy probes were actually run after the ordinary
mutant subprocess:

* `omit_MIn`: bare and contextual MIn rejection for each of Z3, E2 and One;
  raw-added weights 0 through 8 at all four named six-vertex slots plus the
  empty-loop slot, all retaining identity semantic tuples (135 cases).
* `erase_nullary_value`: all three nonidentity scalar choices across Z3 and
  E2; a typed MIn-DL unit path is validated with independent address semantics,
  then the intended recursive local-value mismatch is detected.

Missing-MIn validator rejection is syntactic sanity, not itself the necessity
proof. The tower computations illustrate the separate P raw-added-vertex
invariant; neither they nor any mutant establish unrestricted relation
independence. `mutations/*/TargetedProbe.json` and probe stdout/stderr retain
these additional executions.

## Final evidence identifiers

* Author certificate: `bc4be682414f765a17877e91188913174e545f3d41ad74f72783a8f2ade4e9bf`.
* Full trace: `2b44858dbbc3d0dac77a2fca7503d96e436beebca427879714327388c7632a87`.
* Author formula/source verification: `7caa25b1b4e2c54c02d21950465b1b5d0a689d057b828faa205caf808572b0b4`.
* Final mutation certificate: `e9e5d8ea5cc7c20921e383cbb4bcb7d09c1ebb7245493ec7999e4f898de87fc2`.

Author PASS is not a substitute for independent acceptance. The separate review
owns the scope audit, fresh-copy replay, independent implementations and final
C disposition. No blanket acceptance of A4/C5/B3 or the whole contract is made
by this reproduction file.
