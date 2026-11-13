# C2 finite certificate: exact domain and executable conventions

Contract v0.1 SHA256
`47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
Frozen pre-proof target SHA256
`b6711190a46b19205ef25f439105eaf1951137d90f5e55a595ea67daf172e2f4`.
These are **C** certificates, not unrestricted proofs or Lean kernel results.
Full C2 remains **OPEN** for later D2/E use. No later obligation is activated.

## Run and trust boundary

From this directory, with Python 3.10 or later and only its standard library:

```
python3 check_c2_model.py --output AuthorCertificate.json
python3 run_mutations.py --output MutationCertificate.json
```

The first command runs F1–F6; `--named-only` is explicitly a smoke test and
cannot substitute for that run. The JSON is deterministic: runtimes are printed
only to stdout (`AuthorRun.log`), not embedded in the certificate. Each JSON
records the exact checked source hash. No random seed, external solver, network
connection, unchecked data import, or third-party library is used. Python
assertions must remain enabled: do not run `python -O`. The two relation
algorithms inside the author source give redundant author checking, **not**
independent authorship. Independent checking lives in the separately authored
review directory and must not import these algorithms.

`run_mutations.py` compiles four actual modified source strings into isolated
in-memory modules and reruns the original tests. It never edits the source
checkpoint. Each mutation must cause an assertion or validation failure; an
undetected mutation fails the runner. The mutants reverse containment, replace
composite-of-pulls by pull-of-composite, key replacements by component instead
of occurrence, and replace the nullary diagonal by the empty relation.

## Coordinates and two evaluators

An interface is a pair `(label, cardinality)`; a label is not erased when two
cardinalities agree. Its element coordinates are `[n]={0,...,n-1}`. A relation
on `[a] × [b]` is a bit mask: entry `(x,y)` is bit `x*b+y`. Every integer
`0 <= mask < 2^(a*b)` is included, so empty, universal, partial, nonfunctional,
non-total, and all other relations occur. A map `[a']→[a]` is a length-`a'`
tuple with entries in `[a]`; all such tuples are enumerated, including the
unique empty tuple and excluding nonexistent nonempty-to-empty functions.

`join` computes matrix composition by taking unions of selected bit rows.
`chain` iterates it, starting at the diagonal on the first interface.
`global_chain`, independently of `join` and `chain`, enumerates every tuple of
vertex values on a path, checks every edge, and collects its endpoint pairs.
For an empty path the tuple has one coordinate, so this yields exactly the
diagonal, including the empty diagonal on `[0]`.

`Profile` retains the ordered component tuple and actual interface labels;
`Cell` stores its **independent whole relation** and checks containment.
`exact_cell` uses a separate equality check, not merely the containment check.
`substitute` consumes one child per original occurrence, checks each child's
whole against the corresponding original component, and concatenates the full
typed profiles. `Generator` stores a distinct primitive name and its chosen
semantic cell. `Node` and `Leaf` are unquotiented syntax; their evaluator may
identify groupings or names but never declares the syntax equal.

## F1: all binary restriction comparisons

For every `(a,b,c,a',b',c')` in `{0,1,2}^6`, enumerate **all** functions
`f:[a']→[a]`, `g:[b']→[b]`, `h:[c']→[c]`, all relations
`R⊆[a]×[b]`, and `S⊆[b]×[c]`. There is no nonemptiness filter.
Compare these different relations:

- `compose(pull(R,f,g), pull(S,g,h))`;
- `pull(compose(R,S), f,h)`.

Check the inclusion; compare the left side with the independent vertex-tuple
algorithm; check equality whenever `g` is surjective; explicitly map **every**
realizing primed triple `(x',y',z')` to `(f(x'),g(y'),h(z'))` and check that it
is an original realizing triple. Then enumerate **every** `W⊇compose(R,S)`
and check the surviving restricted containment cell. Original and resulting
exact/nonexact classes are counted independently.

| Check | Count |
| --- | ---: |
| Original relation pairs over the 27 original size triples | 499 |
| Full valid relation/function comparison cases | 113,171 |
| Cases with surjective intermediate map | 33,821 |
| Strict comparisons | 17,424 |
| Primed realizing triples mapped and checked | 75,547 |
| All original containing-whole cells restricted | 661,613 |
| Original nonexact cells among those | 548,442 |
| Resulting exact cells | 364,341 |
| Resulting nonexact cells | 297,272 |
| Comparison cases with empty primed endpoint | 35,043 |
| Comparison cases with empty original intermediate set | 121 |

These counts do not count merely size shapes as successful comparisons when
one of the required functions does not exist.

## F2: all ternary associativity and unit checks

For every `(a,b,c,d)∈{0,1,2}^4`, enumerate all independent relations
`R⊆[a]×[b]`, `S⊆[b]×[c]`, `T⊆[c]×[d]`. Both binary groupings and the global
vertex-tuple result must agree. This is **8,507** triples, of which **1,075**
have at least one empty interface. For each of the **31** relations on every
pair of sizes in `{0,1,2}`, check both units by both evaluators: **62** unit
equalities per evaluator. No finite test is claimed to prove arbitrary arity.

## F3: every frozen path, segmentation, inner whole and outer whole

For each flat arity `n=0,1,2,3`, each size vector `(a_0,...,a_n)` with every
entry in `{0,1,2}`, and every independently chosen relation on each edge,
enumerate every weak composition `(l_1,...,l_k)` of `n` for `k=0,1,2,3`.
Here `k=0` is possible only for `n=0`. With cumulative cut positions
`0=c_0≤c_1≤...≤c_k=n`, the inner profile `q_i` is exactly the contiguous
subpath from position `c_(i-1)` to `c_i`. If its length is zero, both endpoints
are the **same boundary position and label**, not two equally sized labels.

For every such segmentation, independently compute every `C(q_i)` and verify
that composing those block composites recovers the flat composite using both
algorithms. Then explicitly enumerate every tuple of relations
`R_i⊇C(q_i)` and, for that tuple, **every** outer whole
`W⊇C(R_1,...,R_k)`. Check `C(flat)⊆W` for each instance. The exact case takes
`R_i=C(q_i)` and `W=C(flat)`; it is checked separately for each segmentation
and is also included in the containment enumeration.

There is **no weighted skipping or factorization** of this domain. Caches only
memoize pure finite relation operations on already specified inputs. No family
is omitted on the grounds that it has the same truth value as another.

| Check | Count |
| --- | ---: |
| All flat profiles | 9,040 |
| Profile/segmentation pairs | 132,793 |
| Exact substitutions | 132,793 |
| Nullary inner segments among those pairs | 124,853 |
| Inner-whole relation families | 8,162,514 |
| All containing outer-whole substitutions | 25,619,591 |
| Nonexact outer cells among those substitutions | 17,457,077 |
| Nonexact resulting composite cells | 24,395,285 |

The outer-arity counts of profile/segmentation pairs are respectively
`k=0:3`, `k=1:9,040`, `k=2:35,590`, `k=3:88,160`.
An independent arithmetic cross-check is that the numbers of flat profiles
of arity `0,1,2,3` are `3,31,499,8,507`, and their numbers of weak-composition
choices summed over `k≤3` are `4,6,10,15`. Thus
`3*4+31*6+499*10+8507*15=132793`.

This numerical enumeration uses boundary positions with specified cardinalities.
It covers any compatible naming of those positions: identifying two boundary
labels only requires their cardinalities to agree and imposes the corresponding
component equality if a component is repeated. Such equal-table cases are
already included among the independently ranging masks. Renaming does not
change a matrix calculation. The separate typed API tests retain actual labels,
reject unequal-label nullaries even at equal cardinality, and explicitly test
repeated identical components. This is a cardinality-skeletal finite certificate,
not an enumeration of infinitely many possible strings used as interface names.

## F4: principal strict comparison and positive controls

Use distinct labels `A,B,C` of sizes `2,3,2` and

```
R = {(0,0),(1,2)} : A→B
S = {(0,0),(2,1)} : B→C
C(R,S) = {(0,0),(1,1)}
W = {(0,0),(1,1),(0,1)}
```

Both `C(R,S)` and the strict containing whole `W` define legitimate cells;
they are not silently identified. Restrict along identity endpoint maps and
`g:[2]→[3]`, `g=(0,1)`. The composite of restricted components is `{(0,0)}`,
whereas restriction of the original composite is `{(0,0),(1,1)}`. The original
exact cell becomes a **valid nonexact containment cell**. Its original
realizers are `(0,0,0)` and `(1,2,1)`; the latter has no lift.

Positive control: `g:[4]→[3]`, `g=(0,1,2,2)`, is onto and many-to-one. Exactness
survives, and the actual map on realization tuples is noninjective. Separately
use noninjective endpoint maps `(0,0,1)` and `(0,1,1)` together with that
surjection. Identity and two-stage restrictions are checked as equal complete
cells. Empty-endpoint and empty-intermediate controls show why emptiness cannot
be excluded from a future converse or surjectivity criterion.

## F5/F6: typed syntax, occurrences, nullaries and actual mutations

The named four-leaf profile is `R,L,L,S`, where `L` is the nonempty universal
relation on `B×B`. The two middle component objects are literally equal.
Different binary trees have the same complete relational cell. The first `L`
occurrence receives `[Delta_B,L]` and the second `[L,Delta_B]`, both exact cells
with whole `L`. Reusing the first replacement at both positions or swapping
these legal same-output replacements changes the complete ordered profile.
A nested substitution subsequently replaces the first diagonal by a nullary
exact cell and checks the two associativity routes. Restriction/substitution
commutation in the author checker uses one global map per named interface and
non-nullary child cells. The separately authored independent checker additionally
checks restriction/graft with a nullary replacement. The per-interface map
convention ensures that the two incidences of its contracted loop agree; the
author nested-nullary associativity check alone is not claimed as that additional
restriction/graft certificate.

Separate primitive labels `alpha` and `beta` have the same chosen cell and
remain different raw corollas. No semantic-kernel quotient is introduced.
The nullary cell `()≤L` is legitimate but nonexact; `()=Delta_B` is exact.
Pulling the exact nullary on a singleton along the constant map from a two-point
set produces the full kernel-pair relation (mask 15), while the new empty-path
composite is the diagonal (mask 9). The exactness failure is explicit and is
not disguised by vacuous internal surjectivity. The empty-set nullary is tested.

Named validation controls reject wrong endpoints, reversed order, wrong
repeated-occurrence output, unequal-label nullaries, false exactness,
incorrect restriction endpoints, and two independently supplied endpoint maps
for a nullary contraction. Four in-memory source mutations are executed by the
separate runner; their failure certificates are in `MutationCertificate.json`.

## What this does not establish

The API here is a finite executable model, not the public Lean `Calc` itself.
The precise public-API correspondence and unbounded model proofs belong to
the parent proof/Lean artifacts. These computations alone establish no
unrestricted theorem, equipment universal property, D2 sharp criterion,
faithful recovery of syntax, or novelty. Independent source inspection and
separately implemented checking are required before parent acceptance.
