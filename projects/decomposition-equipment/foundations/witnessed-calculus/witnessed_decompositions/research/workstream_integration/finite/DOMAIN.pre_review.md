# Frozen proposed finite domain — integrated A4/C5/B3

Status: SUBMITTED FOR NON-AUTHOR PRE-EXECUTION REVIEW; no C test has run.
Contract v0.1 SHA256
`47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
Technical target SHA256
`2f8cc8b77165ef9d5fe915799e5291089067b10f0683f82d9f878ba1da1c7f7b`.
This is C support, not an unrestricted proof, a category quotient definition,
independent authorship, or scientific-scope acceptance. All 811 inherited files
remain unchanged. New sources and generated certificates live only here.

## 1. Finite tables and literal data

### Interface categories

C is the three-object chain. Objects are 0,1,2. Arrows are exactly
`00,01,02,11,12,22`, where ij:i→j. Identities are 00,11,22. The COMPLETE partial
composition table (row followed by column; `-` is not composable) is:

| ; |00|01|02|11|12|22|
|---|---|---|---|---|---|---|
|00|00|01|02|-|-|-|
|01|-|-|-|01|02|-|
|02|-|-|-|-|-|02|
|11|-|-|-|11|12|-|
|12|-|-|-|-|-|12|
|22|-|-|-|-|-|22|

C2 is C times the two-element group, used for the critical-rule domain and
named grade-retention controls. Its COMPLETE finite specification is objects
0,1,2 and arrows `(i,j,z)` for each of the six C arrows and z∈{0,1}; identities
`(i,i,0)`; `(i,j,z);(j,k,t)=(i,k,(z+t) mod 2)`, and no other composites.
Equivalently its 12-by-12 partial table replaces every defined C-table cell
with the group table `[[0,1],[1,0]]`; this specifies every entry, including all
nonidentity loops, without an unspecified operation. A flat cut retains the
ENTIRE string of these actual arrows, not only object names or total grade.

### Commutative monoids

Every listed carrier element is tested; no random palette selection occurs.

* Z3: carrier {0,1,2}, identity 0, operation table
  `[[0,1,2],[1,2,0],[2,0,1]]` (addition modulo 3).
* E2: carrier {0,1}, with 0 denoting mathematical 1 and 1 denoting e; identity
  0, operation table `[[0,1],[1,1]]` (the noncancellative idempotent monoid).
* One: carrier {0}, identity 0, operation table `[[0]]`.

All identity/associativity/commutativity laws are directly table checked.
Each source file receives a monoid table argument; no hard-coded Z3 aggregation
is permitted in the new general finite engine.

### Graphs, partitions, and terms

Graphs G=(r,E) have literal vertices [r], all unordered distinct pairs as the
possible edges, and no graph-isomorphism quotient. `Graphs(d)` includes ALL
`sum_{r=0}^d 2^(r(r-1)/2)` graphs. This count is 4 for d=2. A k-block ordered
partition is every function [r]→[k], encoded as the ordered inverse-image tuple;
empty blocks remain. For k=0 there is exactly one partition if r=0, none
otherwise (`0^0=1` convention). Restrictions use increasing ranks.

A term stores its full output graph and actual arrow, a constructor L/U/D/C,
children, actual binary cut subset, and each D value. L is an external identity
leaf; U exists only at `(empty,(a,a,0))`. Neither an empty L nor an empty
nonidentity-grade component is U. No arbitrary untyped term is counted.

## 2. Separate implementations and finite claims

`model.py` will contain the typed constructors and recursive tree evaluation by
local cut substitution. A separately coded root-address traversal carries
inclusions from root to leaves, collects the full graph/profile and D values,
and does not call the recursive evaluator or its block-lifting helper.
`flat_compose` is a third, operation-level routine consuming only full flat
witnesses and original-slot tuples, not terms. Normalization uses the actual
seven rewrite rules with their constructor addresses and the inherited
lexicographic measure; canonical reification is independently computed from a
full witness. For each checked term, compare these routines, every generated
one-step reduction, and actual normal form. None establishes unbounded
confluence or path coherence by computation.

Semantic arrows are explicit ordered tuples of full flat operations. The
principal hom decoder enumerates run lengths and pulls back target blocks;
the redundant encoder enumerates local operation catalogs, forms actual tuples,
then calls flat substitution. It does not call the hom decoder. Equality keys
retain each entry's graph/output arrow, profile/arrow string, partition, length,
and value, in original occurrence order. Different whole grades have no homs.

A path is a finite sequence of typed raw-graft and equation edges (equation
edges may be traversed backwards). Its normalizer processes edges while
retaining the original-slot raw forest, composes raw forests by leaf offsets,
and then normalizes every entry. It is tested on the syntactically generated
relation paths below. Equal semantic tuples are NOT used to define the
category's path congruence or claimed as a computational proof of completeness.
The category comparison/coherence theorem remains P evidence.

## 3. Exhaustive critical-template domain T

Use exactly the 18 labelled pattern rows in inherited `THEOREM.md` §7 and
`check_fragment.py` PATTERNS (identical rows, not invented peaks). For EACH
monoid Z3,E2,One and EACH row independently enumerate:

1. every G in Graphs(2);
2. every ordered partition of [r] into its k metavariable leaves;
3. every weakly increasing object string `(a_0,...,a_k)` in {0,1,2};
4. every string of k grade bits in {0,1}, giving every C2 arrow string;
5. every assignment of monoid values to the row's DISTINCT monoid parameters.

Instantiate all term metavariables as their actual identity leaves in this
exhaustive T domain. Nullary U nodes are actual units at the position's object.
For row with d independent monoid parameters, the expected number of T cases is

`sum_(r=0..2) 2^(r(r-1)/2) * k^r * binom(k+3,2) * 2^k * |M|^d`.

The implementation records each factor and separately counts actually executed
cases and every contextual one-step reduct examined. It checks all reducts,
not only the two named critical steps. Inherited shape numbering is preserved.
No product count is reported as executed unless the nested loops actually run.

## 4. Context/forest and relation-path domain X

To test non-leaf instantiation and surrounding contexts without pretending to
exhaust all terms, use this separate fully specified finite generated suite.
For EACH of the 18 rows, EACH monoid assignment, and EACH of two graph options
on k vertices (edgeless; also the graph with edge {0,k−1} if k≥2), place its
metavariable leaves on singleton blocks in order. For k=0 use only the empty
graph; for k=1 use only the edgeless graph. The object string is:

* k=0: (1); k=1: (0,2);
* k≥2: `(0,1,...,1,2)` of length k+1.

Grade bits are all 0, plus the string with first bit 1 when k≥1. Thus nonidentity
intermediate grades and a mixed path occur without any quotient of their data.

The surrounding one-hole context list is exactly: identity; D_v[-] for EACH
v∈M; C(U_a,[-]); C([-],U_b); C(L_empty,id_a,[-]); and C([-],L_empty,id_b).
The latter two add genuine external empty occurrences. There are 5+|M| context
instances, with no de-duplication even if a resulting semantic witness agrees.

For every resulting contextual equation edge e:t→u, apply the following forest
menu on its COMMON full frontier:

* all identities;
* for each original slot i, change ONLY that slot to D_v(L_i), for each v∈M;
* for each original slot i, change ONLY that slot to every binary corolla on
  that component: all subsets of its vertices, every intermediate object
  a_i≤b≤b_i, and both possible first grade bits, with the second determined
  by the existing total grade modulo 2;
* at each empty identity-graded loop occurrence, change only it to D_v(U),
  for every v∈M (including v=0);
* the simultaneous forest D_v(L_i) at EVERY original slot, for each v∈M.

For each entry and resulting forest, typing is tested before comparing the
MOut square. Verify the residual equation at the same old constructor address
is an actual single generated rewrite of the grafted tree. Then compare both
path-normalizer outputs and independent semantic tuple compositions. Include
inverse-equation squares by reversing e.

For MIn, use the seven BARE template pairs (all their finite label choices
arising in X), and every host context in the above list with its hole replaced
by an identity leaf of the pair's output. Insert l or r at that actual leaf;
verify the displayed residual equation and both mixed-path normal forms.
Then substitute each of the forest-menu instances into the bare template's
leaves, and test the same relation as a contextual instantiated MIn law.
These are exact schema instances, not pairs chosen by equal evaluation.

Also test ordinary disjoint and variable-overlap squares using each bare rule
with a D_0 redex: in a distinct sibling of an outer context (disjoint), and
at each one of the rule's metavariable occurrences (variable). Nullary rules
with no metavariables have no variable case. Check both complete paths by
actual addressed rule application. For the 18 overlaps, reduce each immediate
branch by the deterministic preorder normalizer and compare the explicit final
terms and both full rule-word traces. This checks candidate O fillers, not the
unrestricted theorem that all equation paths are equal.

Raw category paths use the forest menu twice, the second time at a surviving
current leaf; compare sequential grafts against independent forest composition.
For this two-stage suite use the named six-vertex base term and the two-empty-
leaf loop term; choose each first-stage menu element and second-stage identity,
D_v on every single current slot, and U at every eligible empty identity slot.
This finite path family has one or two raw edges, with optional equation
elimination or movement paths supplied by normalization; arbitrary path lengths
are NOT exhaustively checked.

## 5. Full semantic hom and composition domain H

Use category C (grade 0), all three monoids, every G in Graphs(2), and every
source witness of arity k=0,1,2,3 on G, all its partitions, all composable C
arrow strings, and all source values. All targets have arity l=0,1,2,3, the
SAME full output component W=(G,f), all partitions/arrows/values. The source
and target catalogs are generated independently of possible refinements.

For each source, the redundant encoder enumerates every vector of local
arities (l_i) with total at most 3, every full flat local operation at its
specified component and arity, and their Cartesian product. Form its actual
composite target by flat_compose, and retain the entire entry tuple. Group
these tuples by target. For EVERY target in the independent target catalog,
compare that set with the principal run-length hom decoder; absent dictionary
keys mean the empty set, so nonexistent arrows are tested too. This covers ALL
arrows between all source/target witnesses in H, not a random subset.

Catalog counts for arity k at fixed G and endpoints a,b are
`k^r * (# nondecreasing length k+1 strings from a to b) * |M|`, with the
specified k=0 validity condition. Weak run-length vectors are counted by
`binom(l+k-1,k-1)` for k>0; at k=0 only l=0 is permitted. All actual counts and
number of empty/nonempty hom sets, arrows, parallel pairs, and distinct target
witnesses are retained in the certificate.

Composition domain Hcomp is the analogous exhaustive tuple-encoder domain
on Graphs(1), sources of arity≤2, intermediate arity≤2, final arity≤2, category
C and all monoids. Enumerate EVERY composable pair of such arrows. Compare
entrywise forest composition with the independent flat semantic substitution,
verify endpoint and hom membership, identities, and retained values. In
addition use the named six-vertex pair/triple below. No all-category or
all-degree claim is inferred from these bounds.

## 6. Interval factorization domain F and parameter maps

F contains every G in Graphs(2), every full C-arrow cut of arity n=3 or 4,
every ordered partition and value in each monoid, and every proper contiguous
interval of length 2 through n−1. The expected number of operation/interval
cases is the sum of the same flat catalog formula multiplied by
`sum_(q=2..n-1)(n-q+1)` (2 for n=3 and 5 for n=4).

The independent brute encoder enumerates every possible intermediate ordered
graph on at most |G| vertices with the required interval endpoints/arrow,
every inner partition matching the original interval's FULL profile, every
outer partition matching the quotient profile, and every pair of monoid values.
Keep exactly pairs whose actual flat substitution is the original full witness.
Compare the full pair set with the explicit forced-union/rank-block decoder
indexed by {(x,y):xy=m}. This tests actual inverse maps, not only fibre counts.
Include the six-vertex proper intervals too. Unary, full, empty and nullary
ranges are separately labelled boundary probes, not silently counted in F1's
proper-interval range.

Transport checks apply to every named X and six-vertex witness/path, not every
case of T or H: all 10 monotone object maps {0,1,2}→{0,1,2}; grade-preserving
and grade-collapsing functors C2→C2; relabeling 0,1,2 as 4,7,9 and its inverse;
all monoid homomorphisms among Z3,E2,One (enumerate every set-function and filter
by the complete tables, including maps that send a nonidentity value to 0);
and vertex-bound inclusions 2≤6. Verify object/entry/path maps and identities/
composites; compare mapped raw normal forms AFTER normalization, not falsely
as literal terms when a value is killed. Increasing rank relabelings are the
only graph-coordinate maps used. Arbitrary vertex permutations are excluded.

## 7. Named six-vertex and failure certificates

Use G on [6] with edges {0,5},{1,2},{2,3},{3,4}, blocks
({0},{1,2},{3,4},{5}), arrows (01,11,11,12), and all source/child M values.
The two middle nonempty components are literally identical. Test every
placement of the singleton split at occurrence 2 versus 3 (different targets),
and unary label tuples on those occurrences with equal total and unequal
entries (same target, genuinely unequal parallel arrows). Z3 contains tuples
(0,0) and (1,2); E2 contains distinct tuples with the same product. A separate
XOR/C2 scalar illustration may be reported only as an additional named control,
not as a silently added fourth exhaustive monoid domain.

Test actual decorated units, external empty identity leaves, nonidentity empty
grades, same-leaf/different-partition examples on the two-vertex edgeless graph,
and removal of edge {0,5} retaining induced blocks but changing the whole.
Output graph equality without output grade equality must not create arrows.

For missing MIn, use d_0 towers of heights h=0,...,8 on each of the source
components in the named example (including an empty loop). Count raw added
vertices and exhibit the exact normalization equation paths. The invariant's
unbounded theorem is P; these nine heights are finite illustration. Record
that pure equation/inverse/O and MOut steps preserve raw added-vertex counts,
while the MIn d_0 relation is exactly what changes the count from 1 to 0.

Object-only quotient and nonthinness controls retain two different original-
slot label tuples with equal total and prove they have the same source/target
but different serialized full tuple data. Missing-DL control and reverse-rotation
2-cycle are retained as inherited required regressions, not new contributions.

## 8. Actual source mutations and detection

After the unmutated author run passes, copy only the NEW finite sources into
separate mutation subdirectories and apply one documented textual source edit
per mutant. Preserve original source hashes; do not toggle an unrecorded oracle.
Run the SAME checker entrypoint in each copy, expecting a nonzero failure at
these named independent assertions:

1. `omit_MIn`: remove MIn from the local relation-certificate validator's
   admitted mixed schemas; a bare and a contextual MIn certificate must fail,
   and the d_0 spurious loop must remain distinguished by raw-added count.
2. `merge_repeated_occurrences`: change first-slot-only forest dispatch to
   dispatch by equal component type; the six-vertex repeated-component test
   must disagree with the independent positional flat substitution.
3. `erase_nullary_value`: change flat/term handling of decorated U to assign
   identity value; the independent root-address evaluation and MIn unit test
   must detect lost value.
4. `erase_entry_profile`: remove individual entry-profile/segmentation fields
   from the arrow equality key (retain only endpoint/composite or sorted values);
   the independently enumerated empty-slot/associative parallel-arrow test must
   detect the collision. The exact source edit will be recorded, not asserted.
5. `corrupt_MOut_residual`: dispatch the residual equation to the wrong original
   occurrence or reverse the order of the common graft forest; the addressed
   residual-step and independent tuple checker must fail.

These tests demonstrate mutation sensitivity of the finite implementation,
not independence of each mathematical relation from all others. A mutant that
survives requires diagnosis and a genuinely relevant new checker, review of
any changed domain, and honest failure logging; do not count it as detected.

## 9. Execution, counts, provenance, and frozen limits

Only Python standard library; deterministic enumeration; no random seeds.
No external service or oracle supplies equality. Cache memoization may avoid
recomputing a pure function at identical input, but every enumerated test case
and cache-independent execution count remains explicit. Do not replace actual
execution with an asserted symmetry multiplicity. Expected formula counts,
actual loop counts, source hashes, elapsed times and trace-file hashes are
written into `AuthorCertificate.json`; implementation defects and failed runs
remain in a failure log, not erased from chronology.

The reviewed target already contains inherited 18-shape P proof and general
mixed-coherence P work. Finite checks add validation at these exact bounds;
they do not shrink the uniform theorem, prove a simplicial object, settle F1–F3,
activate B4/C4/D/E/F/G/I, or confer novelty on a product by scalar labels.
A separate non-author reviewer must reconstruct/check the sources and rerun
from a fresh directory before final C acceptance. This author's agreement
between independently coded routines is redundancy, not independent authorship.
