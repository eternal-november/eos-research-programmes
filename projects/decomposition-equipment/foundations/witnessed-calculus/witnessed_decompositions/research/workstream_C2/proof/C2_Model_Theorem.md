# C2 relation-interface model: uniform theorem and explicit comparisons

Evidence P; author submission, not self-acceptance. Contract v0.1 SHA256
`47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
Cleared target SHA256 `b6711190a46b19205ef25f439105eaf1951137d90f5e55a595ea67daf172e2f4`.
The parent released this positive local C2 attempt after non-author target
review. Full C2 remains OPEN pending actual D2/E use. This document proves
neither D2's sharp map-class classification nor any equipment universal
property. The construction is standard relational infrastructure, not a
novelty claim. Finite computations are separate C evidence, not this proof.

## 1. Quantifiers, data and conventions

Fix an arbitrary set I and a family of finite sets X=(X_i)_{i in I}. Empty I
and empty X_i are permitted. Finiteness concerns each carrier, not the number
of paths or their lengths. The arguments below in fact work for arbitrary
sets with only finite paths; we claim at least the frozen finite-set family.

The component quiver has interfaces i in I and edges

    Rel_X(i,j) = P(X_i × X_j).

A component is the full triple c=(i,j,R), not just its relation's matrix or
cardinalities. Two distinct labels can have equal carriers without being
identified. A profile p is a finite typed ordered path

    i_0 --R_1--> i_1 --R_2--> ... --R_n--> i_n.

It retains every component occurrence and every intermediate interface label.
For n=0 the profile is the empty path at i_0, with equal outer labels.
A whole is independently supplied W in Rel_X(i_0,i_n).

Write R;S for left-to-right existential composition:

    (R;S)(x,z) iff there exists y in Y with R(x,y) and S(y,z).

The path composite C(p) is defined recursively by C(empty at i)=Delta_Xi
and C(p·R)=C(p);R. Equivalently, for n>=1,

    C(p)(x,z) iff there are x_k in X_ik (1<=k<n) such that
                    R_k(x_{k-1},x_k) for every 1<=k<=n,
                    with x_0=x and x_n=z.                     (1)

For n=0 it means x=z. This is not the empty relation: even the empty profile
may have many diagonal pairs if its interface is nonempty. When X_i is empty,
its diagonal is empty and all the same definitions still apply.

Define two DIFFERENT operation fibres:

    M_le(p;W) = {star | C(p) ⊆ W},
    M_eq(p;W) = {star | C(p) = W}.                             (2)

Each is empty or a singleton. The proposition in (2) is a validity condition,
not an independently stored tuple of intermediate values. We call a cell of
M_le exact when the second condition holds, nonexact otherwise. W is not
defined to be C(p). Its ambient output component is retained. Thus the model
legitimately contains nonreconstructive cells and permits different W for the
same p, while being thin in each fixed (p;W) fibre.

Distinguish three meanings of witness: a primitive symbol in an input
signature; a semantic cell of (2); and a realizing tuple for the existential
relation (1). The coordinate maps in section 4 act on the third of these.
They do not create or retain primitive labels in the thin cell fibre.

## 2. Relational lemmas, including empty paths

**R1 (units and associativity).** For every R:X→Y,
Delta_X;R=R=R;Delta_Y. For all composable R,S,T,
(R;S);T=R;(S;T). Composition is monotone in each argument.

Proof. For the left unit, the existential condition is
there exists x' with x=x' and R(x',y), equivalent to R(x,y); take x'=x
for the reverse implication. The right unit is symmetric. Associativity at
(x,w) expands on the left to

    exists z, (exists y, R(x,y) and S(y,z)) and T(z,w),

and on the right to

    exists y, R(x,y) and (exists z, S(y,z) and T(z,w)).

Both are equivalent to the same pair (y,z) satisfying all three conditions.
These are explicit mutually inverse rearrangements of existential witnesses.
Monotonicity sends a realizing y to that same y with each relation-membership
proof replaced by the inclusion proof. No set is required nonempty. QED.

**R2 (path concatenation).** For any typed paths p:i→j, q:j→k,
C(pq)=C(p);C(q), including either empty path.

Proof. Induct on q. If q is empty, the equation is the right-unit law. If
q=q'·S, recursive evaluation and induction give
C(pq)=C(pq');S=(C(p);C(q'));S=C(p);(C(q');S). QED.
This also proves formula (1) by induction, with n=1 reducing to R by a unit.

**R3 (flattening and monotonicity at independent occurrences).** Let p have
n slots, and for EACH slot k let q_k be any typed path with the same endpoints
as R_k. Empty q_k are allowed only when those endpoint labels are equal.
Then

    C(q_1...q_n) = C([C(q_1),...,C(q_n)]).                    (3)

If C(q_k)⊆R_k for every k, then the left side of (3) is contained in C(p).
If each inclusion is equality, so is the resulting inclusion.

Proof. Iterate R2 and use R1. Equivalently, let m_k be the length of q_k and
s_k=m_1+...+m_k. A realizing tuple of the flattened path restricts to each
interval [s_(k-1),s_k]; the values at s_k realize the outer path of composites.
Conversely, an outer tuple and realizing tuples for its n inner composites
concatenate, dropping the duplicate common endpoint at each join. If m_k=0,
the inner condition says the two adjoining values are equal, so inserting or
removing this empty interval is legitimate. Repeated offsets caused by empty
blocks do not supply new independent values. With n=0 both sides are the
same diagonal and there is no family to choose. To assemble finitely many
existential tuples in the converse, induct on n and eliminate the finitely
many existentials into the existential conclusion; no infinite choice is
used. Monotonicity replaces each C(q_k) edge condition by R_k on the SAME
outer tuple. Distinct positions stay distinct even if R_k=R_l. QED.

## 3. Actual calculus structure and exact subcalculus

**C1 (uniform containment calculus).** For every X, (2) admits occurrence-wise
substitution, both units, and associativity, with the entire typed profile
retained. Its full-arity extension includes exactly the stated loop nullaries.

Define the identity operation on component c=(i,j,R) as the singleton-profile
cell ([R];R); its validity is R1. Given a in M_le(p;W) and an independent
b_k in M_le(q_k;R_k) at every occurrence, define

    a[b_1,...,b_n] = the unique cell of M_le(q_1...q_n;W).      (4)

It EXISTS: R3 gives C(q_1...q_n)⊆C(p)⊆W. Thus (4) is not a partial or assumed
law. Its profile is the ordered concatenation, and its whole remains W.

Right unit replaces every edge by the singleton path containing that same
edge. The expanded path is p, so (4) and a belong to the same singleton fibre
and are equal. Left unit substitutes an arbitrary cell into the sole slot of
[R]; the resulting profile is exactly that cell's profile and the whole is R,
so the cells agree. This argument applies to a nullary replacement: the
singleton identity operation and a zero-input cell remain different operations.

For associativity, take an outer path p, replacement paths q_k, and a third
family r_(k,l) at the ordered occurrences l of every q_k. Both substitution
orders have the same output W and flattened profile

    q_1[r_(1,*)] ... q_n[r_(n,*)].

The position correspondence is the ordered bijection
((k,l),t) ↔ (k,(l,t)); it neither permutes nor merges positions. At the exact
public A API level the profile equality is `Path.expand_assoc`, with the
third-stage family transported using `Path.expandFamily` (see section 6).
After transport along that equality both outcomes lie in the same singleton
fibre, hence are equal. This is equality of OPERATIONS: a total operation
stores only its profile and the validity proof, in addition to the fixed
output. It is not merely equality of their underlying composite relations.
All validity proofs were supplied by R3 before using thinness. Empty outer
and inner families are included; they have no positions to omit. QED.

**C2 (exact subcalculus).** The same definitions restricted to M_eq form a
calculus, and forgetting exactness gives a strict structure-preserving
inclusion M_eq→M_le on this SAME quiver. The inclusion is injective in every
fibre. It need not be proper for a degenerate X.

Proof. Identities are exact by R1. If a and all b_k are exact, R3 says the
flattened composite equals C(p)=W. The same profile/whole/thinness argument
proves all laws; the inclusion sends star to star, so preserves identities
and substitution literally. Properness on nondegenerate families is supplied
by the strict-containment example in section 7, not asserted universally. QED.

A nullary M_le cell at i with whole W is valid iff Delta_Xi⊆W; an exact one
requires W=Delta_Xi. There is no nullary at unequal labels, even if their
carrier sets happen to coincide. A nullary cell's existence does NOT declare
an arbitrary loop component to be a unit. On an empty carrier the only loop
relation is the empty diagonal, so the distinction happens to collapse there.

## 4. Restrictions and the actual comparison maps

For every f:A'→A, g:B'→B define

    Res_(f,g)(R)(a',b') iff R(f(a'),g(b')).                  (5)

This is a relation A'→B', contravariant in both chosen boundary maps.
It sends an inclusion R⊆S to the inclusion with unchanged element pair and
membership proof passed through R⊆S. It is monotone, preserves relation
equality, and satisfies

    Res_(id,id) R = R,
    Res_(f',g') (Res_(f,g) R) = Res_(f∘f', g∘g') R.         (6)

Indeed both sides of the second equation at (a'',b'') say
R(f(f'(a'')),g(g'(b''))). Relation extensionality proves the literal equation.
Consequently any length of iterated boundary change has associative, unital
coherence, not a separately selected comparison.

**R4 (lax composition comparison, every arity).** Given p=(R_1,...,R_n) and
f_k:X'_k→X_(i_k) for each path vertex, set R'_k=Res_(f_(k-1),f_k)R_k.
For n=0 require a SINGLE X'_0 and map f_0 at both ends. There is an inclusion

    lambda_(p,f): C(R'_1,...,R'_n) ⊆ Res_(f_0,f_n) C(p).    (7)

For n>=1 and fixed endpoints a' and z', its underlying map on realizing tuples is

    (x'_1,...,x'_(n-1)) ↦ (f_1(x'_1),...,f_(n-1)(x'_(n-1))). (8)

Each edge condition on the source is by (5) the required edge condition on
the target, so (8) is well-defined. Composing tuple maps agrees with applying
composite boundary functions coordinatewise, and identity tuple maps are
identities. The map may be many-to-one, miss target tuples, or both. Passing
to existence yields inclusion (7); inclusion of relations is not a claim of
bijection between their realization sets. For n=1 there are no interior
coordinates and both sides of (7) are equal by the unary unit law R1.

For n=0 the comparison is instead

    Delta_A' ⊆ {(x',z') | f_0(x')=f_0(z')} = ker(f_0).        (9)

It sends an equality x'=z' to the equality of its f_0-images. This case cannot
be obtained by interpreting an empty conjunction of internal-surjectivity
conditions as an exactness guarantee. QED.

**C3 (restriction of containment cells).** Every containment cell (p;W) yields
one with profile p'=(R'_1,...,R'_n) and whole W'=Res_(f_0,f_n)W.

Proof. Compose (7) with the inclusion Res C(p)⊆Res W obtained from its validity
condition by (5). This explicitly defines the fibre map star↦star, from the
original valid fibre to the new valid fibre. At nullary p use (9); the same
argument applies without supposing f_0 injective. This is a map between the
specified fibres; it is not falsely an identity-base `Calc.Hom` when the
component quiver changes. The identity and composite restriction laws follow
from (6) on all profile edges and whole, and uniqueness of a cell in its fibre.
The source fibre may be empty; its unique empty-domain map causes no problem.
QED.

**R5 (sufficient exact-comparison hypotheses, with separate nullary case).**
For n>=1, (7) is equality whenever ALL INTERNAL maps f_k, 1<=k<n, are
surjective. The endpoint maps are arbitrary, including noninjective and
non-surjective maps. For n=0, (9) is equality iff f_0 is injective.

Proof for positive arity. A pair in Res C(p) supplies an unprimed realizing
tuple with endpoints f_0(a'),f_n(z'). Choose a preimage of each internal
coordinate using its surjectivity. There are finitely many coordinates, so
finite existential assembly gives a primed tuple. Each edge condition is
exactly (5); hence the pair lies in C(p'). The forward direction is R4. For
n=1 the assertion requires no choices and is already equality. Empty carrier
cases need no extra assumptions: if an unprimed tuple does not exist, the
reverse implication is vacuous; if it exists, the stated surjections produce
its preimages. No converse surjectivity claim is made here.

For n=0, equality of diagonal and kernel says precisely that f_0(x')=f_0(z')
implies x'=z' for all x',z', which is the definition of injectivity. This
includes empty A', on which the condition holds. QED.

An exact source cell remains exact under the hypotheses in R5, since
W=C(p), and (7) then gives C(p')=Res W. Without those hypotheses an exact
cell can become a nonexact but still valid containment cell. Nonexactness is
not necessarily preserved either: restriction can discard its extra pairs.
For example, restricting section 7's W along inclusions A'={0}→A and
C'={0}→C and the identity B→B leaves exactly {(0,0)} as both the whole
and the composite, turning that nonexact cell into an exact one.
Every bijective global interface-map family therefore acts on the entire
exact calculus, including nullaries. Surjectivity alone is NOT enough for an
all-arity exact action. These are C2 comparisons and sufficient hypotheses,
not D2's promised sharp universal criterion or E's full theory.

## 5. Restriction and substitution, with incidence compatibility

There are two useful precise formulations; neither identifies a composite
of pulled-back pieces with a pulled-back composite.

### 5.1 Fixed interface-index family (global base-changing map)

Fix the SAME label set I and another family X'_i together with maps
f_i:X'_i→X_i for all i. It induces a component map

    B_f:(i,j,R) ↦ (i,j,Res_(f_i,f_j)R)

and a map of typed paths by applying it to every edge occurrence, retaining
labels/order. It also maps every slot identically in position, with its
component changed by B_f. The resulting operation map sends (p;W) to
(B_f(p);B_f(W)) using C3.

It preserves identities because B_f([R])=[B_f(R)] and that cell is the
identity. For every occurrence-indexed substitution family,

    B_f(a[b_k]) = B_f(a)[B_f(b_k)].                         (10)

Both sides have whole B_f(W) and profile obtained by mapping every edge in
the ordered concatenation q_1...q_n. Mapping edges commutes with concatenating
lists/typed paths, so those profiles coincide. Both cells exist by C1/C3;
thinness in their common fibre gives (10). This proof uses neither equality
in (7) nor exactness preservation. In particular (10) remains true when
(7) is strict. The result is a strict BASE-CHANGING calculus morphism with
specified component map B_f, not a `Calc.Hom` over one fixed relation quiver.
Equations (6) on components induce identity/composition coherence of these
base-changing maps. If all f_i are bijections, R5 additionally makes this
an all-arity exact-calculus map.

### 5.2 Maps chosen locally on a substitution diagram

A finite diagram consists of outer path vertices and each inner path's
vertices, with each child's endpoints identified with its parent slot's
endpoints; equal labels alone do NOT require distinct occurrences to be
identified. A map assignment is incidence-compatible if it supplies a primed
interface set (and label in a chosen primed index set) and map to the original
carrier at each vertex class, and uses that SAME primed set and SAME map at
all incidences of the class. An empty inner path identifies its two endpoint
vertices, so their primed sets and maps must coincide. Nested substitutions
impose the transitive closure of these identifications.

Restrict each relation and each whole at its own two boundary maps. C3 makes
every restricted cell valid, including empty children. Each restricted child's
whole is literally the corresponding restricted outer component by incidence
compatibility. Thus the restricted cells can actually be substituted. The two
orders (restrict the flattened cell; or restrict every cell and substitute)
retain the same endpoint whole and the same ordered list of restricted leaves,
so agree by thinness, exactly as (10). For any finite tree the statement follows
by induction on vertices, with the same final leaf occurrence bijection on
both sides. There is no hidden bound on tree depth. Iterated interface changes
respect the incidence classes and obey (6), hence the comparisons are coherent.
This is compatibility of CONTAINMENT CELLS, not a theorem that their exactness
markings survive arbitrary internal restriction.

If a loop slot has a nullary child but its two primed boundary sets/maps were
chosen independently, the restricted child may have unequal endpoints or
incompatible endpoint maps; that is not a well-typed restriction diagram.
Rejecting it is necessary typing, not deletion of a difficult mathematical case.

## 6. Two-sided public A API bridge and free interpretation

This model is different from the earlier A2 auxiliary model whose operations
are multirelations from products of component-value carriers. Here the
COMPONENTS themselves are interface relations, and operation fibres are thin
containment/equality predicates. No renaming of that older model supplies C2.

Use the existing public `WitnessedDecompositions` definitions with V=I and
quiver edges `X i → X j → Prop` (equivalently subsets of X_i×X_j). Predicate
extensionality identifies the two component descriptions in both directions:
R maps to its membership predicate; a predicate maps to its extension.
`Component I` is exactly the triple (i,j,R). An abstract ordered typed path
is sent to `.nil` for zero edges and `.cons` recursively for a final edge.
Conversely read those constructors to obtain the label-and-edge sequence.
The two maps are inverse by induction on length/constructors. Intermediate
labels are retained by the dependent constructor, not reconstructed merely
from carrier cardinalities. `Path.Slot` gives one slot per constructor,
canonically ordered from 1 to n; for `.cons p e` the old slots are `.inl`
and the new last slot is `.inr ()`. This is an order-preserving bijection,
proved by the same induction, including the empty case.

For a full component c let

    Op_le(c) = {(p,h) | p:Path(c.source,c.target), h:C(p)⊆c.edge},
    profile(p,h)=p.

The validity proof is in Prop, so this can be written as the subtype
`{p // ...}`; alternatively it is a totalization of the empty/singleton Type
fibres (2). These are explicitly equivalent by `(p,h) ↔ (p,star_h)`, with
inverse forgetting the proof wrapper; proofs do not carry extra data.
Define Op_eq with equality instead. The public `CalcData` fields are:

* `identity c = (c.edge.toPath, R1)`;
* `profile_identity c = rfl`;
* `subst (p,h) f = (Path.expand p (fun k => (f k).profile), validity from R3+h)`;
* `profile_subst = rfl`, because `Collection.familyProfile` is that expansion.

Here `f : Collection.Family p` is exactly an independent operation at each
`Path.componentAt p k`; in particular its output relation is R_k. The
`Path.expand` recursion concatenates those profiles in increasing slot order,
so it is precisely the concatenation in (4).

To fill `Calc.subst_identity`, use `Path.expand_edges` for the profiles and
proof irrelevance for the validity fields (`Subtype.ext`). To fill
`Calc.identity_subst`, use `Collection.singletonFamily_profile` (the public
singleton expansion/left-unit equation) after eliminating `profile_identity`.
For `Calc.subst_assoc`, its third-stage family initially has domain the actual
profile of `subst a f`. `CalcData.innerFamily` transports it along
`profile_subst` and applies `Path.expandFamily`; thus it supplies exactly the
slot (k,l) family in C1, with any component equality transport included.
`CalcData.composeAt_profile` / `Path.expand_assoc` give equality of the two
flattened typed profiles. The validity subtypes are then equal by `Subtype.ext`.
These are proved fields, not assumptions that the desired target is a calculus.
The same argument constructs the exact Calc, because its validity step uses
the equality case of R3.

The prescribed public operation fibre is

    Calc.Operation c p = {a:Op(c) // profile(a)=p}.

The map from it to (2) transports a's validity along its profile equality and
returns star; the inverse sends star with its validity proof to
`((p,validity),rfl)`. Eliminating the profile equality and using proof
irrelevance proves both composites are identities. At the collection level
these are `Collection.fiberTotalizeEquiv` and its inverse after the subtype /
empty-singleton identification. They preserve identities and every substitution
by the definitions above and equality elimination. Conversely, starting from
any public Calc and taking its prescribed fibres then totalizing sends
`(p,(a,h))` to a, with inverse `a↦(profile(a),(a,rfl))`; this is the existing
`Collection.totalizeFiberEquiv`. Those maps preserve the structure by the public
`Calc.substitute` definition. Thus the fibre and total formulations are truly
two-sided, not just a semantics-preserving encoding in one direction.

For same-base maps, a profilewise map F of fibres preserving identity and
substitution totalizes to `(p,a)↦(p,F(a))`, providing `Collection.Hom.profile_map`
and `Calc.Hom.map_identity/map_subst`. Conversely a public strict Hom restricts
via `Calc.Hom.onOperation`. Eliminating profile equalities shows these two
constructions are inverse and preserve identity/composition. In particular
M_eq→M_le is a genuine same-base strict public Hom. B_f of section 5 changes
component quiver and is intentionally NOT assigned that same-base type.

Finally, for ANY signature S on this relation quiver, an admissible primitive
assignment is a cell alpha_g in the public fibre
`(containmentCalc X).Operation (S.result g) (S.input g)` for every generator,
equivalently in M_le(S.input g; S.output g) with whole relation S.output g,
i.e. a proof that the composite of its exact declared profile is contained in
its exact declared output relation. These assignments define a signature map
into the underlying collection, retaining each full profile and whole. Applying
the existing A2 free extension yields a unique strict calculus morphism
F(S)→M_le extending alpha; similarly for all-exact assignments and M_eq.
The extension sends a leaf to the singleton identity and a node to (4) applied
to its recursively evaluated children. A direct tree induction gives its
operation: the declared root whole, its actual ordered frontier, and the
containment proof propagated by R3. Grafting compatibility is (4)/C1 with the
public occurrence bijections. This is a target Calc for A2, not an arbitrary
leaf-valued fold used in place of that universal property.

Distinct primitive labels with identical profile and whole necessarily have
the same image if both are admissible, and differently grouped trees with the
same root whole and complete frontier also have the same image. This shows
nonfaithfulness of this interpretation on those syntax examples. It does NOT
assert that the raw trees are equal, that their generators are identical, or
that an undeclared equation is derivable. Different frontiers (even if their
composites agree) lie in different operation fibres; different wholes lie in
different output component fibres. No quotient by semantic equality is defined
or used here. The named certificates test those distinctions explicitly.

## 7. Named nondegenerate and boundary certificates

Here are explicit data, independently checked in the finite suite. Let
A={0,1}, B={0,1,2}, C={0,1}, with three DISTINCT labels, and define

    R:A→B = {(0,0),(1,2)},
    S:B→C = {(0,0),(2,1)},
    T=R;S = {(0,0),(1,1)},
    W=T ∪ {(0,1)}.

The composite is nonempty. The cell (R,S;T) is exact, whereas (R,S;W)
is valid and strictly nonexact. Let A'=A, C'=C with identity maps and
B'={0,1} mapped to B by g(0)=0, g(1)=1. Then

    R'={(0,0)}, S'={(0,0)}, R';S'={(0,0)},
    Res_(id,id)(R;S)=T.

The tuple through 2 that realized (1,1) has been removed, while the tuple
through 0 survives. Thus (7) is strict. Pulling the original exact cell to
whole T still gives a valid containment cell, but it is no longer exact.
Pulling the strict whole W also remains valid. This is not just an empty-
composite or singleton-interface negative control.

For a positive noninjective intermediate example use B''={0,1,2,3} and
s:B''→B with values (0,1,2,2). It is onto and many-to-one; composition of the
restricted R,S is T. The pair (1,1) has two primed realizing tuples, 2 and 3,
mapping to the same unprimed tuple 2. This illustrates equality of endpoint
relations without a bijection of realization witnesses. Arbitrary endpoint
maps may be used too; R5 requires no endpoint injectivity.

For the nullary exception use f:{0,1}→{0} constant. The original exact
nullary whole is Delta_{ {0} }; its pullback is the full four-pair relation on
{0,1}, whereas the primed empty-path composite is the two-pair diagonal.
The restriction is a nonexact containment cell. Although f is surjective,
there are no internal maps whose surjectivity could repair this failure.
For an empty source interface the diagonal/kernel are both empty; no false
converse about nonempty endpoint sets is inferred.

The finite suite additionally retains a mixed four-leaf path A→B→B→B→C
with repeated identical loop components and DIFFERENT valid occurrence
substitutions, competing groupings, and parallel primitive symbols. Their
exact tables, tree encodings and mutation witnesses are part of the executable
certificate rather than a presumed consequence of these three named sets.

## 8. Proof and completion boundaries

All uniform claims in sections 1–6 are P, using finite path induction,
existential witness manipulation, ordinary equality transport, and function /
predicate extensionality. No infinitary choice, interface inhabitance,
reconstruction, equipment universality or decidability assumption is used.
If Lean represents Prop-valued relations literally, predicate equality may
invoke `propext`; the actual optional L axiom report, not this prose, determines
its checked dependency closure. No external Python computation is a kernel proof.

The finite checks establish only their frozen enumerated domains. They must
independently test and falsify mutations of the implementation; their passing
counts do not upgrade P to L. The existing A2 generic free theorem and A1
occurrence API are imported infrastructure, with baseline sources preserved.
The published relational/equipment neighborhood is acknowledged separately;
none of these elementary relation laws is counted as a new major contribution.

This local model and its tests prepare D2/E inputs, but actual integration into
those workstreams is NOT performed. Full C2 stays OPEN, as do all D/E and C3
obligations not separately accepted. Independent mathematical and reproducibility
review, followed by parent acceptance of this local checkpoint, remain required.
