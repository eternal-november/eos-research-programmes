# D2 — Sharp finite relational restriction and retained-witness transport

**Result first.** For arbitrary finite maps `f:A'→A`, `g:B'→B`, and
`h:C'→C`, composing the two restricted relations is always contained in
restricting their composite. For **every** choice of relations `R:A→B` and
`S:B→C`, this containment is equality exactly when

    A' is empty, or C' is empty, or g is surjective.        (D2.0)

For a particular pair `R,S` the condition is weaker: every feasible pair of
lifted exterior endpoints needs **some** intermediate witness in `im(g)`.
It does not need a lift of every old witness, or a unique lift. The latter
conditions govern actual finite-span comparison maps, not relational
equality. Nullaries are separate: the diagonal comparison is exact exactly
when its interface map is injective.

The theorem covers all finite map sizes, all finite path lengths, and all
finite incidence-compatible substitution/cut trees. It includes a sharp
limitation: on C2's complete relation quiver, a global map family preserves
**all** exact operations, including nullaries, iff all primed carriers are
empty or every map is bijective. Noninvertible maps nevertheless give
coherent containment transport, exact positive-arity transport under
surjectivity, and nontrivial support-restricted exact families.

**Evidence and reuse.** This is the mathematical P source for original D2,
contract lines 382–396, dated 31 October 2026. Finite executable checks and
independent audit are separate evidence. The actual-span fibre formula and
its retained-diagram/all-tree extension are already proved in CUT §10 and
I4 §§2–3.4. Section 6 explicitly imports and specializes them; it does not
claim to discover that result again. The Rel/Span mechanisms are standard
relational restriction and Beck–Chevalley-type comparison infrastructure,
not a novelty claim. D3 and global completion-contract acceptance are not
asserted here.

## 1. Declared map class, objects, and the four levels of comparison

All carrier sets in this document are finite, including possibly empty sets.
All boundary maps are total functions. A map to an empty codomain therefore
has empty domain; arbitrary six cardinalities without such a map are not an
input. Component labels, path occurrences, and all intermediate interface
positions remain actual data. Distinct occurrences with equal labels are
not identified. Relations compose left to right:

    (R;S)(a,c) iff ∃b∈B, R(a,b) and S(b,c).

Restriction is ordinary inverse image of the endpoint product map:

    (f,g)^*R(a',b') iff R(f(a'),g(b')).                    (1.1)

These are C2's exact conventions. It is important to distinguish:

1. **Relational inclusion:** a 2-cell in a hom-poset, proved by sending an
   existential witness to its image. It need not be equality.
2. **Relational equality:** equality of subsets of `A'×C'`, equivalently an
   invertible inclusion 2-cell in that poset. It remembers only existence at
   each endpoint pair, not the individual intermediate realizations.
3. **Actual span comparison map:** a specific endpoint-preserving function
   between actual witness apex sets, retaining intermediate realizations.
4. **Span isomorphism:** the specified comparison has a two-sided inverse,
   equivalently its apex function is bijective. This need not be literal
   equality of the two presented apex sets. Equal apex cardinalities alone
   do not make the specified comparison invertible.

The identity of a relation component, the nullary diagonal relation, and a
chosen realizing tuple are also different objects. We use C2's thin
operation fibres `M_le(p;W)={* | C(p)⊆W}` and
`M_eq(p;W)={* | C(p)=W}` only when explicitly discussing that model.
Their validity proofs do not retain actual existential witness tuples.

## 2. Binary comparison and both sharp equality criteria

Put `R'=(f,g)^*R` and `S'=(g,h)^*S`. There is always an inclusion

    λ_(R,S;f,g,h): R';S' ⊆ (f,h)^*(R;S).                 (2.1)

Indeed a source realization `b'` is sent to the target realization `g(b')`.
This proves the inclusion without any injectivity or surjectivity hypothesis.
At fixed exterior lifts define the finite old witness set

    W_(a',c') = {b∈B | R(f(a'),b) and S(b,h(c'))}.          (2.2)

### Theorem 2.1 — relation-specific exactness

For fixed `f,g,h,R,S`, (2.1) is equality iff

    for every a'∈A', c'∈C',
    W_(a',c')≠∅ implies W_(a',c')∩im(g)≠∅.               (2.3)

Equivalently, at each lifted exterior pair, the full old witness set and
its part in `im(g)` have the same emptiness status. This is a finite support
criterion calculated from the relation and map tables, not a hypothesis
that the comparison is already invertible.

**Proof.** Membership in the right side is `W_(a',c')≠∅`. Membership in the
left side says there is a `b'` whose image lies in this set, equivalently
`W_(a',c')∩im(g)≠∅`. Relation extensionality proves the equivalence. It also
shows explicitly that one liftable old witness may cover an endpoint pair
whose other old witnesses have no lift. QED.

The image criterion has a standard relational factorization. Let `Γ_f`
be the graph relation of `f:A'→A`, and `Γ_g^op` its converse. Then

    (f,g)^*R = Γ_f ; R ; Γ_g^op,
    Γ_g^op ; Γ_g = Δ_im(g) ⊆ Δ_B.                        (2.4)

Thus (2.1) inserts the inclusion of the diagonal on `im(g)` into the diagonal
on all of `B`. This explains both the direction and the existential nature
of the comparison; it is not a new identity specific to this project.

### Theorem 2.2 — uniform binary exactness for the full finite-map class

For fixed finite maps `f,g,h`, the following are equivalent:

* (2.1) is equality for every relation `R⊆A×B` and `S⊆B×C`;
* (D2.0) holds.

**Proof.** If either primed exterior carrier is empty, both relations are
subsets of the empty product, hence empty. If `g` is surjective, every member
of a nonempty set (2.2) lies in `im(g)`, so Theorem 2.1 gives equality.

Conversely suppose `A',C'` are nonempty and `g` is not surjective. Choose
`a'∈A'`, `c'∈C'`, and `b∈B\im(g)`. Let

    R={(f(a'),b)},       S={(b,h(c'))}.

The pair `(a',c')` belongs to the restricted composite. Every realization
of the restricted pair would have image `b`, which is impossible. Hence it
does not belong to the composite of restrictions. This disproves the
universal claim. Repeated exterior images of `f` or `h` cause no difficulty:
the displayed pair already witnesses strictness. QED.

When `B=∅`, the existing function `g:B'→B` forces `B'=∅` and is surjective;
there is no missing extra exception. Empty **old** exterior carriers force
empty primed ones and are already covered. Empty `B'` with nonempty `B`
is an honest nonsurjective case and fails whenever both primed exteriors
are nonempty. No assumption that `f` or `h` is surjective or injective is
needed in the nondegenerate theorem.

## 3. Positive paths and nullaries, with complete empty-case classification

Let `n≥1`, let `f_i:X'_i→X_i` for `0≤i≤n`, and let
`R_i⊆X_(i-1)×X_i` for `1≤i≤n`. Write `p=(R_1,...,R_n)`,
`R'_i=(f_(i-1),f_i)^*R_i`, and `C(p)=R_1;...;R_n`.
For fixed lifted endpoints `x'_0,x'_n`, retain the full old realization set

    W_p(x'_0,x'_n) = {(x_1,...,x_(n-1)) |
       R_i(x_(i-1),x_i) for every i,
       x_0=f_0(x'_0), x_n=f_n(x'_n)}.                    (3.1)

For `n=1` this is either empty or the singleton empty tuple. There is a map
on realizations and the resulting relation inclusion

    (x'_1,...,x'_(n-1)) ↦ (f_1x'_1,...,f_(n-1)x'_(n-1)),
    λ_(p,f): C(R'_1,...,R'_n) ⊆ (f_0,f_n)^*C(p).         (3.2)

### Theorem 3.1 — exact positive-path criteria

For a particular path, (3.2) is equality iff for each lifted exterior pair

    W_p≠∅ implies
    W_p ∩ (im(f_1)×...×im(f_(n-1))) ≠∅.                  (3.3)

For `n=1` equality always holds. For `n≥2`, equality holds for **every**
choice of the `R_i` iff at least one of the following holds:

    X'_0=∅;
    X'_n=∅;
    some OLD internal carrier X_i=∅ (0<i<n);
    every internal f_i is surjective (0<i<n).            (3.4)

**Proof.** The right side of (3.2) asserts existence of a tuple in (3.1).
The left asserts existence of such a tuple all of whose coordinates have
preimages. Finitely many preimages can be assembled by finite induction;
no infinite choice principle is used. This proves (3.3) and the unary case.

The first two cases of (3.4) make the exterior product empty. An empty old
internal carrier makes every positive path realization impossible; its
primed carrier is empty too. In the last case every old tuple lifts.
Conversely suppose both primed exteriors and all old internal carriers are
nonempty, and choose a missing value `x_j∉im(f_j)` at one nonsurjective
internal map. Choose arbitrary values at the other old internal carriers
and primed exterior points. Define each `R_i` to contain exactly the
consecutive pair in this chosen path. There is exactly one old internal
tuple at the selected lifted exteriors and it cannot lift because of its
`j`th coordinate. Equality fails. QED.

The old-empty-internal exception is genuinely needed at length three and
above: an unrelated nonsurjective internal map can be invisible because a
different old internal carrier is empty. At binary length it reduces to
the already-surjective empty function `∅→∅`.

### Theorem 3.2 — the separate nullary criterion

A zero-length path at `X` has composite `Δ_X`. It has one boundary interface,
not two independently chosen charts. For `f:X'→X` its comparison is

    Δ_X' ⊆ (f,f)^*Δ_X = ker(f).                          (3.5)

This is equality iff `f` is injective, including `X'=∅`.

**Proof.** The inclusion sends `x'=y'` to `f(x')=f(y')`. Its reverse says
precisely that equal images imply equal elements. QED.

A nullary comparison is not the positive-path formula with an empty product
of internal conditions. The target may contain off-diagonal endpoint pairs.
An operation identity on a component is unary and is always preserved;
this does not imply preservation of nullary interface units.

## 4. Arbitrary-tree compatibility, with the tested data retained

### 4.1 Incidence-compatible input diagrams

Use exactly C2 §5.2's convention. A finite ordered substitution/cut tree
retains every vertex operation, every whole relation, every intermediate
component occurrence, and its complete ordered child profile. A child's
whole is its parent's corresponding input component. Endpoint occurrences
identified by these incidences use the **same** primed set and boundary map.
A nullary path identifies its two endpoint incidences, so uses a single map.
Equal interface labels alone do not identify otherwise independent
occurrences. No comparison is claimed for an ill-typed chart assignment.

At each nonnullary vertex apply Theorem 3.1 to its actual child relations.
These children can be previously supplied whole relations or actual subtree
composites. They are not silently replaced by unrelated primitive leaves.
At every nullary vertex apply Theorem 3.2. The finite tests retain the old
sets (3.1) at every named node, not merely the feasible values at the root.

### Theorem 4.1 — coherent containment transport and exact retained trees

Every such diagram in C2's containment calculus restricts to a well-typed
containment diagram. Restriction commutes with arbitrary finite occurrence
substitution, with identity and iterated boundary change. If every old named
cell is exact, every corresponding restricted named cell is exact iff the
criterion (3.3), or (3.5) at a nullary, passes at **each** named cell.
When it passes, all contractions of this exact tree and its evaluated
flattening are exact and commute with restriction.

If all regroupings of a retained finite path are claimed, impose the same
criterion for every relevant contiguous composite run and every permitted
nullary-unit position. Then it gives coherent exact transport for all its
finite ordered cut trees, arbitrary finite contractions and permitted
insertions of units. This is an unbounded finite-tree statement, not an
adjacent-primitive-pair test.

**Proof.** For a cell `C(p)⊆W`, compose (3.2) with the inverse-image
inclusion `(f_0,f_n)^*C(p)⊆(f_0,f_n)^*W`; use (3.5) at nullary cells.
Incidence compatibility makes every image child's whole literally the
matching image parent input, so substitution exists. Restricting first or
substituting first gives the same restricted whole and the same ordered
list of restricted external leaf components. C2's R3 and §5 prove validity
of both resulting cells; thinness in their common fibre then gives equality.
This argument is an induction on the actual number of vertices and keeps
the original-slot concatenation bijections, including empty child blocks.
It neither deletes repeated occurrences nor recovers hidden witness labels
from a root equality.

For an exact old named cell `W=C(p)`, exactness of its image is exactly
(3.2) being equality, so Theorems 3.1–3.2 give necessity and sufficiency
**vertex by vertex**. Composition of exact C2 cells is exact by C2 R3;
therefore contraction and flattening are exact. Conversely a passing root
alone gives no reason for all the other named cells to be exact.

For witness-map coherence on positive paths, both ways of regrouping a
retained full realizing tuple apply each `f_i` to its same named coordinate.
Tuple flattening only removes duplicate boundary entries; it does not change
or choose an internal value. Thus the maps commute with every binary
grafting/contraction, and induction proves every finite tree diagram.
Nullary branches use the equality of their repeated endpoint coordinates;
the same coordinate formula proves their inclusion squares. For two
successive compatible boundary changes `f_i` and `k_i`, both composites send
`x''_i` to `f_i(k_i(x''_i))`. Inverse image also satisfies

    (k_(i-1),k_i)^*((f_(i-1),f_i)^*R_i)
      = (f_(i-1)k_(i-1), f_i k_i)^*R_i.                  (4.1)

Hence identities and all finite-composite coherence follow as actual
function/relation equalities. If both successive changes satisfy the exact
criteria at their corresponding diagrams, their composite does too, by
substitution of these equalities. No inverse is claimed for a general
interface map.

Finally every node of every ordered tree grouping one fixed path is a
contiguous run. Testing every requested run supplies the vertex condition
for every grouping. Unit insertions additionally use the named nullary
maps, independently of the positive-run conditions. This proves precisely
the stated all-tree scope. QED.

This does not assert an inverse on primitive symbols or arbitrary presented
witnesses: C2's operations are thin. Transport in a separately presented
non-thin calculus still needs maps on its primitive witnesses and a check
of its equations, as D1 specifies. Bijective boundary changes recover D1
§9's relation transport after reversing the direction of the chosen
bijections. No arbitrary noninvertible primitive action is manufactured here.

### 4.2 Why primitive adjacent-pair tests are insufficient

Use CUT §10/I4's existing control. Let `X_0=X_3={*}` and
`X_1=X_2={0,1}`. Each primitive relation has the one pair along the old path

    * → 1 → 1 → *.

Let each internal primed set be a singleton mapped to `0`; leave exteriors
unchanged. Each length-two composite, after restriction of its exterior
internal endpoint to `0`, is empty, so both adjacent-pair comparisons are
empty-to-empty. The full length-three old composite contains `(*,*)`,
whereas all three individually restricted primitive relations are empty.
The whole-path comparison is strict. At the next tree node the actual
composite child relation detects this failure. This is a reused all-tree
scope warning, not a new obstruction discovered for D2.

## 5. Positive families and a sharp all-operation limitation

### 5.1 Noninvertible positive families

* For every positive length `n`, any surjections at all internal interfaces
  and arbitrary endpoint maps give equality for every relation path.
  These maps may identify arbitrarily many internal elements. They preserve
  every positive-arity regrouping of that path, but do **not** automatically
  preserve nullaries at a noninjective interface.
* For arbitrary maps, exactness can hold on a genuine support-restricted
  family. If every feasible old tuple at each requested run has all internal
  coordinates in the relevant images, (3.3) holds. Still more generally it
  is enough for each feasible exterior pair to have one such tuple, even
  when other feasible tuples lie outside the images.
* A noninvertible family allowing **all permitted unit insertions** is
  furnished by inclusions `U_i↪X_i` and relations supported on
  `U_(i-1)×U_i`, using `U_i` as primed carriers. Every feasible realization
  on a nonempty run lies in the images and has unique lifts; every map is
  injective. Units may be inserted anywhere using their actual diagonals.
  Those old diagonals need not themselves be supported on `U_i×U_i`, but
  their nullary comparison is exact and their nonempty unit constraints
  force the same boundary values. Thus the family is closed under the
  stated compositions and unit insertions. If some `U_i` is a proper subset,
  transport is genuinely noninvertible on the full interface set. This is
  a restricted semantic sublanguage, not the complete relation quiver.

### Theorem 5.1 — complete-quiver obstruction, including the global empty case

Fix any label set `I`, finite carriers `X_i,X'_i`, and maps `f_i:X'_i→X_i`.
Use C2's **complete** relation quivers with every relation at every ordered
label pair and every finite ordered typed path. The global base-changing
restriction map exists and preserves containment-calculus identities and
substitution for all `f_i` (C2 §5.1 and Theorem 4.1). Moreover:

1. It preserves every exact operation of positive arity iff either all
   `X'_i` are empty or all `f_i` are surjective.
2. It preserves every exact operation of all arities iff either all
   `X'_i` are empty or all `f_i` are bijective.              (5.1)

**Proof.** If every primed carrier is empty, every primed relation, every
positive composite, and every primed diagonal is empty. Every image exact
cell is therefore exact. Otherwise choose `j` with `X'_j≠∅`. For any label
`i`, consider every binary path `j→i→j`. Its exteriors are nonempty, so
Theorem 2.2 forces `f_i` to be surjective if every such exact cell is to
stay exact: take its old whole to be the old composite. This proves the
necessity in (1), and sufficiency is Theorem 3.1. For (2), the exact nullary
cell with whole `Δ_Xi` additionally forces `f_i` injective for every `i`
by Theorem 3.2. Conversely bijections satisfy all positive and nullary
criteria. Empty label sets cause no problem: the quantified statements
are vacuous. QED.

Thus a nontrivial exact **all-arity** action on the complete relation
calculus cannot be extended to arbitrary nonbijective global carrier maps
by ordinary restriction. This is a sharp impossibility result for the
specified construction and specified complete model, not a theorem denying
all alternative transport or descent doctrines. The coherent containment
calculus is one already constructed repair. The admissible support-restricted
families and the retained-span comparisons below are other precise levels,
not unannounced isomorphisms.

For global map families the induced containment operation map also induces
maps on full C2 occurrence-refinement tuples: map each child operation at
its own original slot. Substitution preservation proves the defining
refinement equation and the functor laws. No faithfulness, fullness,
essential surjectivity, or witness-lifting uniqueness follows from this
functoriality. On the exact calculus this assertion is restricted to the
families/domain justified by (5.1) or Theorem 4.1.

## 6. Chosen categorical extension: actual finite spans, imported with scope

This section uses the already proved CUT §10 formula (10.1)–(10.3) and I4
§§2–3.4. It identifies exactly what their result contributes to D2.

An actual span `S:A←S→B` retains its finite apex and its two leg tables.
Its restriction has apex

    (f,g)^*S = {(a',s,b') | f(a')=left(s), g(b')=right(s)}.

For `S:A←S→B` and `T:B←T→C`, their chosen composite apex retains actual
pairs `(s,t)` with `right(s)=left(t)`. There is a specified map

    c: P((f,g)^*S,(g,h)^*T) → (f,h)^*P(S,T),
    (a',s,b',t,c') ↦ (a',s,t,c').                         (6.1)

Over a target witness `(a',s,t,c')` of old middle value `b`, its fibre is
literally `g^(-1)(b)`. More generally, for any positive path of spans a
fixed feasible old witness tuple with its specified lifted exteriors has
comparison fibre

    ∏_(0<i<n) f_i^(-1)(x_i).                            (6.2)

Consequently the comparison is surjective iff each such fibre is nonempty,
injective iff each such fibre has at most one element, and bijective iff
each has exactly one element. Empty target apexes pass all three tests
vacuously, because a total map into that empty target has empty source.
For fixed actual spans this checks **each old apex tuple**, not merely one
representative for each externally supported pair.

For a nullary identity span the map instead is

    X' → X'×_X X',        x' ↦ (x',x'),                  (6.3)

and is bijective iff `f` is injective. Again no empty internal product
replaces the nullary check.

### Corollary 6.1 — uniform span comparison versus uniform relation equality

For fixed binary boundary maps `f,g,h`, (6.1) is bijective for every finite
pair of spans iff `A'=∅` or `C'=∅` or `g` is bijective. For a positive path
of length `n≥2`, the corresponding uniform condition is: a primed exterior
is empty, some old internal carrier is empty, or all internal maps are
bijective. Unary comparisons are canonical bijections for all maps.

**Proof.** The empty cases force both apexes empty. Internal bijections give
singleton fibres (6.2). If exteriors and old internal carriers are nonempty,
choose singleton-apex spans through any prescribed old internal tuple.
Uniform bijectivity forces every coordinate fibre to be a singleton by
(6.2), hence every internal map bijective. Conversely this suffices. For
binary length this says precisely that every fibre of `g` is a singleton.
QED.

The same argument with 'nonempty' instead of 'singleton' gives the universal
surjectivity condition of Theorem 3.1. The fixed-relation equality condition
is weaker than actual-span surjectivity: passage from spans to their
endpoint support erases which old realizing tuple was present.

### 6.1 Imported retained-cut theorem and its exact domain

A retained exact cut diagram includes each actual intermediate apex, its
leg tables, and each proper certificate

    β_v:P(S_(v,1),...,S_(v,k)) → S_v

as a supplied endpoint-preserving **bijection**. Its root coefficient may
be arbitrary and is not canceled. For one incidence-compatible interface
change let `c_v` be (6.1)/(6.2), or (6.3), computed on that vertex's
**actual child spans**. The transported certificate is specifically

    β'_v = (restriction of β_v) ∘ c_v.                   (6.4)

Restriction of an endpoint-preserving bijection is a bijection: its inverse
is the endpoint-preserving inverse restricted by the same boundary maps.
Therefore (6.4) is bijective exactly when the finite unique-lift test passes
at that named vertex. It is not enough that the root support is unchanged.

CUT §10 proves that passing these tests at every requested run/node and
nullary yields transport of all the retained certificate objects and their
actual coefficient morphisms, coherent with arbitrary finite contractions,
regroupings, exact grafts and successive interface changes. I4 §§3.3–3.4
extends/uses precisely these comparisons in its full retained-diagram
mixed setting and explicitly keeps individual forest stages where those
are part of the compared object. Their proof is tuple projection, followed
by the actual supplied `β_v` maps: both routes forget the same lift
coordinates, and inverse maps, when they exist, are forced by the same
singleton fibres. Theorem 4.1 is the existential relational counterpart;
it is not a new proof replacing that stronger prior retained-witness result.

**Context and factorization must remain explicit.** First cartesianly
restrict a supplied endpoint-preserving coefficient map at its existing
interfaces. If its domain was already an old composite, that restricted
old composite is its domain. The comparison from the composite of
individually restricted pieces to this restricted old domain is a separate
map `c_v`; only then compose. This is I4 §3.3A's distinction. A bijection
covering a noninjective change of interfaces is not silently treated as an
endpoint-preserving bijection in a fixed fibre. Arbitrary ambient span
coefficients do not receive a proved orbit-quotient descent theorem here.
No graph quotient, support quotient, or forgetting of proper certificates
is allowed to bypass these distinctions.

## 7. Explicit controls and the boundary between existence and unique lifting

All unspecified exterior carriers in the first five examples are singleton,
and their boundary maps are identities.

1. **Positive noninjective-surjective family.** `B={0,1}`,
   `B'={a,b,c}`, `g(a)=g(b)=0`, `g(c)=1`. Every `R,S` gives relational
   equality by Theorem 2.2. If a composite old witness has middle value 0,
   its actual span fibre has two elements; span bijectivity fails there.
2. **Strict nonsurjective comparison.** `B={0,1}`, `B'={a}`, `g(a)=0`,
   and singleton relations supported only through middle value 1. The
   restricted composite has its exterior pair; the composite of restricted
   relations is empty.
3. **Nonsurjective relation-specific equality, but missing old witnesses.**
   Use the same map as in (2), with total `R,S`. Both relational results
   contain the single exterior pair, witnessed after restriction through 0.
   The actual comparison misses the old witness through 1.
4. **Equal cardinalities are not comparison invertibility.** `B={0,1}`,
   `B'={a,b}`, both mapped to 0, with total `R,S`. Each actual composite
   apex has two elements, but (6.1) sends both source witnesses to the old
   witness through 0. It is neither injective nor surjective, although the
   relations are equal and the two apex cardinalities coincide.
5. **Noninvertible, genuinely exact actual-span slice.** `B'={a}` includes
   as 0 in `B={0,1}`, and both spans have singleton apexes supported through
   0. The actual comparison is a bijection despite `g` not being surjective
   on all of `B`. Unique lifting is needed only on feasible old tuples.
6. **Exterior emptiness refutes the naive converse.** Take `A'=∅`, any
   existing `f:∅→A`, and a nonsurjective map as in (2). Every `R,S` still
   gives equality because both exterior relations are empty. Likewise for
   `C'=∅`. If `B=∅`, `g` is the surjective empty function, not a further
   counterexample to the sharp criterion.
7. **Different empty internal carrier.** At length three take one old
   internal carrier empty and another nonempty with a nonsurjective map.
   Every composite is empty, so uniform equality holds by (3.4) even
   though not all internal maps are surjective.
8. **Surjective noninjective nullary failure.** For `{0,1}→{*}`, the target
   of (3.5) has four pairs and the source has only its two diagonal pairs.
   Thus even universal binary equality does not imply unit preservation.
   In contrast an inclusion `{0}→{0,1}` has exact nullary comparison despite
   not being surjective; `∅→X` does too.
9. **Root or primitive-pair tests can miss retained intermediates.** The
   explicit length-three example in §4.2 is the established CUT/I4 control.
   For actual graph-decorated spans, CUT additionally gives a whole active
   under the graph quotient while an intermediate first-two-block cut is
   inactive: a `2→1` lift fibre is hidden at the whole but not at that
   retained proper certificate. The latter example is imported with its
   original retained/quotient distinction, not asserted as a theorem about
   arbitrary quotient doctrines.
10. **Global all-empty exception.** Let each `X'_i=∅` and at least one
    `X_i` be nonempty. The complete exact C2 calculus restricts to the
    all-empty calculus in every arity, although some interface maps are
    not bijective. If any primed carrier becomes nonempty, Theorem 5.1's
    binary sandwich tests force all maps surjective, and nullaries then
    force all maps bijective.

## 8. What is and is not discharged

The mathematical source supplies the comparison, the relation-specific
finite table criterion, the sharp uniform map-class theorem with every
empty exception, noninvertible positive families, explicit arbitrary-tree
compatibility, and both a chosen finite-Span extension and a sharp
complete-C2 all-arity limitation. It retains intermediate witnesses whenever
a comparison claims actual witness recovery. The strengthened span/tree
result is explicitly reused from CUT/I4; it is not double-counted as a new
D2 discovery. D1 is recovered on bijections with its actual equation and
refinement checks, not replaced by endpoint-only renaming.

There is no new full D2 Lean development claimed: original C2's formal API
and D1's typed-action bridge are inherited background, while these sharp
classification theorems are P-level results. The independent finite C tests
validate their stated bounded domains and controls, not arbitrary cardinality
or depth. The checked primary-source comparison is `../literature_comparison.md`.
Ordinary Beck–Chevalley isomorphisms have a cartesian-square hypothesis;
no such hypothesis is silently supplied for arbitrary `f,g,h` here.

The independent auditor and parent determine contract disposition;
this author's theorem does not self-accept D2, D3, or the whole project.
