# E2 — Substantive graph/span reconstruction and quotient lift uniqueness

**Result and exact target.** The selected reconstructed class is the parameterized
virtual equipment `V(N,M)` of an actual ordered graph, an actual finite span, an
actual ordered cut, an endpoint-compatible function of witnesses, and one global
finite commutative-monoid decoration. Its presentation names span horizontals and
unary span squares, but generates **all multicells** from binary cuts, one kind of
nullary unit, unary scalars, and a fixed list of local equation schemes. Evaluation
is an isomorphism, with an explicit inverse normal form in every full boundary
sort. This is a substantive enlarged local presentation, **not** the assertion
that the smaller C5-only free equipment generates all finite spans.

The original C5 presented core maps canonically both into its free chosen envelope
and into this reconstructed equipment. The first map is equality-conservative on
all original profiles; the second is bijective on their cell fibres. These remain
true in the explicitly described scalar/unit-subgroup and activated-coefficient
quotient families. Generic relative declarations of existing cells as cartesian
need not be original-profile conservative: the terminal-restriction return-context
obstruction proves an unbounded counterfamily.

A distinction matters for the quotient clause: an ordinary substitution congruence
on an **already complete** virtual equipment, with all objects, vertical arrows,
horizontal arrows and boundary sorts fixed, automatically preserves restriction
and contextual-unit uniqueness. We prove this by actual substitution formulas for
the inverse factors, not by assuming that the quotient is an equipment. A
preequipment or a partially presented core has no such automatic conclusion.
The generator/relation saturation criterion below treats that case and computes
its exact unavoidable equality cost.

This is P-level mathematical work, reusing the existing explicit EXT/ENV/SPAN,
A3, BRIDGE and NOGO proofs and adding the fixed-sort quotient distinction and
relative saturation analysis. It asserts no new Lean formalization, all-span
C5 generation, general free-envelope normal form, or blanket historical-ledger
acceptance. Its companion `universal_theorem.md` supplies the generic free chosen
construction and 2-dimensional universal property. Full paths/hashes are in
`reconstruction_source_map.md`.

## 1. Reconstruction input: more than a bare core

Fix `N≥6` (the formulas also work for smaller bounds), a nonempty finite category
`K`, and a finite commutative monoid `M`. Retain the following data explicitly:

1. The category `B` of actual finite coded/tagged sets and **all** functions between
   them, chosen small and closed under the displayed finite tuple, pullback and
   doubling constructions. Its object names and composition table are input.
2. Ordered graphs on `[r]`, `r≤N`, their complete edge relations, and the increasing
   inclusions `i_U` for induced restrictions. Graphs are not reconstructed from
   their pieces. `i_(i_U V)=i_U i_V` is used throughout.
3. Actual spans `S=(A←l E→r B)`, their apex/leg maps, and actual span squares
   `(a,e,b):S→T`. Equal empty apex functions with different boundary maps remain
   different squares/sorts. No apex is taken modulo isomorphism.
4. The boundary-marked tuple span `[p]` of each finite path of spans. Its apex is
   `P(p)={(a0,e1,a1,…,en,an): l_i(e_i)=a_(i−1), r_i(e_i)=a_i}`.
   For `p=()_A`, `P(p)=A` and both endpoint maps are identities. Explicit tuple
   flattenings/deletions, rather than equality of nested tuple encodings, are used.
5. The local signature/equations in §2, the selected universal restriction/unit
   cells of §4, and any further admissible or exact markings. The reconstruction
   uses whole-globular admissibility; the embedded original core is a separately
   specified admissible subcalculus. Extra markings use E1's declared preservation
   convention and explicit transport where needed; they are not guessed from names.
6. The faithful tagged realization
   `F(A)={(A,C,t):t:C→A in K}`, `F(h)(A,C,t)=(B,C,ht)`.
   It is faithful by evaluation at `id_A`, and injective on interface names because
   of tags. This specifies where the original interfaces sit inside `B`.

The vertical category and restriction data do **not** follow from a globular
multicategory. For instance the same original `C(N,K,M)` can be embedded in a
vertical category with only the designated interface image or in the full finite-map
category, and its globular profile data alone do not specify either choice. Our
reconstruction therefore retains the six items above rather than claiming recovery
from a bare core.

## 2. Local presentation, independently defined semantics, and canonical normal form

### 2.1 The semantic equipment

A horizontal is `H(G,S):A⇒B`. For a full source path
`p=(H(G1,S1),…,H(Gn,Sn)):A0⇒An`, target `H(G,S):B0⇒B1`, and fixed boundary
maps `f:A0→B0`, `g:An→B1`, a cell is precisely

    (π,φ,m),
    π=(U1,…,Un) an ordered partition of V(G), G|Ui=Gi,
    φ:P(p)→E_S,     l_S φ=f π0,    r_S φ=g πn,
    m∈M.                                                       (2.1)

These definitions precede the presentation quotient. At arity zero the partition
forces `G=0`, but the function `φ:A0→E_S`, both boundary maps, and `m` survive.
Substitution lifts actual graph subsets by increasing inclusions, composes the
actual tuple functions, and multiplies the outer and every child scalar. Its row
includes the common maps `u0,…,un`, including `u0` at outer arity zero. SPAN §§2–5
proves all laws and the equipment universal properties directly.

### 2.2 The reusable local signature

Name every `H(G,S)`, but do **not** name every multicell. The generator forms are:

* `u_f^G:H(G,S)⇒H(G,T)` for each actual square `f=(a,e,b):S→T`;
* `d_m^H:H⇒H` for `m∈M`;
* `c_(G;U,V;S,T):(H(G|U,S),H(G|V,T))⇒H(G,[S,T])`, for binary graph partitions,
  including empty blocks;
* `c0_A:()_A⇒H(0,I_A)`, where `I_A=(A←id A→id A)`.

Use the following finite **forms** of equation schemes, plus typed VDC laws:

* span-square category tables `u_id=id`, `u_g u_f=u_(gf)`;
* `d_1=id`, `d_m d_n=d_(mn)`, and scalar naturality past `u_f`;
* movement of a scalar from either binary input to the binary output;
* matched-row binary naturality
  `u_[f,g] c = c[u_f,u_g]`, requiring the same middle vertical map;
* nullary naturality `u_(I_h)c0_A=c0_B⟨h⟩`;
* ternary rotation after the explicit flattening squares
  `[[S,T],R]→[S,T,R]←[S,[T,R]]`;
* left/right deletion of **the designated** `c0` after the explicit bijections
  `[I_A,S]→S` and `[S,I_B]→S`.

The span-square category tables are a base unary category presentation; they are
not a list of arbitrary multiary semantic cells or of every true equation. The
cut laws have at most ternary shape, independently of final arity/depth. This is
a small, generally infinite presentation with finitely many rule forms. No claim
of a finite total set of finite-span generators is made. Call its term quotient
`P(N,M)`.

### 2.3 Reconstruction theorem and proof

For a partition `π` and span path `p`, define `c_flat(π;p)` using a right-comb binary
cut tree, postcomposed with the explicit tuple-flattening square. At arity zero it
is `c0`; at arity one it is the unary tuple-encoding map
`j_S:S→[S]`, `e↦(l(e),e,r(e))`, not an illicit equality of apex sets. Its semantic
coefficient is `id_P(p)`, and its scalar is `1`. Define

    NF(π,φ,m | f,g)
      = u_(f,φ,g)^G d_m^(H(G,[p])) c_flat(π;p).             (2.2)

**Theorem 2.1 (substantive reconstruction).** Evaluation
`Ev:P(N,M)→V(N,M)` is an isomorphism of VDCs and, with the displayed choices,
of chosen virtual equipments. Its inverse on every boundary sort is (2.2).

**Proof.** Each generator has the semantic data just specified. Every local law
is sound: matched naturality is the pointwise induced tuple map, rotation expands
the same final coordinate sequence, and unit deletion erases precisely forced
identity-span coordinates. Normalize a generator-rooted substitution tree bottom
up. A unary square composes with the outer square by the category tables; a
scalar moves outward and multiplies by the monoid laws. At a binary root, move
both child squares outward by **matched** naturality, move both scalar values
outward, and rotate the remaining binary cut tree to the fixed right comb.
At each rotation the two accumulated flattening maps agree pointwise, and hence
are identified by the unary category tables. A nullary child is deleted only after
its actual coefficient square and scalar have been moved outward; its unequal
boundary maps and scalar are not erased. A nullary root whiskered by `h` normalizes
by `u_(I_h)c0=c0⟨h⟩`. These cases cover every tree, including identities.

Consequently every term equals (2.2) with its evaluated `(π,φ,m)`. Every semantic
triple has that term as a preimage. Equal semantic triples give the very same normal
form, while soundness excludes any other equality. Thus evaluation is bijective
on every fixed full sort and preserves all structure; (2.2) is its inverse. The
restrictions/units of §4 are correspondingly universal on both sides. This is the
explicit EXT §§3–5 argument, not a freeness assumption. ∎

Repeated equal components remain different positions in `π`; a zero tuple set
does not discard any position. Arbitrary unary/nullary decorations remain in
`m`. The proof applies in all finite arities and unbounded tree depths.

## 3. Reconstruction on morphisms and transformations

For an arbitrary target VDC `E`, let `Local_E` have as objects interpretations of
the named vertical category, horizontal names and four generator forms satisfying
the displayed local laws. A morphism is a vertical natural transformation and a
unary component at **every named horizontal**, natural for those generators.
At nullary generators its naturality includes the actual common vertical component.

Restriction to generators and evaluation of terms are inverse functors

    VDC(P(N,M),E)  ≅  Local_E.                            (3.1)

Naturality for a composite term follows inductively from generator naturality
and substitution associativity, including nullary whiskering. Thus (3.1) is an
isomorphism of **categories**, not an object or hom-set correspondence. Substituting
`Ev` and its explicit inverse produces

    VDC(V(N,M),E)  ≅  Local_E,                            (3.2)

whose maps are respectively generator restriction and evaluation by (2.2).
Both round trips are literally identity on functors and their components.
Postcomposition by a target functor commutes with both constructions, and
whiskering a transformation has the same components; hence the isomorphism is
2-dimensionally target-natural at the stated VDC level.

For the equipment statement restrict `Local_E` to interpretations carrying each
`c0_A` to a contextual unit and each displayed pullback square in §4 to a cartesian
cell. These are **target universal properties**, not equations claimed to force
universality against arbitrary extra target cells. Then (3.2) restricts to the
category of universal-structure-preserving equipment functors and its full
cell-natural transformation category. As E1 records, cartesian preservation is
already automatic for every VDC functor between full virtual equipments; normality
means unit preservation. Listing both universal conditions is a redundant explicit
check, not a new weaker notion of normal morphism. A strict chosen version
additionally demands literal choice compatibility. Arbitrary raw interpretations
of all named horizontals are not asserted strictifiable while fixing those names.
This marked-sketch universal property is distinct from the free fresh-horizontal
construction in `universal_theorem.md`.

If further admissible/exact markings are supplied, impose E1's stated preservation
conditions on the corresponding interpretations. The inverse maps preserve those
conditions because they agree on the actual cells. No additional exactness is
ascribed to binary graph cuts merely because they are generators.

**Bridge to the generic chosen presentation.** Let `Q_EXT` be the local signature
and relations of §2, supplemented by declaring each named `c0_A` a contextual unit
and each named pullback cell of §4 cartesian. The latter declarations use the
explicit comparison-isomorphism encoding (6.6a), or its one-inverse-generator
variant in the companion theorem. This is a small reusable marked presentation,
not a diagram of every semantic multicell.

Let `F(Q_EXT)` be the companion generic chosen term equipment. Evaluation in the
independently constructed `P(N,M)` gives a normal functor
`q:F(Q_EXT)→P(N,M)`. Conversely the named generators and the local equations give
a VDC functor `j:P(N,M)→F(Q_EXT)`. It is normal because the named `c0_A` were
explicitly declared universal; the named cartesian cells have their proved/marked
universal properties. On all named horizontal objects and all generator cells,
`qj` is the identity, so term induction gives `qj=id_P`.

The functors `jq` and `id_F` agree on the original EXT named horizontals and
local generators. Extend their identity components recursively to a fresh restriction
using cartesian comparison and to a fresh unit using unit comparison. The auxiliary
comparison-inverse generators have fresh-horizontal types, so one does **not**
claim literal agreement there: naturality for them is forced by their inverse
equations and the already established naturality for the cartesian comparisons.
Naturality for declared universal factors follows by uniqueness. The companion's
normal interpretation-category theorem (including its §11.3 bridge) therefore
gives the actual invertible comparison `jq≅id_F`, with inverse and coherence laws,
whose components on all named horizontals and vertical objects are identities.
The comparison encoding adds no free choice because its inverse is uniquely
determined.
Thus `F(Q_EXT)` is equivalent, in the underlying normal-functor/cell-natural-
transformation 2-category with whole-globular admissibility, to the reconstructed
`P(N,M)≅V(N,M)`. This admits every declared `c0_A`, not only those at F(K).
Extra selected markings or smaller admissibility families extend this equivalence
only when transferred/pulled back along q,j and the displayed comparisons; no
unchanged arbitrary-mark equivalence is asserted. Their horizontal-name sets need
not be literally equal. Naturality of the comparison, identity on named boundaries,
also proves that every F-cell entirely on named profiles equals `j` of its q-image.
This explicitly connects the universal chosen construction to the substantive
semantic reconstruction while making no such equivalence claim for **C5-only**
`F(C)`.

## 4. Actual restrictions, units, and all alternative choices

For `S=(B←l E→r C)` and `f:A→B`, `g:D→C`, set

    R_(f,g)S = (A ← {(a,e,d): f(a)=l(e), g(d)=r(e)} → D).

The square `(f,pr_E,g)` gives `κ:H(G,R_(f,g)S)⇒H(G,S)`.
Its inverse factor on (2.1), for boundaries `fu,gv`, is

    (π,φ,m) ↦ (π, z↦(uπ0(z),φ(z),vπn(z)), m).           (4.1)

Projection is the inverse. Fixed outside boundaries force first/last coordinates;
therefore uniqueness holds in every arity, even zero.

The chosen unit is `H(0,I_A)` with `c0_A`. Inserting it at a specified source
position inserts one empty partition block and the forced diagonal coordinate;
its inverse deletes those exact coordinates and block, retaining `m`. This gives
bijections in every context. Two inserted units commute because both orders erase
the same designated positions. No arbitrary empty-graph span is erased.

**Proposition 4.1 (classification in the selected semantics).**

1. A unary cell `H(G,T)⇒H(G,S)` with boundaries `f,g`, apex map `e` and scalar `m`
   is cartesian iff the induced map
   `E_T→E_(R_(f,g)S)`, `t↦(l_T(t),e(t),r_T(t))`, is bijective and `m∈M^×`.
2. A globular nullary cell `()_A⇒H(G,S)` is a contextual unit iff `G=0`, its apex
   function `σ:A→E_S` is an isomorphism of the identity span with `S`, and its
   scalar belongs to `M^×`. Equivalently `l_S=r_S` is a bijection with inverse `σ`.

**Proof.** Cartesian cells with a fixed target and boundaries have unique inverse
globular comparisons. Comparing with the displayed κ gives a globular isomorphism
whose coefficient is exactly the indicated apex map and whose scalar is `m`.
A globular unary isomorphism in (2.1) is precisely a bijective apex map with unit
scalar (its graph is fixed by the unary partition). Conversely an isomorphism
followed by κ is cartesian. For units, compare the proposed nullary with `c0_A`
using their contextual universal properties. The resulting unary comparison is
an isomorphism; its coefficient and scalar are `σ,m`. The converse follows by
composition with that isomorphism. This includes empty apexes because the global
scalar coordinate is never discarded. ∎

**Actual change-of-choice maps.** A second restriction choice has a unique
isomorphism to the displayed pullback, defined by the cartesian factorization of
its cell. Its inverse is obtained in the other direction. Their composites are
identities by postcomposition with κ and uniqueness. For two tuple encodings this
is explicitly encoding-change of `(a,e,d)`. For successive restrictions the
comparison deletes intermediate coordinates; any iterated route deletes precisely
the same coordinates. For a second unit choice, factor each universal nullary
through the other; the two inverse maps commute with the universal cells.
For three choices the direct comparison equals the two-step comparison by the
same uniqueness argument. These maps induce the recursive comparisons of all
interpreted terms and transformations established in the companion universal
proof. Thus chosen reconstruction passes to coherent unchosen structures through
specified maps, not the phrase “canonical choices”.

## 5. The canonical original-core maps and their exact strength

Let `C=C(N,K,M)` be the **original** local C5 presentation: binary `C`, nullary `U_A`,
unary `D(W,m)`, with exactly `R,UL,UR,D0,DA,DL,DR`. A3's independently proved normal
form identifies it with full data `(output (G,h), full input arrow path, π,m)`.
This is not the extended list of local equations in §2.

### 5.1 Into the reconstructed identity-boundary calculus

Define on original components and generators

    J(G,h:A→B)=H(G,Γ(Fh)),
    J(π,m)=NF(π,π0,m | id,id).                           (5.1)

Here `Γ(Fh)=(FA←id FA→Fh FB)`. The tuple source of a composable string of graph
spans has exactly one tuple for every starting point; `π0:P(Jp)→FA0` is a bijection.
The left output leg forces every coefficient map to be `π0`. The right leg then
requires `Fh=F(h_n…h_1)`, equivalently `h=h_n…h_1` by faithfulness of `F`.
At arity zero it requires `G=0` and `h=id_A`. Thus

    C(p;W)  ≅  Core(V(N,M))(Jp;JW)                      (5.2)

for **every original full profile**, including empty fibres. The original seven
relations hold because graph partitions/scalars substitute identically; (5.1)
therefore descends from the actual original presented core. (5.2) proves both
fullness and equality reflection on those profiles. At the refinement level the
same statement holds entrywise for actual old-profile tuples, and substitution
preserves their compatibility equations. Tuples are not replaced by flattened
endpoints.

The old empty identity component maps here to `H(0,Γ(F id_A))=H(0,I_FA)`, and its
scalar-one nullary maps to `c0_FA`. This identification is justified by the explicit
span formula and contextual-unit theorem. It holds in **this selected semantic
reconstruction**, not as an unproved identification in free syntax.

### 5.2 Into the free fresh-horizontal envelope

Let `η_C:C→Core(V_free(C;B))` send each original horizontal/generator to its names
in the companion free construction. This is the requested canonical original
presented-core map: old equations are among the constructor equations, so the map
is well-defined. Its horizontal grammar consists of old `W`, fresh `I_A`, and fresh
`H[f,g]`; the ordinary strengthening also has `Comp(p)`. There are no horizontal
term equations. Identity and iterated restrictions are coherently isomorphic by
universal comparison, not literally equal. Old empty loops and fresh `I_A` remain
different names.

The local semantic interpretation (5.1), together with the selected restrictions
and units, extends uniquely to `V_free(C;B)→V(N,M)`. Hence if two old cells become
equal in the free envelope, their images in (5.2) are equal and they were already
equal. This is **conservativity**, not a claim that every new original-profile cell
is old. For the ordinary envelope, use ENV's graph-**word**/span model: old `G`
maps to `[G]`, the new unit has empty word, and all original cell fibres still have
exactly one cut and one forced coefficient. This separately proves ordinary
conservativity. Its occurrence allocation separates `[empty graph]` from the
empty word, so no unsupported old-loop/unit isomorphism is being inferred.

### 5.3 Exact boundary, not a missing stronger requirement

The above reconstructed semantic class deliberately has explicit all-span names
and squares. They need not be generated by C5 plus fresh unit/restriction/composite
constructors. GEN proves that, for `b=max_A |F(A)|`, the ordinary semantic horizontal
image consists precisely of empty graph words or spans whose nonnegative-integer
multiplicity matrix has factorization width at most `b`. In particular a graph
carrier on an identity span of size `>b` is missing. Full carrier-cell generation
and equality completeness from a smaller added-carrier signature remain a separate
stronger problem. No part of (2.2), (5.2), or free-envelope conservativity assumes
that false maximal-span image claim.

## 6. Quotient criterion at the correct presentation level

All quotients below are **parallel**: vertical objects/arrows, horizontals, full
profiles and boundary maps remain fixed. Quotienting those sorts is a different
problem and needs new existence/descent hypotheses.

### 6.1 Necessary and sufficient uniqueness criterion

Suppose a prequotient has designated restriction cell κ and actual inverse factor
`L` on the relevant fibres. Let `R` be a substitution congruence. Postcomposition
by κ descends and remains surjective. It is injective on quotient fibres iff

    κa R κb  implies  a R b,                             (6.1)

for every correctly typed pair of lifts, in every source arity. Equivalently

    α R β  implies  Lα R Lβ.                             (6.2)

Indeed use `α=κa,β=κb` in one direction and `κLα=α` in the other. For contextual
units the exact condition is similarly

    a[1_r,η,1_s] R b[1_r,η,1_s]  implies  a R b,         (6.3)

or stability under the inverse insertion `U_(r,A,s)`. For a separately designated
nonnullary opcartesian cell `e:q⇒H`, the corresponding exact condition is
`a[1_r,e,1_s] R b[1_r,e,1_s] ⇒ a R b`, equivalently stability of its source-compression
inverse `Q_(r,e,s)`. This proves, rather than assumes, when an equation between
composites has identified the unique lifts.

For a local presentation with declared equation pairs `E`, a generator/relation
criterion is: take each correctly typed instance of a declared pair inside an
ordinary one-hole substitution context, including its full shared vertical maps;
apply each type-correct inverse-factor operation `L` or `U`; and require the
resulting pair to have an ordinary congruence derivation from `E`. This is necessary
and sufficient. Necessity is (6.2)/(6.3). For sufficiency, every ordinary congruence
derivation is a finite zigzag of contextual equation instances; apply the inverse
to each step, then use symmetry/transitivity. This is an effective proof obligation
schema on generators/relations, not an assertion that checking the bare uncontexted
generators suffices. It makes no finite-termination or decision claim in general.
For §7's family it reduces to explicit finite induced-subgraph and monoid tests.

### 6.2 A complete fixed-sort equipment has the needed contexts already

**Theorem 6.1 (quotients of complete virtual equipments).** Every parallel ordinary
VDC substitution congruence on a complete virtual equipment preserves its chosen
restriction and contextual-unit bijections. Thus its homwise quotient is a virtual
equipment, with the same chosen horizontals/cells. No additional saturation of
that congruence is needed for these universal structures.

**Proof for restrictions.** Fix `K:B⇒C`, `f:A→B`, `g:D→C`, and `κ:R⇒K`.
Set `P=I_B[f,id_B]:A⇒B`, `Q=I_C[id_C,g]:C⇒D`, with cartesian cells `p,q` to the
respective units. Lift `η_B⟨f⟩` and `η_C⟨g⟩` to obtain

    ε_f:()_A⇒P | id_A,f,      ε_g:()_D⇒Q | g,id_D,
    p ε_f=η_B⟨f⟩,            q ε_g=η_C⟨g⟩.

Let `ω_K:(I_B,K,I_C)⇒K` be the double unitor obtained by inserting the units into
`1_K`. Define the fixed cell

    τ=L_κ(ω_K[p,1_K,q]):(P,K,Q)⇒R | id_A,id_D.

For every `α:s⇒K | fu,gv`, where `s:X⇒Y`, direct postcomposition with κ and the
unit laws give

    L_κ(α)=τ[ε_f⟨u⟩, α, ε_g⟨v⟩].                      (6.4)

The row's shared maps are **exactly** `u,fu,gv,v`. Both sides have boundaries
`u,v`; the right side postcomposes to α, so prequotient cartesian uniqueness proves
the formula. This also applies when `s=()_X` and `u,v` are different maps from the
same source. The right side is an ordinary substitution context with one hole α
and fixed other cells. Hence any substitution congruence respects it.

**Proof for units.** For insertion into a nonempty source path, choose an adjacent
source horizontal and substitute its fixed left or right unitor at that occurrence.
This produces precisely `U(α)`: precomposing with η returns α, so uniqueness proves
the formula. For an entirely empty source, write `α:()_A⇒K | f,g`, `K:B⇒C`.
Let `v_f:I_A⇒I_B | f,f` be the unique unit comparison satisfying
`v_f η_A=η_B⟨f⟩`, and let `ℓ_K:(I_B,K)⇒K` be the left unitor. Then

    U(α)=ℓ_K[v_f,α].                                    (6.5)

Substitution of η_A gives α by that comparison equation and the left-unit law.
Again the displayed expression is an ordinary one-hole substitution context.
Thus every inverse unit factor respects the congruence. Applying §6.1 gives the
claimed bijections on quotient sets. This argument does not use any universal
property of the quotient before proving it. ∎

This explains why a purported full-equipment counterexample consisting only of
`κa~κb` but `a≁b` is not a substitution congruence once all the structural contexts
(6.4) are admitted. A genuine failure test must specify the missing contexts or
work at the preequipment/relative-marking level, as §8 does. Theorem 6.1 does
**not** assert preservation of arbitrary selected nonnullary opcartesian/exact
markings. Their inverse source-compression operators `Q_e` must satisfy the
additional criterion in §6.1; no automatic context formula for them is proved here.

### 6.3 Relative saturation, its adequacy, and its exact equality cost

For a raw presentation that has not yet supplied universal inverse operations,
adjoin typed `L,U` operations and their beta/eta equations as in the companion
free construction; for designated existing cartesian cells use the same equations
without replacing their horizontal names. Equivalently, and within the companion's
staged presentation language, a designated existing cell `κ:R⇒K | f,g` can be
required cartesian by adjoining globular generators

    i:R⇒K[f,g],   j:K[f,g]⇒R,
    κ_ch i=κ,    ji=id_R,    ij=id_(K[f,g]).               (6.6a)

The existing κ is then a chosen cartesian cell followed by an isomorphism, and
hence cartesian. Conversely if κ is cartesian, comparison with the free chosen
restriction uniquely determines inverse i,j satisfying these equations. Thus this
encoding changes neither the eligible target models nor their morphisms: their
components at i,j are forced by naturality and cartesian uniqueness. It does not
identify either horizontal name. A relative factor is expressible as
`L_κ(α)=j L_κch(α)`; (6.6a) gives its beta/eta laws. It is therefore legitimate to
use the direct relative-factor notation below without adding an unproved universal
construction beyond the companion theorem.

Start with the ordinary substitution congruence `R0` generated on the expanded raw
term set by the original declared relations, **all VDC laws, and all universal
beta/eta laws**, including the comparison equations (6.6a) when that encoding is
used. Recursively let
`R_(n+1)` be its ordinary substitution-congruence closure after adjoining all
`(Lα,Lβ)` and `(Uα,Uβ)` with `α R_n β` in the correct sort. Then

    Sat(R0)=⋃_(n<ω) R_n.                                (6.6)

All constructors/rules are finitary. Consequently the union is a congruence closed
under every factor operation: a finite premise already lies in one stage. It is
the least such congruence, by induction into any other factor-stable congruence
containing `R0`. If selected nonnullary opcartesian cells are part of the input,
include their typed `Q_e` constructors, beta/eta laws and closure pairs in the same
recursion; the identical finitary proof applies. No automatic `Q_e` preservation
is deduced from Theorem 6.1. Beta/eta now descend to inverse maps, proving adequacy, not merely
existence of a relation. Every equality in (6.6) has a finite derivation; no finite
stage or algorithmic termination is asserted.

Every interpretation into an eligible equipment respecting the raw generators,
relations and designated universal cells sends each new factor to its unique
factor. Induction over (6.6) shows it identifies every saturated pair. Conversely
the saturated term quotient is itself such an equipment and separates every pair
not in (6.6). Thus **exactly** the saturated equalities, not an unspecified larger
kernel, are forced by all eligible interpretations. The companion universal
interpretation-category theorem makes this also the correct relative categorical
universal property, including transformations.

For a frozen original-core congruence `Q`, the exact cost is the restriction of
(6.6) to pairs of original terms: conservativity holds iff that restriction is `Q`.
This is complemented by a usable sufficient certificate, not used as a substitute
for a proof: exhibit one eligible interpretation whose original-profile kernel is
exactly `Q`. Soundness of saturation and that separation force conservation.
§5 supplies this with `Q=equality`; §7 supplies nontrivial `Q_H`; §8 proves that
other specified local relations make such a certificate impossible. The new
structural contexts may then force a strictly larger original kernel. Theorem 6.1
says that after a **complete** equipment is already present, an ordinary congruence
has those contexts and saturation contributes no further `L/U` equalities.

## 7. Explicit positive quotient families: local criteria, reconstruction, conservation

### 7.1 Activated coefficient forgetting

Choose a set `I` of allowed graphs such that

    G|U∈I  implies  G∈I.                                (7.1)

For finite `N`, this is a finite induced-subgraph test. For each active `G` and
span `S`, double its apex `S[2]` and add only the local section equation

    u_(s0)^G=u_(s1)^G,   s_i(e)=(e,i).                   (7.2)

Then the exact quotient normal form is

    (π,φ,m) ~ (π',φ',m')
      iff π=π', m=m', and [G∈I or φ=φ'].                (7.3)

**Proof.** (7.3) is a substitution congruence: an active child graph is an induced
subgraph of the retained output whole, so (7.1) makes that output active too.
Conversely, for parallel `φ,ψ:[p]→S`, define the square
`t:[p][2]→S` by `t(z,0)=φ(z)`, `t(z,1)=ψ(z)`, with the given fixed boundaries.
Precompose (7.2) at `[p]` by `d_m c_flat` and postcompose by `u_t`. The span category
tables produce exactly the desired equation between normal forms. Thus the local
section equations generate (7.3), not all true semantic equations by declaration.
Restriction (4.1) and contextual unit insertion are bijections retaining `G,π,m`;
therefore both directions respect (7.3). This proves the quotient is an equipment
and its local presentation is sound and complete. If (7.1) fails, two singleton
selectors at an active induced child, inserted in a binary cut of an inactive whole,
give distinct coefficient maps there: the proposed (7.3) is not substitution
stable. This proves necessity for this **specified graph-only forgetting family**,
not a classification of all possible quotient congruences. ∎

On original profiles the coefficient is already unique. Hence (7.3) preserves every
original cell and equality, including empty fibres, and (5.2) still holds. This is
a nontrivial quotient because general finite spans have genuinely different maps.
Its finite active-graph criterion is a local relation-level test for preservation
of restriction uniqueness and original-profile conservation.

### 7.2 Original scalar quotients and conservative free completion

Let `H≤M^×` be any subgroup, and add to the **original C5** presentation only

    D(W,h)=id_W   (h∈H, graph(W) nonempty).              (7.4)

The exact original kernel `Q_H` retains complete profiles and partitions, is scalar
`H`-orbit equality at nonempty output graphs, and is literal scalar equality at the
empty graph. KERNEL proves this from the original seven local equations. Within
graph-indexed scalar kernels it is precisely the family with original fixed-endpoint
refinement lifting; it is not a classification of every possible congruence.

In `V(N,M)` extend it by retaining the **actual** coefficient map and applying the
same scalar rule. Induced-subgraph closure makes this a substitution congruence,
and (4.1)/unit insertion retain graph/scalar and hence preserve the quotient both
ways. It is presented locally by (7.4) for every named nonempty horizontal of EXT.
Combining it with (7.2) gives the product normal-form rule: retain π, forget φ exactly
at active outputs, take scalar H-orbits exactly at nonempty outputs, and retain
empty-output scalars literally. The two local derivations act independently.
Original profile recovery is precisely `C/Q_H`, with no extra equality.

For the **C5-only free** virtual and ordinary envelopes, BRIDGE proves the stronger
separate statement

    V_free(C/Q_H) ≅ V_free(C)/⟨(7.4)⟩,
    O_free(C/Q_H) ≅ O_free(C)/⟨(7.4)⟩,                    (7.5)

with exact old kernel `Q_H` after every factor closure. The presentations on the two
sides have the same raw horizontal/cell grammar and relations. To prove old-kernel
reflection rather than merely (7.5), use the graph-word/span separator with vertex
grade `v(L)`. Its cells retain forest and coefficient, quotient scalars by H only
at positive grade, and retain scalars at grade zero. Restrictions preserve grade,
units have grade zero, and composites add grades; hence all universal bijections
descend. Its original profile fibre is exactly `C/Q_H`. This is the separation
certificate of §6.3, for **all finite interface maps**, not only invertible ones.
The interpretation-category isomorphisms, transformations and choice-change
comparisons in (7.5) are the companion free construction applied to the same old
equations. No claim that (7.4) at old horizontals generates every equation at new
horizontals is needed or made.

### 7.3 Decoration and genuine refinement information

Take `M={1,e,0}`, `e²=1`, `e0=0`, `0²=0`, and `H={1,e}`. This gives an unbounded
family in `N,K` with nontrivial quotient and noninvertible decoration. Before
quotient, unary `D_e` is invertible and `D_0` is not. An outer scalar `0` cannot be
refined to scalar `1`, since every refinement product remains `0`; an outer scalar
`1` refines to `0` by inserting a scalar-zero child. At empty outputs, in particular
nullary `D_m(U_A)`, all three scalar witnesses remain distinct even after free
completion and its quotient. At nonempty outputs only `1,e` become equal, and
fixed-endpoint representatives can be corrected by multiplying a nonempty child
by an H-element. Thus finite decoration changes actual factorization/refinement
information; it is not a redundant label on an otherwise thin model.

## 8. Genuine noninvariant relation test and the unavoidable conservativity cost

### 8.1 A substitution-compatible preequipment relation that fails lift uniqueness

Take a vertical category with a nonidentity arrow `f:A→B`. In a free unary VDC
preequipment give horizontals `P,R:A⇒A`, `T:B⇒B`, parallel globular cells
`a,b:P⇒R`, and `κ:R⇒T | f,f`. Adjoin the single parallel equation

    κa=κb.                                               (8.1)

Its ordinary VDC substitution-congruence quotient is legitimate. It still has
`a≠b`: no generator returns from T to R, so an expression of output R is built
from `a,b` and identities and cannot contain κ; the equation cannot be instantiated
in that fibre. This is also witnessed by the explicitly presented path category,
viewed as a unary-only VDC. Declaring κ cartesian in the subsequent relative
equipment construction forces `a=b` by (6.1). Thus (8.1) is compatible with ordinary
substitution but incompatible with the proposed *conservative* cartesian descent.
There was no claim that κ was cartesian in the preequipment. This is exactly the
level at which a noninvariant quotient can exist; Theorem 6.1 excludes calling it
a congruence quotient of an already complete equipment.

### 8.2 Original C5 cost with nontrivial cuts, not an explicit old equation

Choose distinct parallel original operations
`a,b:(H1,…,Hn)⇒W`, `n≥1`, all interfaces at an old object `o` with `F(o)=1`.
Choose nonempty finite sets `A0,…,An`. Before completion adjoin **fresh** horizontals
`Ri:A_(i−1)⇒Ai`, `T:A0⇒An`, prospective restriction cells
`χi:Ri⇒Hi`, `χ:T⇒W` with terminal-map boundaries, and new globular cells `x,y`
from `(R1,…,Rn)` to T. Add only

    χx=a[χ1,…,χn],    χy=b[χ1,…,χn],    x=y.             (8.2)

The preequipment presentation is old-profile conservative. No nonidentity generator
outputs any Ri. Hence any term outputting Ri has that same Ri leaf; any occurrence
of a new generator leaves an Ri occurrence in the frontier. No term or contextual
instance of (8.2) can have both entirely old frontier and old output. Consequently
all-old profiles contain precisely the original cells and original equations.
This argument includes original nullaries and repeats, because a nullary never
outputs an Ri. It uses names, not accidental equality of later semantic spans.

Now require the **existing** χi and χ to be cartesian. Choose coherent sections
`si:1→Ai` (one at each actual interface occurrence). Cartesian uniqueness produces
`βi:Hi⇒Ri | s_(i−1),si` with `χi βi=id_Hi`. Applying the ordinary return context

    r(z)=χ z[β1,…,βn]                                   (8.3)

to (8.2) gives

    r(x)=a[χiβi]=a,       r(y)=b[χiβi]=b,    so a=b.

Thus the saturated equality cost on original profiles is strictly larger than the
original equality congruence. Every eligible target interpretation forces it by
(8.3); no “saturation repair” preserving the requested old distinction exists.
This is not the trivial act of adding `a=b` as a declared old equation. The reference
preequipment conservativity was proved before the structural return contexts were
adjoined. The same calculation is a finite proof in the relative term syntax.

For an unbounded actual graph family take `G=K_(r,r)`, `r≥3`, its two ordered sides
`U,V`, and the distinct partitions `(U,V)` and `(V,U)`. Both source graphs are the
same edgeless r-vertex graph, so these are parallel **repeated-component** C5
witnesses of scalar 1 with nontrivial retained cross edges. Use `K=[2]` and `o=0`,
whose regular realization is a singleton. For every `N≥2r` and every internal
multiplicity `k≥2`, choose `A0=A2=1`, `A1=[k]`. A permutation of the middle coordinate
is invisible to the endpoint-projection coefficient of the terminal restrictions.
Therefore a proposed paired graph/permutation equality including those two
restricted cuts triggers (8.2) and forces their old partitions equal. Balanced or
surjective terminal maps do not prevent the obstruction. This is NOGO's exact
counterfamily and conservation target, not a larger claim against every quotient.

## 9. Mandatory tests and conclusion

The companion checks exercise: two explicitly different restriction/unit encodings
and their actual comparison maps; two composable interface changes; repeated equal
source occurrences; genuine nullaries with retained shared map and nonunit scalar;
finite decoration changing refinement/factorization; activated-section and scalar
quotient normal forms; exact original-profile reflection; and the preequipment
noninvariant equation with saturation return-context collapse. Their finite outputs
illustrate the general proofs and do not replace them.

The positive recovery theorem is (2.2)/(5.2), with the canonical conservative free
core comparison in §5.2 and nontrivial quotient extension in §7. The generic
obstruction and exact additional structural requirements are §§6/8: inverse-factor
compatibility (equivalently cancellation), adequate least saturation, and an
old-kernel separating interpretation; at complete fixed-sort equipment level
compatibility is automatic by the explicitly proved structural contexts. Neither
literal equality with the old core nor C5-only all-span generation is the target.
