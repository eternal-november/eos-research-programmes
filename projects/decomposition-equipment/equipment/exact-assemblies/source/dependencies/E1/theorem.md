# E1 — Marked virtual equipments, their 2-category, and the actual witnessed core

**Result first.** The axiom system below defines a classical marked virtual
equipment, its normal morphisms and cell-natural transformations, and proves
the strict 2-category laws. Its identity-boundary part is an actual typed
witness calculus, with the original occurrence-indexed refinement construction,
not a relation of reachability. Cartesian factorization works in every arity;
unit factorization works at every distinguished occurrence in every surrounding
context. Chosen universal structures have specified comparison maps satisfying
all finite coherence laws. Boundary- and incidence-compatible interface changes act coherently on all
cells; a concrete, finite-table-testable noninvertible class also preserves the
declared exact markings. None of this removes nonuniversal primitive witnesses.

**Evidence boundary.** This is the consolidated P source for **original E1
only**, contract lines 414–434, dated 31 October 2026. It reuses, and explicitly
credits, existing equipment and core proofs. The separately checked core-facing
L fragment is recorded in the companion formal evidence and source map. No E2
universal-presentation theorem, E3 acceptance, entire-workstream acceptance,
novelty claim, or amendment of the historical ledger is asserted here.

## 1. Sources, size, and precise conventions

The standard background is Cruttwell–Shulman, *A unified framework for
generalized multicategories*, Definitions 2.1, 3.1, 5.1, 7.1, 7.6 and Theorem
7.24 ([primary source](https://arxiv.org/pdf/0907.2460v3)). The standard baseline
is the virtual-double-category framework, its transformations, and universal
restriction/unit structure. In particular **normal means unit-preserving**;
cartesian preservation by functors between complete virtual equipments is
already Theorem 7.24, not a newly discovered additional independent property.

The principal existing proofs are:

* **SPAN:** `structural_extracted/GraphSpanModel.md`, §§2–6: actual graph/span/
  scalar cells, substitution including nullary vertical whiskering, all-arity
  restrictions, contextual units, and bijective original-profile comparison.
* **ENV:** `structural_extracted/proof/Conservative_Equipment_Envelope.md`,
  §§3–7,9: typed factor operations, contextual beta/eta equations,
  transformation extension, choice comparisons, and old-tuple conservation.
* **EXT:** `structural_extracted/proof/Extended_Local_Presentation.md`: the
  substantive enlarged local presentation. It is credited as existing E2-facing
  evidence, not reproved or promoted by this E1 document.
* **CUT:** `structural_extracted/proof/Global_Cut_Repair.md`, §§9–10: retained
  actual comparisons and the feasible-tuple unique-lift test, including the
  separate nullary condition and coherence at every actual subtree.
* **A/B:** the original `WitnessedDecompositions` API: `Calculus.lean`,
  `FreeExtension.lean`, `PresentedCalculus.lean`, `QuotientCalculus.lean`,
  `RawRefinement.lean`, `SemanticRefinement.lean`, `RefinementComparison.lean`,
  `RefinementFunctoriality.lean` and `RefinementLifting.lean`.
* **D1/D2/D3:** the completed 31 October theorem dossiers. We use D1's
  generator/equation and occurrence transport, and D2's distinction between
  existence of a relational lift and uniqueness of an actual span lift. D3's
  retained symmetry is compatible evidence, not a license to replace actual
  span maps by isomorphism classes.

The full paths, hashes and clause map are in `source_obligation_map.md`.

Work classically in sets in a fixed universe U, or in a set-sized collection
inside an ambient larger universe. The vertical category, horizontal families,
cell families and optional presentation are U-small. All paths and trees are
finite but their arities/depths are unbounded. Categories of these structures
live in the larger universe. The principal finite-set model uses a small full
category of tagged finite sets closed under the displayed tuple constructions;
actual tagged sets, not just cardinalities or isomorphism classes, are retained.

Vertical categories and VDC substitution are strict. Parenthesized finite
lists are identified only through their specified ordered flattening maps;
proofs of typing equalities are not additional witnesses. Cartesian restrictions
and horizontal units are **chosen but not split** unless explicitly said
otherwise. Nested pullback tuples need not be literally equal. All their
comparison isomorphisms are supplied below. No horizontal composite for every
path is assumed; that is the separate ordinary-equipment strengthening.

The chosen formulation needs no choice to select its universal data, since
these are inputs. Existence of a simultaneous choice of restrictions and units
for an unchosen small equipment uses the corresponding set-indexed axiom of
choice. Once such data are supplied, each universal factor is uniquely
determined, so its selection uses unique specification, not an arbitrary
choice. Finite explicit models need only the displayed formulas. The original
A3 set-quotient/Lean classical-choice conventions remain those recorded by A/B;
this document does not introduce a normalization or decidability assumption.

We write `βα` for first α then β, and `α[β_i]` for simultaneous substitution.
A horizontal arrow `H:A⇒B` is an actual component, not merely the pair `(A,B)`.
A path includes every intermediate interface and every occurrence, even if
several components are equal. The empty path `()_A` includes its interface A.

## 2. Complete axiom system

### 2.1 The unmarked underlying virtual double category

Give a small category V, a set `Hor(A,B)` for each pair of its objects, and,
for each path `p=(H_1,...,H_n):A_0⇒A_n`, output `K:B⇒C` and arrows
`f:A_0→B`, `g:A_n→C`, a set

    Cell(p;K | f,g).

A cell is an element of this set. The fibre need not be a proposition, a
singleton, or a set of universal cells. Parallel distinct elements remain
parallel distinct witnesses.

Give `1_H∈Cell((H);H | 1,1)`. For
`α∈Cell((H_1,...,H_n);K | f,g)`, give substitution by a row of cells

    β_i ∈ Cell(q_i;H_i | u_(i-1),u_i),
    u_i:C_i→A_i,     q_i:C_(i-1)⇒C_i,

where the right and left sides at each shared boundary are the **same** `u_i`.
The resulting cell is

    α[β_1,...,β_n] ∈ Cell(q_1...q_n;K | f u_0,g u_n).    (2.1)

For `n=0`, the row has no cells but still has **one arrow** `u:C→A_0`.
Its composite is written `α⟨u⟩`, with boundaries `fu,gu`. This is nullary
vertical whiskering. A general nullary α may have `f≠g`, and an empty inner
path `q_i` may have `u_(i-1)≠u_i`: they merely have the same domain. This data
must never be erased because a tuple of cells happens to be empty.

Require these equations, at every correctly typed instance:

* `α[1_Hi]=α`, with the identity boundary row; for n=0 this says `α⟨1⟩=α`.
* `1_K[α]=α`.
* Three-layer substitution is associative: substituting the bottom row into
  `α[β_i]` equals substituting into each `β_i` and then into α. The left side
  uses the ordered bijection from bottom slots to pairs `(i,j)`; its vertical
  boundaries are the corresponding composites. Empty blocks retain their
  interface maps. When the outer row is empty this includes
  `(α⟨u⟩)⟨v⟩=α⟨uv⟩`.

These are equations of actual cells, not only of source profiles or observed
outputs. These data and equations are the VDC axiom system used here.

### 2.2 All-arity cartesian restrictions

For every `K:B⇒C`, `f:A→B`, `g:D→C`, choose `K[f,g]:A⇒D` and a unary cell

    κ_(K;f,g) : K[f,g] ⇒ K | f,g.

For every path `p:X⇒Y`, every `u:X→A`, `v:Y→D`, require that

    κ ∘ - : Cell(p;K[f,g] | u,v)
             → Cell(p;K | fu,gv)                         (2.2)

is bijective. Denote its inverse by `L_(K;f,g;u,v)`. Its two equations are

    κ L(α)=α,                 L(κβ)=β.                  (2.3)

There is no positive-arity proviso. At arity zero p is `()_X` and u,v may
be different maps with common domain. There is no admissibility/marking
proviso either. Universality concerns **all** multicells in each fibre.

### 2.3 Contextual opcartesianness and units

A **globular** cell `e:p⇒H` has identity vertical boundaries. Call it
opcartesian if, for every composable prefix r and suffix s, every output K
and arbitrary outside boundaries f,g, substitution at the specified block p
is a bijection

    -[1_r,e,1_s] : Cell((r,H,s);K | f,g)
                   → Cell((r,p,s);K | f,g).             (2.4)

This definition quantifies over all arities of r and s, including zero; it is
not weak context-free opcartesianness. It makes no assertion about cells with
an empty horizontal **target**: every target here is one horizontal arrow.
Thus the present nullary-source cells are not the nullary-target cells of an
augmented virtual double category.

For each A choose `I_A:A⇒A` and `η_A:()_A⇒I_A | 1,1`, required to satisfy
(2.4). Write the inverse insertion map in a specified context as `U_(r,A,s)`.
Its equations are

    U(α)[1_r,η_A,1_s]=α,
    U(β[1_r,η_A,1_s])=β.                                (2.5)

No equation identifies an arbitrary nullary witness with η_A. No pre-existing
loop component is identified with I_A unless a comparison is proved.

A VDC with §2.2 and §2.3 is the chosen virtual equipment of this document.
These are its full structural axioms; all remaining structure is declared
extra witness-sensitive data, not concealed in the word “equipment”.

### 2.4 Admissibility, exactness, and optional presentation

An **admissible decomposition calculus** A is specified by an interface/
horizontal subquiver of the identity-boundary part of E and subsets

    A(p;H) ⊆ Cell(p;H | 1,1)

on its profiles, containing its unary identities and closed under every
occurrence-indexed substitution, including nullaries. The default is the
whole identity-boundary calculus. This is a restriction of admissibility,
not a restriction of the existence of ambient equipment cells. Optional
all-boundary admissibility may instead be supplied as a sub-VDC, but is not
needed for the core comparison.

Specify a marking `Ex_op(p;H)⊆A(p;H)` whose members satisfy (2.4). One may
mark all opcartesian cells in A or a smaller declared family. We do not
silently assume an arbitrary selected marking is closed under substitution;
when that closure is used it is part of the declared marking convention.
All opcartesian cells themselves are closed under substitution: each relevant
contextual substitution map is a composite of the bijections (2.4).

Other semantic marks may be supplied as separate named predicates on actual
cells. In the principal model we use `Ex_coeff` for actual bijective coefficient
maps with scalar 1. **Ex_coeff is not Ex_op** in the graph-span equipment:
assembly with two nonempty graph inputs can have a bijective coefficient map
without being universal. Keeping this distinction is necessary to reuse CUT
without changing the meaning of “opcartesian”.

Presentation data, when supplied, consist of the original typed signature Σ,
parallel equations R, A3's actual presented calculus `P=F(Σ)/≡_R`, and a strict
interpretation

    j:P → Core_A(E).                                    (2.6)

It is specified by actual primitive images in A that satisfy R; A2/A3 give
its extension, not an assumed quotient action. Each primitive may map to a
nonuniversal cell. A presentation does not mean “all semantic cells and all
true equations”, and no presentation is required to present all of E.
Refinement is derived from these actual cells by §7, not supplied by replacing
witnesses with a preorder. The bare core does not determine V, its nonidentity
arrows, the ambient horizontals/cells, or the restrictions and units: those
remain additional equipment data.

## 3. Universal factorization in arbitrary diagrams

### Theorem 3.1 — contextual laws

Cartesian lift (2.3) and unit insertion (2.5) work at every distinguished
occurrence in every finite well-typed substitution diagram. They are natural
under all legal substitutions, with the bridge κ or η retained in its proper
position; all finite compatible diagrams of these universal factors commute.

**Proof.** First, if a typed row β can be substituted into α, then

    L(α[β]) = L(α)[β].                                  (3.1)

The boundaries of L on the left are the composites of those on the right.
Postcomposing the right side with κ, associativity and (2.3) give α[β].
Injectivity in (2.2) proves (3.1). The same argument includes an empty outer
row: the row has its arrow u, and vertical associativity gives the boundaries.

At an internal node of any larger diagram replace α by `κ L(α)`. This is a
local equality of cells in exactly the same fibre, so substitution congruence
preserves the whole diagram. Conversely a local factor through κ is unique
**at that hole**, by (2.2). We do not infer that an arbitrary surrounding cell
is cancellative. Iterating from the leaves proves the cartesian statement for
all finite diagrams, including repeated components and empty subpaths.

For units, (2.5) gives existence and uniqueness at every specified junction
of every surrounding path. Substitute any further row in the other positions.
Associativity shows that deleting the distinguished η before or after that
substitution gives the same cell. Uniqueness in (2.4) equates the two inserted
factors. Several distinguished units are handled in their retained positions:
deleting them in either order gives the same shortened path and cell; repeated
use of injectivity in (2.4) gives equality of their insertion factors. This
also proves naturality when a surrounding context itself appears at an inner
node of a larger tree. Mixed cartesian/unit laws follow by first postcomposing
with the relevant κ's and then deleting the relevant η's, in any fixed order;
each operation is injective in the fibre where it is used. Both compared
expressions reduce to the identical fully expanded cell. QED.

This is a theorem about the specified universal bijections, not a claim that
all cells are invertible or that arbitrary nonuniversal substitution has a
unique inverse. SPAN §§4–5 and ENV §4 give concrete formulas/term beta–eta
proofs of precisely these all-arity and all-context axioms.

## 4. Normal morphisms, transformations, and every 2-category law

### 4.1 One-cells and the marking convention

A VDC functor `F:E→D` gives a functor on vertical categories, a function on
each horizontal family over that functor, and functions on **all** cell fibres
with the mapped full boundaries and profiles. It preserves 1_H and every
substitution (2.1), including nullary whiskering, as equalities.

It is **normal** when it preserves nullary opcartesian cells. Equivalently it
sends each chosen η_A to a universal nullary cell: any other universal unit is
uniquely isomorphic to a chosen one (§5), and functors preserve these inverse
unary comparisons. Normality is not literal equality `F(I_A)=I_(FA)`.
Cartesian preservation is part of the usable preservation statement; by
Cruttwell–Shulman Theorem 7.24 it follows already for VDC functors between
virtual equipments. It may redundantly be included in a record to expose the
comparison maps, but is not an extra theorem hypothesis here.

Our main marked 1-cells preserve the admissible subquiver, all admissible cells,
Ex_op and every additional named mark designated **preserved**. This does not
force preservation of unmarked non-nullary opcartesian cells; a normal functor
need not be strong. A **reflecting** variant additionally requires, on each
source cell, `Fα∈mark_D ⇒ α∈mark_E`; preservation plus reflection is explicitly
called both. A **forgetting** variant deletes a named marking and all its
conditions. We never silently change between these conventions. The default
in this theorem is preservation, not reflection.

Composition is function/functor composition on every datum. It preserves
identities and substitution, normality, and each declared marking. Reflection
also composes: reflected membership is pulled back first along G then F.
Identity morphisms satisfy every convention. Thus each fixed convention gives
a category of 1-cells.

### 4.2 Two-cells and naturality, including zero source arity

For normal marked `F,G:E→D`, a transformation `α:F⇒G` consists of:

* a natural transformation of vertical functors with arrows `α_A:FA→GA`;
* for each `H:A⇒B`, a unary cell
  `α_H:FH⇒GH | α_A,α_B`;
* for every `ξ:(H_1,...,H_n)⇒K | f,g`, the cell equation

    α_K [Fξ] = Gξ [α_H1,...,α_Hn].                     (4.1)

The boundaries of the two sides agree because
`α_B Ff = Gf α_A0` and similarly on the right. For n=0 the right side is
`Gξ⟨α_A0⟩`, not an unparameterized empty substitution. Thus (4.1) is also
the exact required compatibility for arbitrary nullary witnesses.

These are the standard cell-natural transformations. The main marked
2-category is **locally full**: transformation components need not themselves
be admissible or exact. This is a deliberate convention. A transformation is
not a function mapping cell fibres, so imposing preservation of marks on its
components would be a different restriction. It is especially inappropriate
to force all components to be universal and thereby discard valid witness
comparisons. No extra mark condition is hidden here.

### 4.3 Explicit compositions and laws

The identity transformation has components identity vertical arrows and 1_FH.
For `α:F⇒G`, `β:G⇒H`, put

    (β·α)_A=β_A α_A,       (β·α)_J=β_J[α_J].             (4.2)

Vertical naturality follows from that of α,β. For a cell ξ, expand the left
side of (4.1) for β·α, associate, apply α's equation then β's, and reassociate.
This proves its cell naturality, with the same retained arrow in the nullary
case. The unit/associativity laws for (4.2) are exactly the unary cases of the
VDC laws, pointwise at every component.

Whiskering is

    (Lα)_A=L(α_A),  (Lα)_J=L(α_J),
    (αR)_A=α_(RA),  (αR)_J=α_(RJ).                      (4.3)

Functorial preservation of substitution proves cell naturality and preservation
of identity/vertical composition by left whiskering; right whiskering follows
by evaluating (4.1) at Rξ. For `α:F⇒G:E→D` and `β:L⇒M:D→Z`, define

    β*α = (β G)·(Lα) = (Mα)·(β F).                     (4.4)

The equality of object components is vertical naturality of β at α_A. The
equality of horizontal components is (4.1) for β applied to the **unary cell**
α_J. Thus (4.4) is equality of transformations, not a new comparison 3-cell.

For completeness the remaining strict 2-category equations are:

    1_L * 1_F = 1_(LF);
    1_E and identity 2-cells are two-sided units;
    (γ*β)*α = γ*(β*α);
    (β'·β)*(α'·α) = (β'*α')·(β*α).                     (4.5)

The first two use identity preservation and (4.2). For associativity expand
both sides using `(βG)·(Lα)`: both become the same three whiskered components
in the same order, by strict functor composition and unary associativity. For
interchange expand the right side; move its middle pair past one another by
(4.4), and reassociate. This gives the left side. On objects this is ordinary
naturality in the vertical categories; on horizontals the move is precisely
the cell naturality just proved. It works for noninvertible components. Hence
all homs are categories, composition is a functor on hom categories, and its
associativity/units are strict. The marked objects and normal marked morphisms
therefore form the promised strict 2-category `MVEq`.

The same proof applies to the reflecting variants and to the forgetful
2-functors deleting marks, because identities/composites of their 1-cells
stay in those classes and all transformations remain allowed. Forgetting all
extra data gives the standard 2-category of normal virtual equipments. No
claim that the vertical category itself has only identity arrows is involved.

### 4.4 Optional presented-core packages

Let `Disc(P)` be the VDC whose horizontal cells are P and whose only vertical
arrows are identities. It is a VDC, not asserted to have all equipment units
or restrictions. A presentation package is an arrow `j:Disc(P)→E` as in (2.6).
A morphism `(h,F)` to `j':Disc(P')→E'` consists of a strict core map h and a
normal marked equipment map F such that `Fj=j'h`. One may specify h on
primitives by target presented terms; source relations must be derivable in
P', so A3 proves that h exists. The primitive assignment alone is not h until
that equation check passes.

A package 2-cell `(ρ,α):(h,F)⇒(k,G)` consists of a VDC transformation
`ρ:Disc(h)⇒Disc(k)` and an equipment transformation α satisfying

    α j = j' ρ.                                         (4.6)

Because the core vertical categories are discrete, ρ exists only with equal
interface functions, and its horizontal components are actual unary core
operations. Vertical and horizontal compositions are those of §4.3 in each
coordinate. Equation (4.6) is preserved under each composition by whiskering
and interchange; the identities satisfy it. Thus these packages too form a
strict 2-category (a specified sub-2-category of the arrow 2-category of VDCs).
The fibre with fixed P, h=id and ρ=id is the strict relative theory under the
original core. This makes presentation preservation explicit without making
an E2 claim that P universally generates the whole equipment.

## 5. Chosen and unchosen universals: actual comparisons and coherence

### 5.1 Cartesian comparison maps

Two cartesian cells `κ:R⇒K | f,g` and `κ':R'⇒K | f,g` determine unique
globular unary cells

    c:R⇒R',   d:R'⇒R,       κ'c=κ,     κd=κ'.           (5.1)

Indeed lift κ through κ', and conversely. Then `κ(dc)=κ` and `κ'(cd)=κ'`;
injectivity in (2.2) gives `dc=1_R`, `cd=1_R'`. This proves an actual inverse,
not only the existence of an unspecified isomorphism.

The composite of two cartesian cells is cartesian because its maps (2.2)
are composites of bijections at **every** arity and boundary. Consequently
identity and successive restriction choices have comparisons

    e_K:K[1,1] ≅ K,
    c_(f,g;u,v):K[f,g][u,v] ≅ K[fu,gv],                 (5.2)

characterized by

    κ_(fu,gv) c_(f,g;u,v) = κ_(f,g) κ_(u,v).

For three successive pairs, the two comparison composites have identical
postcomposition with the final κ: each is the same threefold composite of
cartesian cells. Injectivity gives their equality. Identity coherence follows
in the same way. The argument applies to any finite pasting, so it proves all
finite associativity/identity coherence, not only a named low-dimensional
pentagon. Naturality with cell substitution is Theorem 3.1.

### 5.2 Unit comparisons

If `η:()_A⇒I` and `η':()_A⇒I'` are universal, (2.4) with empty context gives
unique `u:I⇒I'` and `v:I'⇒I` satisfying

    uη=η',       vη'=η.                                (5.3)

Precomposing their composites with η,η' and using injectivity gives `vu=1`,
`uv=1`. The contextual property is stronger: substituting u at any occurrence
maps cells with I' in that source position to cells with I there, and is
exactly the composite “delete η', insert η” of (2.5). For three choices,
the direct and two-step comparison have the same precomposition with η, hence
are equal. Several occurrences commute by §3. These equations explicitly
compare arbitrary choices without identifying their horizontal objects.

### 5.3 Normal functors and transformations respect these comparisons

For normal F the canonical isomorphisms are characterized by

    r_F:F(K[f,g]) ≅ (FK)[Ff,Fg],
    κ_(FK;Ff,Fg) r_F = Fκ_(K;f,g),

    u_F:F(I_A) ≅ I_(FA),
    u_F Fη_A = η_(FA).                                 (5.4)

The first uses cartesian preservation and (5.1), the second normality and
(5.3). For composable normal F,G their comparison isomorphisms satisfy

    r_(GF) = r_G G(r_F),       u_(GF)=u_G G(u_F),         (5.5)

where r_G is evaluated at FK,Ff,Fg and u_G at FA. Postcompose the first with
its final κ, or precompose the second with GFη, and both sides agree by functor
preservation of substitution. Universal injectivity proves the equalities.
Identity functors give the identity comparisons relative to identical choices.
Equations (5.2) and (5.5) are compatible for exactly the same reason.

For a transformation α:F⇒G, its naturality at κ and η gives

    Gκ α_(K[f,g]) = α_K Fκ,
    α_(I_A) Fη_A = Gη_A⟨α_A⟩.                          (5.6)

These equations uniquely determine the corresponding restricted/unit
components once the other indicated data are given. Substituting (5.4)
therefore gives compatibility with every choice comparison. This is the same
universal-factor mechanism already used in ENV §§6–7; no invertibility of
α_A or α_H is assumed.

### 5.4 Exact level of chosen/unchosen comparison

Let `ChMVEq_coh` have chosen objects and normal marked functors with the
canonical comparisons (5.4), not demanded literal equality of chosen
horizontal objects. Its transformations are §4.2. Forgetting choices induces
an **isomorphism on every hom category**, since (5.4) exists uniquely for each
underlying functor and (5.6) is automatic. Every unchosen small equipment
admits a chosen lift under the set-indexed choice assumption in §1. Thus this
forgetful 2-functor is a biequivalence (on the declared universe-sized catalogue).
For two choices on the *same* marked E the identity underlying functor in each
direction, with (5.1) and (5.3), supplies inverse comparisons; all their
composition laws follow from those displayed equations.

The marking predicates on the underlying cells have not changed in this
statement. Neither the unary comparison c nor u is required to lie in an
arbitrary selected mark. If one moves an admissible subquiver or marking to
**different horizontal representatives**, its transport must be defined by
conjugation with these comparisons, or iso-invariance must be supplied and
checked. Mere substitution closure of A does not imply stability under an
unmarked isomorphism. The concrete comparisons in §9 preserve its marks by
their actual scalar-1 bijective formulas.

There is also a stricter chosen convention, in which F sends chosen I,κ,η
literally to the chosen target data. It is a sub-2-category but we do **not**
assert that every coherent functor between arbitrary fixed marked equipments
can be strictified in this way. ENV proves a separate strictification/
interpretation equivalence for its **free term source**; that existing scoped
result is not silently generalized here.

## 6. The full and admissible globular cores

### Theorem 6.1 — core extraction and the presented comparison

For every E, let its component quiver have E's objects and all its horizontal
arrows. Define the total operation set at a component H by

    Op_H = Σ_(p:source(H)⇒target(H)) Cell(p;H | 1,1).      (6.1)

Its profile is the retained p. Identity is `(H,1_H)`. Substitution takes the
independently supplied cell at **each occurrence** of p and applies (2.1) with
the identity boundary row. This defines the original A1-style lawful calculus
`Core(E)`. Restricting components and cell sets to A gives `Core_A(E)`.

**Proof.** Typing of (2.1) gives the actual expanded full profile. The identity
and associativity laws of §2.1, with all boundary arrows identities, are exactly
`Calc.subst_identity`, `Calc.identity_subst`, and `Calc.subst_assoc`. The slot
bijection is the original ordered occurrence expansion, including repeated and
nullary components. For A, identities and closure in §2.4 make all these
operations land in A. No proof is lost by totalization: fixing the profile
recovers the original cell fibre as A1's `Collection.fiberTotalizeEquiv`.
A2 extends primitive images; A3 factors through R precisely when those equations
hold. This is (2.6). QED.

A normal marked F induces a base-changing strict map `Core(F)`, and its
restriction `Core_A(F)`, by mapping the full profile and cell. It preserves
identity and substitution because F does. Identities/composites map identically.
Thus extraction is a functor on objects and 1-cells. The package square in
§4.4 becomes an actual commuting square of these maps.

**The 2-dimensional boundary is important.** A general α has nonidentity
vertical sides α_A,α_B. Its α_H is not a globular core operation, so extraction
is **not** a 2-functor from all of MVEq to plain fixed-boundary multicategories.
On the sub-2-category with fixed interface functions and identity vertical
components it does send transformations to ordinary core transformations.
For the admissible core one must additionally require those unary components
to lie in A. Alternatively one can keep the full charted boundary data of §8;
that is a different, explicitly indexed target, not the fixed-boundary Calc
API. No ordinary-core 2-functor is claimed for general α.

### 6.2 Exact abstract image and limits

For an interpreted presented core j the image in a full fibre is exactly

    Im(j)_(H;p) = { j([t]) : [t]∈P(H;p) }.              (6.2)

Equivalently it is the **source-typed, named** substitution/identity closure
of the declared primitive images, with identifications induced by R and any
further equalities actually true in E on the same original full profile. If j
identifies interface or component names, unrestricted target grafts can join
source-incompatible colors and need not belong to (6.2); we do not include them. It is contained in A, not necessarily in Ex_op. Equality of image
cells need not imply derivability of the corresponding equation in P.
Likewise A may contain cells not generated by those images. This is a precise
image description and a limitation, not an assertion of automatic fullness
or conservativity.

If j is fibrewise injective, it identifies P with this image calculus on its
**retained source names**. It identifies an ordinary embedded image subcalculus
of Core(E) when the interface/component maps are injective as well. If it is fibrewise bijective on a specified full component/profile
subquiver, it gives the stronger full recovery there. The principal model has
this property on **original profiles** by §9.2. The free envelope V of ENV has
proved original equality conservation, not an assertion that every new cell
on an old profile is old. These are three different conclusions:

1. abstract image (6.2), always;
2. full original-profile recovery in the concrete semantic model, proved;
3. conservative original-core inclusion in the free envelope, existing scoped
   evidence, without a blanket fullness claim.

## 7. Actual occurrence-refinement comparison, not endpoint reachability

For a lawful core C and a fixed output W, let `Ref_C(W)` have all its operations
`a:p⇒W` as objects. An arrow from `a:p⇒W` to `b:q⇒W` consists of an actual
occurrence-indexed tuple

    (β_i:q_i⇒H_i)_(i∈Slot(p)),
    q = q_1...q_n,             b = a[β_i].              (7.1)

The source's original slot i, each whole H_i, each complete q_i and each β_i
are retained. Profile equality and the final equation are proof-only
constraints; they do **not** quotient the tuple. For empty p there is one empty
family with its prescribed interface; for repeated H_i the entries remain
independent. The corresponding forest category omits a,b and the final equation
and has paths as objects. This is exactly the direction of the original
`RefinementForest.Arrow` and `SemanticRefinement.Arrow` API.

Identity is the tuple of unary identities. Composition substitutes the second
tuple into each β_i using the consecutive subblock of slots belonging to q_i.
The identity laws hold at every tuple entry by the calculus unit laws.
Associativity at every entry is calculus associativity plus the canonical
ordered bijection between triple occurrence indices. Thus these are categories.
This is A/B's already-proved construction; no new reachability relation is
substituted for its arrows. B1's raw tree category maps to it by the existing
A2 evaluation map and B2 comparison.

### Theorem 7.1 — functor, exact image, and reflection/fullness criteria

A strict interpreted core map j induces a functor

    Ref(j):Ref_P(W) → Ref_Core(E)(jW)                   (7.2)

by sending a to ja and the actual tuple `(β_i)` to `(jβ_i)`. Its image arrows
are precisely those tuples admitting a simultaneously typed source tuple
β with the root equation (7.1); every entry then lies in (6.2). Without
faithfulness of j, entrywise membership in (6.2) alone need not force the
root equation for chosen source objects. With fibrewise injectivity it suffices
only after the lifts are required to
have the **exact prescribed original block profiles**, so their substituted
root and b occupy the same original fibre. Membership in an unindexed union
of image fibres is not sufficient if colors are identified.

**Proof.** The root equation is preserved by substitution preservation. A tuple
of identities maps to a tuple of identities, and composition is preserved at
every original occurrence by `j(β_i[γ_ij])=jβ_i[jγ_ij]`. These are equality of
whole tuples, the original `mapArrow_id`/`mapArrow_comp` laws. If j is fibrewise
injective, equality of image tuples first gives equality of each mapped
entry profile, hence equality of its length. Since both original arrows have
the same fixed target full profile q, equal block lengths cut q into the same
original consecutive blocks, including the same empty-block boundaries. Thus
corresponding original entries lie in the same original fibre even if j
identifies colors. Fibrewise injectivity then gives equality of each entry,
so (7.2) is faithful. Given lifts of entries, the ambient root equation reads
`j(b)=j(a[β_i])`; injectivity on that full fibre gives (7.1). QED.

For **full original-profile recovery**, assume the interface and component
maps are injective and each original full operation fibre maps bijectively to
its ambient fibre. An ambient arrow between two original image operations
has a retained ordered block decomposition of the target original profile.
Each block consists of original components; its endpoints are original because
the interface map is injective, including empty blocks. Each tuple entry
therefore has an original full profile and a unique lift. The preceding root
argument proves the lifts form an arrow. Consequently (7.2) is fully faithful
and identifies the original category with the full subcategory on its image
objects **when profiles/entries are restricted as just specified**. The same
entrywise proof gives the forest comparison. This is the genuine B2-style
fibre criterion, not a deduction from equality of composite root operations.

For an admissible calculus replace Core(E) by Core_A(E). For a selected
unital, substitution-closed exact marking, the same construction restricts to
exact refinement arrows and the same proof applies when j preserves that marking.
If a selected mark omits identities or is not closed, its marked arrows are a
class of arrows,
not automatically a subcategory. This qualification also applies to semantic
“exact” predicates imported from other dossiers.

Package composition in §4.4 sends these tuple maps to their composites because
it does so entrywise; its comparison square commutes on objects **and entire
retained tuples**. D1's equivariant generator/equation transports fit this
construction directly. Nothing erases its stabilizers or parallel witnesses.

## 8. Coherent interface reindexing exists before any marking theorem

### 8.1 All-cell reindexing along compatible squares

Take `ξ:p=(H_i)⇒K | f,g`, input interface changes `u_i:A'_i→A_i`, output
changes `v:B'→B`, `w:C'→C`, and new outside boundaries f',g' satisfying

    f u_0=v f',             g u_n=w g'.                 (8.1)

Set `H'_i=H_i[u_(i-1),u_i]`, `K'=K[v,w]`. Define `Rξ` to be the unique
cartesian lift through κ_K of

    ξ[κ_H1,...,κ_Hn],                                    (8.2)

with boundaries f',g'. For n=0 use `ξ⟨u_0⟩`; u_0 is one source change,
while f',g' and the old f,g remain independently allowed. Equations (8.1)
are exactly the typing hypotheses of (2.2), so this operation exists for
**every** such square, with no exactness/admissibility hypothesis.

For an incidence-compatible substitution diagram assign one map at each
identified interface occurrence and one chosen restriction at each identified
horizontal occurrence. Applying R to the flattened diagram equals composing
the reindexed node cells. Postcompose with the root κ and use (8.2) at each
node; VDC associativity produces the identical unreindexed diagram with its
leaf κ-row. Cartesian injectivity proves equality. Induction on the tree
includes every nullary node. This is the all-tree coherence argument, not
merely a binary endpoint check.

For two successive interface changes, (5.2) identifies the twice restricted
horizontals with the once restricted composite. Conjugate the twice reindexed
cell by these unary comparisons at its output and inverse comparisons at
its inputs. Postcomposition with the final κ gives the same expression (8.2)
using the composite vertical maps. Hence it equals the once reindexed cell.
The identity and three-change laws follow from (5.2) and injectivity. This
proves a coherent action, without pretending the cleavage is split.

### 8.2 Fixed named frames and the original core API

To express this as an ordinary core map, retain a fixed quiver of **names** Q.
A frame assigns an actual interface A_x to each named vertex and an actual
horizontal H_c to each named component. Its calculus uses actual globular E
cells on those named profiles. A family `u_x:A'_x→A_x` produces the restricted
frame H'_c and a strict, fixed-Q calculus map `R_u` by (8.2) with outside
identities. It preserves identities and substitution by §8.1, and hence gives
the actual forest/refinement functors of §7. It never identifies equal names
or repeated occurrences. Independently charted local interface changes use
the incidence-compatible diagram version, not an invented global Q map.

The comparison from a nested restriction frame to its flattened composite
frame acts on a cell α by

    c_out α[c_in,1^(-1),...,c_in,n^(-1)].                 (8.3)

Its inverse uses the inverse c's. These are strict calculus isomorphisms;
substitution cancels the adjacent c^(-1)c at every internal occurrence.
Equations (5.2) give the identity/cocycle laws and §7 gives the same laws on
complete refinement tuples. This explains precisely how coherent chosen
restriction action connects to the original fixed-base Calc API.

### 8.3 What marks do, and do not, follow

Nothing in (2.2) implies that R_u maps A into A or preserves Ex_op. A changed
horizontal may even leave the specified admissible subquiver. The entire
ambient equipment and the all-cell action remain available in that case.
An **eligible marked change** must first land in the declared admissible
horizontal class and preserve the declared predicates. This abstract
condition alone is not our checkability theorem: §9.3 supplies a finite-table
criterion for a substantive noninvertible parameter class.

For a presented admissible subcalculus one practical independent certificate
is: give admissible target terms for the reindexed primitive images, verify
source equations become derivable target equations, and verify the declared
marking generators/rules and choice comparisons. A2/A3/D1 then extend the
map and its occurrence-refinement action. If a mark is generated by specified
substitution rules, checking their preservation suffices; for an arbitrary
unstructured predicate there is no theorem that finite generator checks can
verify all its members. Changes of representatives require the iso-stability
qualification in §5.4. This prevents a vacuous marking convention from being
mistaken for a computable preservation result.

## 9. Principal reused model, marking certificate, and original image

### 9.1 The actual graph/span/scalar model and its declared marks

Fix N≥0 and a finite commutative monoid M, written multiplicatively. SPAN's
`V(N,M)` has finite tagged interfaces and all functions vertically. Its
horizontal components are actual pairs

    H=(G, A ←[l] E [r]→ B),

with an ordered graph G on at most N vertices and an actual finite span apex
E. Components with the same endpoints are not identified. For a path p retain
its full compatible tuple set

    P(p)={(a_0,e_1,a_1,...,e_n,a_n):
           l_i(e_i)=a_(i-1), r_i(e_i)=a_i};
    P(()_A)=A.                                         (9.1)

A cell `p⇒H | f,g` is an ordered partition U of the retained whole graph G
into its specified induced input graphs, an actual function `φ:P(p)→E` with
`lφ=fπ_0`, `rφ=gπ_n`, and one global m∈M. All three coordinates participate
in equality. Substitution lifts each child's partition through the parent's
increasing subset enumeration, evaluates the child tuple maps and then the
parent map, and multiplies all vertex scalars. The induced-restriction identity,
flat ordered tuples and commutativity of M prove associativity. This is SPAN
§§2–3, including every empty inner path and nullary common vertical arrow.

Its chosen restriction of H along f:A'→A,g:B'→B has unchanged graph and apex

    E[f,g]={(a',e,b'):f(a')=l(e), g(b')=r(e)}.            (9.2)

The cartesian cell selects e and has scalar 1. The lift of `(U,φ,m)` in any
arity is `(U, z↦(uπ_0(z),φ(z),vπ_n(z)),m)`. The first and last coordinates
are forced by the boundaries and the middle by factorization, proving both
inverse laws, not merely an endpoint relabeling. The chosen unit is the empty
graph with identity span on A, and η_A has map id_A and scalar 1. Removing it
in a context removes its forced empty graph block and repeated equal endpoint
coordinates; its inverse inserts them and leaves the scalar unchanged. These
are SPAN Theorems 4.1 and 5.1, already establishing the full equipment axioms.

Take A to be the full globular calculus (or a stated full subquiver slice).
Define the following **different** marks:

    Ex_coeff: φ is bijective and m=1;
    Ex_op^0:  Ex_coeff and at most one input graph is nonempty.   (9.3)

The ordered partition then forces all other graph blocks to be empty. Both
marks are checkable from the finite cell data and are substitution-closed.
For Ex_coeff, the map from the expanded tuple set to the tuple of child apex
witnesses is bijective when all child maps are, with inverse obtained by each
child's endpoint-preserving inverse; composing with the outer bijection proves
closure. For Ex_op^0, at most one nonempty child can lie below the outer's sole
possible nonempty input, and below that child at most one remains. Scalars
remain 1. Unary identities and chosen η belong to Ex_op^0.

**Lemma 9.1.** Every Ex_op^0 cell is genuinely contextual opcartesian.

**Proof.** In any surrounding graph partition, replacing its source block by
its output graph deletes its specified empty input blocks and retains the one
possible nonempty block. Inverse insertion is forced, even when adjacent
components repeat. On the span coordinate, its endpoint-preserving bijection
φ replaces exactly its subpath tuple by an apex witness; the inverse replaces
that witness by φ^(-1). These are inverse operations on the complete tuple
set in the surrounding context and hence on all maps out of that set. The
scalar is unchanged since m=1. Thus contextual substitution is bijective on
the whole cell fibre for every surrounding context and outside boundaries.
This proves (2.4). QED.

Thus (9.3) is a concrete declared Ex_op marking. It need not exhaust all
universal cells: replacing scalar 1 by any invertible scalar gives another
universal cell, with scalar-adjusted inverse factorization, but need not be
selected by this normalized marking. Conversely Ex_coeff alone does not imply
opcartesianness: SPAN §7 proves the cross-edge obstruction when two input
graphs are nonempty in the full graph family. The coefficient-only “exact”
cut cells in CUT retain precisely this distinction. No graph assembly has
been silently made universal by its bijective coefficient map.

### 9.2 Exact original-profile and original-refinement recovery

For a finite category K, SPAN §6 uses the faithful regular realization

    F(A)={(A,C,t):t:C→A in K},
    F(h)(A,C,t)=(B,C,ht),                               (9.4)

with distinct tags for distinct objects. Evaluating F(h) at `(A,A,id_A)` proves
faithfulness. Send an original component `(G,h:A→B)` to

    J(G,h)=(G, graph-span(Fh)),
    graph-span(Fh)=(F(A) ←[id] F(A) [Fh]→ F(B)).         (9.5)

These horizontal components retain the whole graph and the actual old arrow.
For every original full path p, the tuple projection
`π_0:P(Jp)→F(A_0)` is bijective: starting at its first coordinate, each graph
span forces every later coordinate. A globular cell into J(G,h) must have
`φ=π_0` by its left endpoint equation. Its right endpoint equation is exactly

    F(h)=F(h_n...h_1), hence h=h_n...h_1.                (9.6)

Its remaining data are the original actual ordered partition of G and the
original scalar m. Therefore J is bijective on **every original complete
operation fibre**, in arbitrary arity. For n=0 the partition forces G empty
and (9.6) forces h=id_A; there are exactly the original scalar-labelled
nullaries, not an extra unit conflation. Increasing lifts and scalar products
are exactly original substitution. This recovers the original graph-and-arrow
calculus, not just its endpoint support relation.

The declared admissible image is all of these original-profile cells, inside
the full globular A. It includes ordinary nonuniversal cuts and all original
scalars, not just (9.3). Its component/profile description is explicit: whole
ordered graphs, tagged regular K interfaces, and graph spans of actual K
arrows. J is injective on interfaces/components, so Theorem 7.1 gives the
actual full original-profile occurrence-refinement comparison: every tuple
entry lifts uniquely and tuple equality is reflected. Raw/free evaluation is
the inherited B1/B2 functor followed by J. Neither equal assembled wholes nor
equal total scalar products identify different tuples.

This section **imports** SPAN's existing theorem and identifies its precise
role in E1. ENV §9's free-envelope equality conservation is a different
result; no new full-envelope-image theorem is claimed here. The nontrivial
C5 local presentation used there is retained; EXT is not replaced by an
all-cells tautological presentation.

### 9.3 A finite-table-testable, composition-stable marking-preserving class

For changes `f_i:A'_i→A_i` along a positive path p there is an actual comparison

    c_f:P(H_1[f_0,f_1],...,H_n[f_(n-1),f_n])
          → P(p)[f_0,f_n].                             (9.7)

It forgets only the chosen lifts of internal interface coordinates. Over an
old feasible tuple z with specified lifted exterior endpoints, its fibre is

    ∏_(0<i<n) f_i^(-1)(a_i(z)).                         (9.8)

In particular, empty feasible support causes no failure, and at unary arity
the internal product is the singleton empty tuple. For n=0 the comparison is
instead

    A' → A'×_A A',             x↦(x,x),                 (9.9)

which is bijective exactly when f:A'→A is injective. Formula (9.9) is **not**
obtained by treating (9.8) as an empty product with no endpoint condition.

Call a finite incidence-compatible diagram change **UL-certified** when:

1. at each positive node/run needed by the diagram, for every feasible old
   tuple with its chosen exterior lifts, the product (9.8) has cardinality 1;
2. each arity-zero node at which exact-mark preservation is asserted uses an
   injective interface map, not only occurrences of the specifically chosen
   η (every marked nullary here is itself a universal unit);
3. every intermediate run is tested on the actual child/composite spans
   occurring there, not only on the original adjacent primitive pairs.

This is a finite calculation on leg tables, map tables, occurrence lists and
finite tuple sets. It is not the statement “assume the comparison is an
isomorphism” in disguise: (9.8) supplies the independent fibre computation
and identifies exactly which values of each map must have unique preimages.
CUT §10 proves this formula and the necessity of testing actual composite
nodes; D2 §6 retains the difference from mere relational existence.

**Theorem 9.2.** Every compatible finite map change acts on all cells. A
UL-certified change additionally preserves Ex_coeff and Ex_op^0 at all tested
nodes, and acts coherently on the corresponding marked diagrams and actual
occurrence-refinement tuples. The class is closed under composable certified
changes, with the second certificate evaluated on the already changed diagram.

**Proof.** In the concrete model, §8's reindexed coefficient map is

    φ_new = (endpoint pullback of φ) ∘ c_f.              (9.10)

Its graph partition and scalar are unchanged. This formula is defined even
when c_f is not invertible. If φ is bijective its endpoint pullback is
bijective. Conditions (9.8)–(9.9) say exactly that c_f is bijective, including
zero arity. Thus (9.10) is bijective and scalar 1 remains 1, proving Ex_coeff
preservation. The graph condition in Ex_op^0 is unchanged, so Lemma 9.1 gives
preservation of the declared genuine opcartesian marking.

For successive f and h the two comparisons, after the canonical restriction
coordinate deletions, satisfy

    c_(fh) = (endpoint pullback of c_f) ∘ c_h.           (9.11)

Both sides send an actually lifted tuple to the same original tuple and its
outermost endpoint lifts; the omitted intermediate coordinates are forced by
h. Pullback preserves a bijection, so successive certificates give a
certificate for fh. In arity zero this is also the ordinary fact that a
composite of injections is injective. Identities are certified. The analogous
three-change equation is literal deletion of the same intermediate coordinates.
The graph/scalar coordinates are unchanged, so all comparisons commute as
actual maps of witnesses. Applying the same argument at every actual tree
node proves compatibility with flattening, grafting and arbitrary finite
composition. The occurrence tuple is retained throughout, and §7 proves the
refinement functor equations entrywise. QED.

**Noninvertible positive family.** For each interface choose a subset S_A⊆A
that is an object of the selected finite-set vertical category, and its inclusion. Allow horizontals whose span legs land in the selected
subsets, together with the identity spans I_A, and arbitrary graph/scalar
data on these components. Any positive-path tuple with lifted exterior
endpoints has all its internal coordinates in the subsets: supported spans
force them there and identity spans propagate equality. Inclusions give
unique preimages; nullaries satisfy injectivity. Thus the entire generated
finite-diagram class is UL-certified, including unit insertions. Proper
inclusions, e.g. `{0,1}↪{0,1,2}` with actual nonempty supported spans, are
noninvertible examples. Successive eligible subset changes compose by (9.11).
This is not a ban on nonconstructive witnesses: arbitrary maps φ and arbitrary
nonunit scalars still define legitimate admissible cells and reindex by
(9.10). Only the separate universal/exact-mark preservation assertion is
restricted.

**Necessary caution.** A surjective noninjective change can preserve a
positive relational composite while duplicating actual span witnesses; it can
also destroy (9.9). Therefore D2's relational existence criterion is not
substituted for (9.8). An inverse in a quotient that forgot actual parallel
maps is not an actual bijection and does not certify this theorem. This is
consistent with D3's retained-symmetry distinction.

### 9.4 Explicit required tests in one family

Take terminal endpoint set 1 and empty graphs; take M={1,z} with z absorbing
and z≠1. Let H have singleton apex and K have two-element apex, both with the
unique legs to 1.

* H and K are distinct horizontal components between the same interfaces.
  The two functions `1→{0,1}` give distinct parallel cells `H⇒K` of scalar 1.
  They are legitimate and admissible. Neither is universal: for the function
  selecting 0, postcomposition with id_K and with the constant-0 self-map of
  K gives the same composite but distinct factors; use constant 1 for the
  other cell. Thus uniqueness fails already in empty context.
* The nullary cell into the identity span on 1 with scalar z is not universal:
  substitution multiplies every factor scalar by z and cannot yield scalar 1.
  The chosen η has scalar 1. Nullaries into K can independently select either
  apex element; they are not declared equal to η or to each other.
* The nonidentity map `f:{0,1}→1` has a cartesian restriction of every H and K,
  with apex (9.2), regardless of markings. Reindexing η produces the diagonal
  `2→2×2`, not a bijection, so genuine exact marking is not preserved by this
  arbitrary restriction.
* Compose f with `h:{0,1,2}→{0,1}`, `h(0)=h(1)=0`, `h(2)=1`.
  The twice restricted identity span has apex
  `(a'',(h(a''),*,h(b'')),b'')`; the once restricted one has apex
  `(a'',*,b'')`. Deleting/inserting the forced h-coordinates gives inverse
  maps. Both ways of reindexing any cell give the same φ on these flattened
  tuples. This tests two genuinely nonidentity composable changes, without
  falsely claiming either preserves universal units.
* Independently, the proper-inclusion support family of §9.3 supplies two
  composable noninvertible **mark-preserving** changes. These test the positive
  theorem, not only its counterexample boundary.

All these cells exist inside the already-proved SPAN construction. The examples
are diagnostics for the abstract conventions; no amount of finite testing
replaces the universal proofs above.

## 10. The core-facing checked slice: scalar-decorated relations

The L fragment uses the following second, deliberately delimited model family rather
than pretending to mechanize all of GraphSpan or the entire 2-category.
Interfaces are sets (the worked examples finite); horizontal components are
actual binary relations. For a path p let C(p) be its relational composite,
with `C(()_A)=Δ_A`. For boundaries f,g, a cell into R is

    (n, proof that C(p)(x,y) ⇒ R(fx,gy)),     n∈Nat.      (10.1)

The proof is a truth constraint, not witness multiplicity; the independent
natural number n is retained **actual witness data**. Parallel cells of
weights 0 and 1 differ. This is the product of the containment relation model
with the commutative additive scalar calculus; it is not an assertion that
relations retain their existential witnesses as actual span apices.

Substitution sends each existential intermediate realization to its image
under the shared boundary maps and has weight `n+Σ_i n_i`. Identity has weight
0. Associativity follows because both associations use the same relational
witness image and sum the same finite tree-vertex weights; commutativity of
addition handles independent-slot regrouping. A nullary row is still its
vertical arrow u and has zero added weight, so §2.1 holds in all cases.

Restriction of R along f,g is its inverse image
`R[f,g](x',y')↔R(fx',gy')`. Its cartesian cell has weight 0. In every arity
factoring a cell through it leaves the number unchanged and is the logical
rewriting of the displayed predicate. Both composition/factor inverse laws
therefore hold. The unit is Δ_A with nullary weight 0. In any context,
relational composition with Δ_A inserts or removes the forced equal junction
coordinate, and substitution adds 0. This is a bijection of actual cell sets,
with inverse retaining the weight. Thus this too is a genuine virtual
equipment, including nonglobular cells and contextual universal units.

### Theorem 10.1 — exact mark in this model

A globular cell `(p⇒R,n)` is contextual opcartesian iff

    C(p)=R  and  n=0.                                   (10.2)

**Proof.** If (10.2) holds, replacing p by R inside any context leaves the
composite relation unchanged and the scalar weight unchanged; the same
containment predicate and n-factor define inverse substitution maps.
Conversely the weight-0 cell `p⇒C(p)` exists. Context-free factorization
through the proposed universal cell requires a cell `R⇒C(p)` with weight k
such that `n+k=0`. Thus n=0 and `R⊆C(p)`. The original cell already gives
`C(p)⊆R`, proving equality. This necessity used only a special context; the
sufficiency proved every context. QED.

Take A to be all globular cells and Ex_op to be (10.2). All maps give the
all-cell reindexing of §8. Boundary bijections preserve and reflect (10.2):
they lift each internal relational realization uniquely and preserve the
nullary diagonal; the scalar is unchanged. Identity and two-change laws are
the inverse-image/equivalence composition equations, including each actual
occurrence. D2 gives broader, precisely qualified noninvertible relational
families, but they are not assumed in this L statement.

### Theorem 10.2 — original exact-core image and its separate forgetful kernel

The original C2 exact relation calculus maps into this decorated core by
keeping the full profile/equality predicate and assigning scalar 0. This is a
strict `Calc.Hom`: identity has weight 0, and substitution sums only zeros.
Its image is exactly (10.2), since each marked cell has that same profile,
weight 0, and exact relation equality. It is injective on total operations
(the original equality proofs are proof-irrelevant), and Theorem 7.1 gives
faithfulness on the original B2 complete refinement tuples. In contrast the
strict map to C2's containment calculus that forgets n has kernel, at a fixed
output, exactly equality of profiles: every valid scalar-labelled cell on
that profile maps to its unique containment operation. Hence it deliberately
identifies parallel scalars but the equipment/core inclusion does not.
These are `exactLift`, `marked_image`, `exactLift_injective`,
`exactRefinement_faithful` and `forgetScalar_kernel` in the checked source.
They exhibit both an actual retained-witness comparison and an explicitly
nonfaithful forgetful one rather than conflating the two.

The companion `formal/E1RelationEquipment.lean` constructs this **specific**
core from totalized globular relation-equipment cells, proves the restriction
composition/factor inverse laws, proves contextual unit/opcartesian statements,
and links its strict witness maps to the original `Calc`, free interpretation
and B2 occurrence-refinement API. Its named signature using available cells
is a core-facing comparison device, not a claimed local-generators E2
presentation. Its finite examples retain repeated slots, parallel weight
witnesses, nonuniversal nullaries, nonidentity changes and a coherent
bijective-action slice. Exact declarations, clean-run receipt, axiom closures
and any scope qualifications belong to the separate formal source map/evidence;
this paragraph is not a claim that all of §§2–9 is mechanized. In particular,
Lean `precompose` accepts the semantic relation map and scalar of a substitution
row; constructing every arbitrary nonglobular row and proving the full VDC/
2-category laws is the P proof, not an unreported Lean implementation.

## 11. E1 conclusion and explicit nonclaims

The construction is a full classical virtual-equipment axiom system, not just
an interpretation into Rel/Span. Sections 2–5 include all fibres, general
boundaries, universals, normal morphisms, transformations, both compositions,
interchange and all 2-category laws. Sections 6–7 locate the full/admissible
core and the original actual refinement categories, with image and faithfulness
hypotheses stated separately. Sections 8–9 give a computable positive
mark-preserving class with coherent action and retain all unmarked witnesses.
Section 10 identifies the exact genuinely equipment-derived original-API
fragment whose L evidence is supplied separately.

This does **not** assert that every path is representable, every witness is
universal, every restriction preserves a mark, every normal functor preserves
all non-nullary opcartesian cells, every equipment presentation is conservative,
or every general 2-cell is globular. Chosen strictness is not silently forced.
The original full E2/E3/E4/E5 and global acceptance statuses are not decided by
this E1 theorem. The source map records inherited results and new consolidation
without presenting standard equipment infrastructure as a novelty claim.
