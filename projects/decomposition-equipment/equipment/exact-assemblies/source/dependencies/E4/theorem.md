# E4 Ordinary equipment representability and conservative completion

31 October 2026. Uniform P proof for original contract E4, lines 466–482.

**Result.** For every `N≥6`, nonempty finite category `K`, and finite commutative
monoid `M`, the actual free chosen virtual equipment `V(C;B)` on the original
C5 local presentation has a universal ordinary completion

    j:V(C;B) → O(C;B).

The input is genuinely nonrepresentable: an invariant of its own cell syntax,
not an inference from preservation by a normal functor, excludes a composite
of two nonempty old graph components. The output has actual all-context
universal composites of every finite path. A binary formal composite is not
isomorphic to any horizontal in the image of V. No object or vertical arrow
of the retained interface category B changes. Every original C5 full-profile
witness equality, distinct whole up to unary globular isomorphism, and complete
occurrence-indexed refinement tuple is preserved and reflected at the precise
original-core scope in §7. **Full faithfulness of `V→O` on all added V cells is
not asserted.**

The universal property is an isomorphism of categories of chosen-strict maps,
and an equivalence for strong maps out of O versus normal maps out of V;
all cell-natural transformations are included. Normal means unit-preserving,
not preservation of arbitrary nonnullary opcartesian cells. Associators and
unitors satisfy pentagon and triangle by cancellation through the actual
universal cells. The representability criteria and failure boundaries below
separate a conservative completion from constructions that erase witnesses,
identify wholes, or impose incompatible universal markings.

**Source credit and evidence scope.** ENV already constructs the chosen term
ordinary envelope, its contextual factor laws, transformation extension,
coherence, and graph-word separator. This proof uses those results explicitly
and closes the E4 source-nonrepresentability, relative-completion, and
information-boundary obligations. Accepted E1 supplies the axiom system; E2
supplies the original local-presentation interpretation and its careful normal
versus strong convention; E3 supplies the substantive graph-cut/span model
classification. This is not a new general theorem of pseudo double category
coherence, an all-span generation claim for C5, or an E5 result. The finite C
certificates and independent audit are separate evidence. No additional Lean
formalization is claimed by this P document.

## 1 Inputs and the retained information

Use the original C5 local presentation `C=C(N,K,M)`, with its binary
whole-labelled cuts, old nullaries, unary scalars, and exactly the seven local
rule forms `R,UL,UR,D0,DA,DL,DR`. Its accepted normal-form comparison identifies
an old operation with its entire ordered graph partition, full component/grade
path, retained output whole, and one global scalar in M. It does not replace
this local presentation by all semantic cells and all true equations.

The small vertical category B is a full category of actual tagged finite sets
and all functions, closed under the finite tuple/pullback constructions. It is
retained input. Original interfaces and arrows enter through

    F(A)={(A,D,t): t:D→A in K},
    F(h)(A,D,t)=(B,D,ht),   h:A→B.                       (1.1)

Distinct interface names have disjoint tagged representatives. Evaluation at
`(A,A,id_A)` shows F faithful. F need not be full. The original noninvertible
arrows are not inverted by passing to B: if F(h) is bijective, a preimage of
`id_B` gives t with ht=id_B, and injectivity applied at id_A gives th=id_A.
Thus F reflects vertical isomorphisms as well as equality.

All horizontal paths retain their intermediate interfaces, repeated positions,
and empty positions. A cell sort is `Cell(p;H | f,g)`. For an empty source,
the source interface and both f,g remain specified; they need not be equal.
A substitution row retains its entire shared vertical-arrow family, including
one arrow when the outer source is empty. Equality compares actual witnesses,
not merely their existence. The size and classical-choice conventions are E1's.

Our preservation predicate `Pres_C` on a comparison into an equipment means:

1. it retains the original interface and vertical-arrow embedding (and in our
   construction retains all of B literally);
2. original horizontal names remain distinct, and original horizontals become
   unary-globular-isomorphic only when they already were so in C;
3. for every **fixed original full profile**, the function on original cells
   is injective and preserves substitution, hence reflects equality of two
   original cells and the original equations they satisfy;
4. complete old refinement tuples, with every child profile and occurrence
   retained, are compared entrywise; their equalities and original refinement
   compatibility equations are preserved and reflected.

There is no assertion of surjectivity onto all new cells with old profiles,
no deletion of whole labels, no replacement of tuples by their flattened
root, and no declaration that every old cut is universal. The globular
original C5 core is not itself being called a full virtual equipment.

## 2 Actual representability and checkable criteria

For a path p:A⇒B and a globular cell `μ:p⇒H`, define for every prefix r,
suffix s, output T and outside boundaries a,b the substitution function

    μ*: Cell((r,H,s);T | a,b) → Cell((r,p,s);T | a,b).
                                                               (2.1)

It substitutes μ at the indicated occurrence and identities elsewhere.
The cell is contextually opcartesian precisely when every (2.1) is bijective.
An ordinary equipment is a full virtual equipment in which such a cell exists
for every finite path, including the empty path. A formal path name by itself
establishes none of these bijections.

**Presentation certificate.** In a locally presented theory, a sufficient
checkable certificate for proposed composites is a uniformly typed factor
operation on terms `Q_(r,p,s)`, respecting the presentation congruence, together
with derivations, for every legal parameter, of

    Q(α)[1_r,μ,1_s]=α,
    Q(β[1_r,μ,1_s])=β.                                 (2.2)

The proof is simply that Q and (2.1) are inverse on the actual quotient cell
sets. These are finite rule forms with arbitrary finite path parameters, not
bounded-depth testing. Conversely actual chosen composites supply the unique
Q functions and both laws; to claim a certificate *in an unchanged local
presentation*, those functions must already be given on its cells or realized
by well-defined terms, not created by silently quotienting additional equations.
Section 4 constructs a new presentation that actually supplies them.

**Substantive model criterion from E3.** In the full ordered-graph families
`G(N,K_groupoid,M)` and `S(N,M)` (single graph plus actual finite span), write
s(p) for the number of nonempty input graphs. Then

    p has a contextual composite ⇔ s(p)≤1.             (2.3)

For a given globular assembly, universality is equivalent to `s(p)≤1` and
unit scalar in G; in S it additionally requires bijectivity of its actual
coefficient `P(p)→E_target`. These are direct graph/count, finite-function and
finite-monoid tests. E3 §7 proves the entire criterion in arbitrary contexts:
if at most one graph is nonempty, merge/split its unique nonempty block and
compress/expand the stored span tuple; if two are nonempty, competing cross
edges force different possible whole graphs, while a unary factor forces the
same graph. If the total vertex count exceeds N, no output cell exists at all.
Consequently, for nonempty groupoid K, these full model families are ordinary
on all finite paths iff `N=0`. They remain virtual equipments for every N.
This is an unchanged-horizontal-universe criterion, not a redefinition that
replaces a missing whole by its leaves.

**Rel and Span regressions.** Over any chosen small finite-set universe, Span
has actual finite spans and endpoint-compatible maps from the compatible-tuple
span P(p). Its composite is P(p), with the identity tuple map; compressing an
arbitrary consecutive substring of a larger tuple to its stored subtuple, and
expanding it again, are inverse endpoint-preserving bijections. This proves
(2.1) for all contexts, not merely associativity of pullback names. Units are
diagonal spans and restrictions are endpoint pullbacks. For Rel, the composite
relation contains `(a,b)` exactly when a compatible intermediate tuple exists.
The condition for a cell into a target relation is unchanged when an existential
substring is compressed or expanded; its fibres are propositions, so existence
and uniqueness give (2.1). Units are diagonal relations and restrictions are
inverse images. The identity maps of these already representable equipments
are information-preserving no-extension regression cases. We do **not** claim
that their identities satisfy §5's free normal-to-strong completion property
against arbitrary normal maps; no such assertion follows from representability.

## 3 The genuinely nonrepresentable positive input

The selected input is the actual free chosen envelope `V=V(C;B)` of E2 and
ENV, not the concrete single-graph model S. Its horizontals are the finite
expressions

    H ::= old W | I_A | R(H;f,g),                        (3.1)

with their typed endpoints and with **no horizontal equations**. Its cells
are generated by the old local witnesses, identities, full VDC substitution,
chosen restriction cells κ, fresh unit cells η, and factors L and U; their
quotient equations are the old local laws, VDC laws and the R/U inverse laws
listed in §4. E2 proves that this is a full virtual equipment. In particular
I_A is fresh; the old component `(empty,id_A)` is not silently identified with
it or declared to be a universal unit of V.

### Lemma 3.1 Graph-cut existence invariant of the actual syntax

Assign a single graph to every V horizontal by

    γ(old(G,h))=G,   γ(I_A)=empty,   γ(R(H;f,g))=γ(H).
                                                               (3.2)

If `Cell((H_1,…,H_n);H | f,g)` in V is inhabited, then there exists an ordered
partition `(U_1,…,U_n)` of the entire vertex set of γ(H), with
`γ(H)|U_i=γ(H_i)`. In particular an inhabited unary cell forces its two
graph grades to be equal, and an inhabited nullary cell has empty target graph.

**Proof.** Induct on a raw representative's finite formation tree. An old
witness has its given graph partition; an identity or κ has the full singleton
block; η has the empty partition of the empty graph. Substitution lifts each
child block through the increasing enumeration of its parent block; the induced
restriction identity `(G|U)|V=G|i_U(V)` proves the required graph. L changes
only the restricted target name, not its γ, and keeps the witness. U inserts
one empty block at its specified source occurrence. Nullary vertical whiskering
changes no graphs or blocks. These are all constructors of V. Every quotient
cell has a raw representative of the same full sort, so existence follows.
Only this sort-level existence invariant is needed: there is no assumption
that a chosen graph partition is a normal form for all V cells. ∎

### Theorem 3.2 The selected input has no composite of a genuine old path

Choose any A in nonempty K. Let `X=(one vertex,id_A)` and `p=(X,X)` at F(A).
There are old scalar-one cells from p to `W⁰=(edgeless two vertices,id_A)`
and `W¹=(one-edge two vertices,id_A)`, using blocks `({0},{1})`. Their
images are actual cells of V. If `μ:p⇒H` were even weakly opcartesian,
factorization with no surrounding context would produce unary cells
`H⇒W⁰` and `H⇒W¹`. Lemma 3.1 forces `γ(H)=G⁰=G¹`, a contradiction.
Hence V is genuinely nonrepresentable for every parameter triple in §1.

This proof ranges over **all** V horizontals, including arbitrarily iterated
restrictions and fresh units. It does not infer source nonrepresentability
from a normal functor into a nonrepresentable model: such functors need not
preserve an arbitrary composite. The same invariant proves the principal
six-vertex path in §9 nonrepresentable. ∎

The argument itself works for N≥2; the stated positive theorem keeps N≥6 to
stay within the inherited original-presentation test range without expanding
its historical acceptance. No claim about the N=0 free syntax is needed.

## 4 Construction of the ordinary envelope and its genuine universal cells

Construct O directly from the same original local presentation, retaining B,
by the finite horizontal grammar

    H ::= old W | I_A | R(H;f,g) | Comp(H_1,…,H_n), n≥1. (4.1)

The empty composite at A is I_A. A singleton Comp may be a fresh name too.
Restrictions are allowed on every new expression and composites on every new
finite path. This inductive set is small; no bound is imposed on nesting or
arity. There are no type equations.

The cell grammar contains the V constructors over this larger horizontal
universe, plus a globular cell `μ_p:p⇒Comp(p)` for each nonempty p and a
factor `Q_(r,p,s)(α)` whenever α has source `(r,p,s)`; the factor has source
`(r,Comp(p),s)`, the same target and the same outside boundaries. More explicitly,
the original restriction and unit factors have types

    L_(H;f,g;u,v)(α):p⇒R(H;f,g) | u,v
       when α:p⇒H | fu,gv,
    U_(r,A,s)(α):(r,I_A,s)⇒T | a,b
       when α:(r,s)⇒T | a,b.

Quotient by the least **parallel constructor congruence** containing the old
seven local rule forms, the complete VDC identity/associativity laws, and

    κ L(α)=α,                    L(κ β)=β;               (R)
    U(α)[1_r,η_A,1_s]=α,
    U(β[1_r,η_A,1_s])=β;                                 (U)
    Q(α)[1_r,μ_p,1_s]=α,
    Q(β[1_r,μ_p,1_s])=β.                                 (Q)

Every equation retains its complete sort and displayed parameters, including
all boundary arrows and all occurrences. Congruence closure includes L,U,Q.
Finite terms and set quotients suffice; no termination or normal-form result
for O is assumed. The construction is ENV §§2–4, not a name-only path category.

### Theorem 4.1 O is an ordinary equipment

Substitution is well-defined by congruence closure and satisfies the VDC laws.
Postcomposition with κ at every source arity and boundary factorization is
inverse to L by (R), so all restrictions are cartesian. Insertion of η at any
source occurrence is inverse to U by (U), so all chosen nullaries are contextual
units. Insertion of μ_p in any surrounding path is inverse to Q by (Q), so
every nonempty path has a contextual composite. The empty case is already U.
The laws hold on the actual cell quotients and for arbitrary targets and
outside boundaries. Thus O is genuinely representable on every finite path.

The inclusion of horizontal and cell constructors induces
`j:V→O`: all V equations hold in O, and the chosen V restrictions and units
remain literally chosen there. It is normal and chosen-strict for that
structure. It is not claimed to preserve every other opcartesian cell that
V might possess. Both V and O have exactly the same B objects and arrows. ∎

## 5 The relative categorical universal property

For a chosen ordinary equipment E write:

* `Hom_ch(V,UE)` for functors literally preserving the chosen restrictions and
  units, with no requirement to preserve arbitrary nonnullary composites;
* `Hom_ch^comp(O,E)` for functors also literally preserving the chosen finite
  composites and their universal cells.

Both categories have **all E1 cell-natural transformations** as arrows, with
no invertibility or strict-choice restriction on their components. UE forgets
the composite choices, not any cells or horizontals. The vertical functor B→E_v
may vary, or one may take the fibre with a specified vertical realization.

### Theorem 5.1 Relative chosen completion

Precomposition with j is an isomorphism of categories

    j*: Hom_ch^comp(O,E) ≅ Hom_ch(V,UE).                 (5.1)

**Objects and inverse.** Given F on V, restrict it to the old local C5 data.
Evaluate (4.1) recursively in E using its chosen units, restrictions and finite
composites. Evaluate κ,η,μ by the chosen universal cells and L,U,Q by their
unique actual factors. Every relation is valid because it is either an old
interpreted equation, a VDC law, or one of the inverse laws of the universal
bijections. This gives an extension `F̄:O→E`. On the V grammar it is exactly
F by E2's term induction. Conversely an extension's values are forced on
horizontal terms and universal cells; universality forces its factor values.
Induction on cells proves uniqueness, so restriction and extension are literal
inverses on functors.

**Transformations.** Given `τ:F⇒G` on V, extend over O horizontals. At a new
restriction and unit the forced formulas are

    Gκ τ_R = τ_H Fκ,
    τ_I Fη = Gη⟨τ_A⟩;                                  (5.2)

vertical naturality gives the boundary factorization in the first, and the
retained common component τ_A gives nullary whiskering in the second. At a
composite the forced equation is

    τ_Comp(p) F̄μ_p = Ḡμ_p[τ_H1,…,τ_Hn].                (5.3)

The right side has source Fp, so the actual universal cell F̄μ_p gives a unique
factor with outside components τ at the endpoints. Internal vertical τ
components remain in the row; they need not be identities or invertible.

Naturality holds for the old generators because τ was given on V; for κ,η,μ
it is (5.2)–(5.3). It is preserved by identities and full substitution, including
the empty-row vertical naturality case. For L, postcompose the proposed equation
with Gκ and use (R) and naturality of its argument; cartesian injectivity
proves the equation. For U, insert Fη at its actual occurrence and use (U)
and argument naturality; contextual unit injectivity proves it. For Q use
F̄μ in the same way and (Q). This proves naturality for every cell term.
The same equations force every component, so the extension is unique.
Identity and composite transformations agree with their extended counterparts
on V and hence everywhere by uniqueness. Thus (5.1) is a category isomorphism,
not merely existence of an extension on objects. ∎

### Corollary 5.2 Unchosen strong and normal convention

Let `Hom_str(O,E)` have functors preserving **all** contextual opcartesian
cells (hence normal) and let `Hom_n(V,UE)` have normal functors. Then

    j*: Hom_str(O,E) ≃ Hom_n(V,UE).                     (5.4)

To prove this, choose structures. E1/Cruttwell–Shulman Theorem 7.24 says that
functors between complete virtual equipments preserve cartesian cells. For a
normal F on V, E2's recursive restriction/unit comparisons strictify F to a
chosen-strict functor, with an invertible cell-natural comparison determined by
its old horizontal components. Apply (5.1). For a strong map on O the same
construction also uses unique comparison isomorphisms for its composite images.
Its strictification is therefore chosen-composite-preserving. Comparisons and
all transformations extend by (5.2)–(5.3); inverse comparisons and their cocycle
laws follow from uniqueness after cancellation through the same universal cells.
This proves full faithfulness and essential surjectivity of (5.4).

Preserving all chosen composites implies preserving every opcartesian cell:
an arbitrary such cell with source p is the chosen μ_p followed by its unique
invertible unary comparison. Conversely strong preservation supplies precisely
the comparisons just used. Thus the left convention is substantive, whereas
the right is only normal. The category isomorphism is natural in target maps preserving all chosen
restrictions, units and composites literally. The equivalence is pseudonatural
in strong target maps in the unchosen case; the comparison
for a composite target map equals the iterated comparison by the same unique
factorization. No strict unchosen 2-adjunction or preservation of arbitrary
extra exact markings is silently asserted.

## 6 Associators unitors and all finite coherence

For any finite parenthesization t of a path p, including inserted unit nodes,
let H_t be its iterated chosen composite and let `e_t:p⇒H_t` be the substituted
μ/η tree. A composite of contextual universal cells is contextual universal:
its substitution functions are composites of the bijections (2.1). This proof
includes empty nodes and arbitrary surrounding paths.

For two trees t,u on the same flattened path there is a unique globular cell

    c_(t,u):H_t⇒H_u,     c_(t,u)e_t=e_u.                 (6.1)

The reverse factor satisfies `c_(u,t)c_(t,u)=id` after precomposing with e_t,
and universality cancels e_t; likewise in the other direction. Moreover

    c_(u,v)c_(t,u)=c_(t,v),   c_(t,t)=id,                (6.2)

because both sides have the same composite with e_t. Define the binary
associator from `Comp(Comp(H,K),L)` to `Comp(H,Comp(K,L))` by (6.1).
Define the left and right unitors by the same formula comparing the μ/η tree
with `id_H:H⇒H`; singleton composite comparison is included.

For a composable row of unary cells `α_i:H_i⇒K_i` with its entire shared
vertical-boundary family, horizontal composition is the unique factor satisfying

    (⊗_i α_i) μ_(H_1,…,H_n) = μ_(K_1,…,K_n)[α_1,…,α_n].
                                                               (6.3)

It retains the row's outside vertical boundaries; shared internal boundaries
are not discarded before forming the right side. Identity and interchange
follow by inserting μ and using VDC identity/associativity; uniqueness proves equality before insertion. Naturality
of associators/unitors follows by expanding the same row through the relevant
e_t on both sides. Every route around the pentagon is c between the same two
four-leaf trees by (6.2), so the pentagon commutes. Both routes around the
triangle are c between the same two unit-containing trees, so it commutes.
The identical argument proves all finite rebracketing/unit coherence. Together
with the already proved cartesian restrictions, this gives the coherent ordinary
pseudo double equipment, not merely a list of unrelated representing objects.
This is the concrete universal-cell proof behind the standard representability
theorem; no novelty is claimed for that theorem.

## 7 Independent ordinary separation and original information conservation

We use ENV §§8–10's ordinary semantic equipment `W(N,M;B)`. Its graph component
is the **unnormalized** planar monoidal envelope of the bare graph-cut
multicategory. An object is a finite word of ordered graphs, with empty graph
entries allowed. A morphism `L→T` consists of a weak consecutive allocation of
input occurrences to output roots, and for each root an actual graph-cut witness
from its allocated run to that output graph. A zero-input root is allowed exactly
for an empty output graph. Composition substitutes these ordered forests with
all allocations retained; tensor concatenates words and forests. The unit is
the empty word `[]`, not the one-entry word `[empty]`.

A horizontal of W is `(L,S)` with a graph word L and an actual finite span S.
A multicell consists of (i) a forest from the concatenated source words to the
output word; (ii) an endpoint-compatible map from the actual source tuple span
to the output span; and (iii) one global scalar m in M. Composition is forest
substitution, actual tuple-map substitution and multiplication of all scalars.
These are actual independent coordinates of equality, including when the tuple
set is empty. Commutativity of M verifies simultaneous substitution associativity.

Restriction leaves L unchanged and pulls back S; its unique factor appends the
forced boundary coordinates, retains the forest and retains m. Unit is
`([],diagonal_A)`; factorization inserts/deletes its forced identity coordinate
and changes no forest. Composite of a path concatenates its graph words and
stores its compatible source tuple as the new span apex. The universal cell has
identity forest, identity tuple coefficient and scalar 1. In **every surrounding
context**, expanding/compressing this stored substring tuple is an endpoint-
preserving bijection, concatenated input graph words are literally the same,
and the scalar is unchanged. These are explicit inverse factor functions,
so W is a chosen ordinary equipment. It is not assumed to be the free O.

Interpret an old `(G,h)` by `([G],ΓF(h))`, where
`ΓF(h)=(FA←id FA→F(h) FB)`. An old cut maps to its one-root forest, the uniquely
forced tuple map and its actual m. Local C5 equations hold by actual forest
substitution and scalar multiplication; therefore §5 supplies a chosen strong
interpretation `Ev:O→W`.

### Lemma 7.1 Full original-profile semantic recovery

For every original globular full profile `(p;W)`, this semantic comparison is a
bijection on cells. Indeed, the tuple path of graph spans has exactly one
compatible tuple for every `x∈F(A_0)`; the left output identity leg forces the
coefficient to be its starting projection π_0. The right leg permits it exactly
when `F(h)=F(h_n…h_1)`, equivalently `h=h_n…h_1`. The forest to the one-entry
output word is exactly one ordered graph partition of the retained whole,
with the given occurrences, including empty entries. Its remaining coordinate
is precisely m. At arity zero, the forest forces G empty and the span equation
forces h=id; these are exactly the original nullaries. Substitution agrees
coordinate by coordinate with C5's accepted original normal form. ∎

### Theorem 7.2 Original-core conservation

The canonical old-core map `C→Core(O)` satisfies `Pres_C`; consequently the
comparison `V→O` preserves the designated embedded original information.

For old parallel cells a,b, equality of their images in O implies equality
under Ev, which by Lemma 7.1 implies a=b in C. The converse is preservation.
This proves reflection on **every original profile**, not only the principal
fixture or scalar-one witnesses. It also proves the same reflection for the
old image inside V by applying j. The semantic bijection does not imply that
all arbitrary new O or V terms in an old profile are themselves old.

A forest has a monotone occurrence-allocation function from input positions to
output roots. Composition composes these functions. An invertible forest must
induce a monotone bijection, hence have equal input/output word lengths and
identity allocation. Each root then has one input, whose unary graph cut forces
equality of the ordered graphs. Conversely these identity forests are invertible.
Thus a unary globular isomorphism between two old images forces equal graphs.
An endpoint-preserving isomorphism between graph spans ΓF(h),ΓF(k) has apex
map forced by the identity left legs to be identity; the right legs then force
F(h)=F(k), hence h=k. With tagged interfaces, no distinct original whole can
become isomorphic. An old scalar can become invertible only if it was a unit
of M, since semantic invertibility must invert the scalar coordinate; its old
inverse then already exists.

An original refinement arrow is an actual occurrence-indexed tuple `(t_i)`
of old cells satisfying its original equation `a[t_i]=b`. Entrywise equality
reflection proves that two such image tuples agree iff every old entry agrees.
The compatibility equation is preserved by substitution and reflected because
both sides are old cells in one fixed full profile. Tuple composition is the
same entrywise substitution. Thus the old refinement category maps faithfully,
with every original equation and tuple coordinate retained. No claim of
fullness onto new ambient refinement arrows is made. ∎

### Corollary 7.3 The added composite is genuinely new

For the two-singleton path p of Theorem 3.2, `Ev(Comp(p))` has graph word of
length two. Every horizontal from V has word length zero or one under Ev:
old names have length one, I has zero, and restriction preserves the word.
The forest-isomorphism argument above excludes an isomorphism between lengths
two and at most one. Therefore `Comp(p)` is not unary-globular-isomorphic to
**any** j(H), not merely a syntactically fresh expression. No old whole was
selected, reconstructed from its leaves, or made into this universal composite.

There is an important boundary: the assignment from the concrete single-graph
model S to graph words `G↦[G]` sends its actual unit `(empty,diagonal)` to
`([empty],diagonal)`, not to `([],diagonal)`. It is not normal, so it is **not**
the claimed completion of S. The positive input V has a fresh true unit I,
whose image is the empty word, and old empty-graph names stay distinct. This
is why no extra universal marking from S was imported into the C5-only input.

## 8 Sharp obstruction and information-loss boundaries

### Proposition 8.1 Unchanged horizontals with full cell recovery

Suppose D is a nonrepresentable virtual equipment and `T:D→E` is a comparison
fixing its object, vertical-arrow and horizontal-arrow universe, bijective on
every complete boundary cell fibre, and preserving substitution. Then E cannot
be ordinary. A universal E-cell μ lifts to a D-cell by surjectivity. For every
surrounding context its substitution map is conjugate, through the two fibre
bijections, to the bijective substitution map in E. Hence it is universal in
D, contradicting nonrepresentability. This applies to both E3 single-graph
models and to the selected input V.

The hypothesis is deliberately **full cell recovery**, not equality reflection
alone. With new cells allowed, declaring one old whole a composite could add
unary factors from it to other old wholes without equating those wholes. We
therefore do not claim that *every* equality-conservative completion must add
horizontals. Theorem 7.3 proves that this universal construction really does.

### Proposition 8.2 Additional universal declarations can force witness loss

Let `M={1,e,0}`, `e²=1`, with 0 absorbing. In C choose any old whole W. The
parallel unary scalar cells `d_1≠d_e` remain distinct in V and O by §7. The
old scalar-zero unary `d_0` satisfies

    d_1 d_0 = d_e d_0.

If a further completion requires this **specified** cell d_0 to become
opcartesian, injectivity of its context-free substitution map forces
`d_1=d_e`. No comparison satisfying `Pres_C` can meet that extra declaration.
More generally any distinct scalar a,b and m with am=bm yields the same
obstruction for a specified scalar-m assembly. It is an exact cancellation
cost, not a failure to find a clever horizontal name.

Similarly, if both old cells `w⁰:p⇒W⁰` and `w¹:p⇒W¹` of Theorem 3.2 are
required to be universal, unique factorization gives inverse unary cells
between W⁰ and W¹. That violates old-whole isomorphism reflection in Pres_C.
Declaring only one of them universal does not by itself prove a collapse;
this obstruction has exactly the two-marking hypothesis stated. Thus the
unmarked C5 positive class cannot be upgraded indiscriminately to “every old
assembly is exact.”

### Proposition 8.3 Actual bad ordinary targets

Forgetting the graph word/forest and scalar in W gives the ordinary span
equipment, preserving its chosen units, restrictions and composites. Composing
this map with `Ev:O→W` is a genuine strong map into an ordinary equipment,
but not an information-preserving completion: W⁰ and W¹ of equal grade map
to the same graph span, different old ordered cuts on a fixed whole map to
the same forced span coefficient, and d_1,d_e map to the same span identity.
Thus it destroys wholes and parallel witnesses while still landing in a
representable target. Mere representability of the target is insufficient.

A narrower bad comparison uses the unital monoid quotient `M→{1}`. Interpret
C's scalar generators by 1 in `O(C(N,K,{1});B)` and keep the original graph
and grade names. The relative property extends it to a strong ordinary map.
It preserves whole labels but identifies d_1 and d_e, so it fails the fixed-M
witness requirement. By contrast the identity monoid map is faithful; the
completion in §§4–7 retains every scalar. The exact distinction is the kernel
on the specified old full-profile fibres, not whether the new object is called
an envelope or whether all its paths have formal names.

For a proposed further relation/universal-mark extension, this gives a precise
presentation boundary: form its typed congruence including the required inverse
factor laws. Original equality conservation holds iff its restriction to each
old full profile is the original equality. A separating ordinary interpretation
injective on those profiles is a sufficient certificate; §7 supplies one for
the positive class. The scalar example gives an explicit unavoidable nontrivial
kernel, while the two-whole example gives unavoidable old-object isomorphism
loss. This is a criterion and proved obstruction, not an algorithm claimed to
decide arbitrary presented congruence equality.

## 9 The retained principal graph path and required tests

Take the original principal graph fixture with N=6, and realize its three-
interface path in the finite groupoid K with objects 0,1,2 and arrows
`(i,j,σ)`, σ∈S_3, composed by `(j,k,τ)(i,j,σ)=(i,k,τσ)`. Set
`a=(0,1,(012))`, `b=(1,2,(01))`, and `M={1,e,0}` as in §8. The faithful functor
from the original chain `0→1→2` sending its generators to a,b preserves this
entire original path profile; it does not retroactively invert chain arrows.
This is also the nontrivial groupoid interface realization used in the finite
C certificate. The actual ordered six-vertex graphs are

    E(G⁰)={01,12,13,24,34,45},   E(G¹)=E(G⁰)∪{05},
    U=({0},{1,3},{2,4},{5}),
    grades=(a,id_1,id_1,b),      output grade=ba.         (9.1)

The two middle inputs are literally the same two-vertex one-edge component,
but occupy different positions. Both whole graphs receive the same input
profile and the displayed partition, yet differ in the retained edge 05.
There are separate scalar-1,e,0 cells in each profile. Lemma 3.1 rules out any
V-horizontal representing this path: its universal factorization to both
wholes would force the two whole graphs equal. The new `Comp(p)` has a
four-entry word under Ev and factors every O-cell from that path uniquely in
every source context by Q. It is not one of the original whole graphs.

The old parallel refinement tuples

    (1,1,1,1),     (1,e,e,1)                             (9.2)

of unary scalar cells both stabilize the scalar-one old witness because their
products are 1, but differ at both repeated middle occurrences. Theorem 7.2
retains their difference in O. They collapse under the bad scalar quotient.
Properly refining the second middle graph by `({0},{1})` and the third by
`({1},{0})` gives the actual flattened partition

    ({0},{1},{3},{4},{2},{5}),                           (9.3)

so equality cannot replace occurrence-sensitive refinements by repeated names
or by their root alone. Precisely the principal arity-four assemblies into the
old wholes remain nonuniversal even in O: if one were universal, its target
would be isomorphic to Comp(p), contradicting word lengths one and four under
Ev. This does not label all refinement entries nonuniversal: the unary scalar
1 and e entries in (9.2) are invertible and hence universal.

The evidence inventory records the finite certificates for the same graph
partitions, contextual tuple compression/expansion, graph-word occurrence
allocation, scalar collisions and coherence. The unbounded constructor proof
and factor equations, not finite enumeration, prove the uniform theorem.

## 10 Original E4 conclusion and stopping boundary

The selected presented virtual input is genuinely nonrepresentable by its own
syntax invariant. The ordinary completion is constructed with all finite
universal composites, satisfies its stated categorical relative property, adds
horizontals genuinely new even up to isomorphism, fixes B, and conserves the
specified original whole/witness/refinement information. Its associators and
unitors satisfy the required coherence. Rel/Span and E3 supply precise positive
and negative model criteria; actual bad strong maps and incompatible markings
show the information-loss boundary.

This establishes the E4 P theorem at the chosen parameterized class, subject
to the separately recorded independent review and C evidence. It does not
claim full faithfulness on the entire free V syntax, preservation of all
preexisting nonnullary universal cells by normal maps, normalization of O,
free ordinary completion of the concrete S via a nonnormal one-entry embedding,
or the E5 local-to-global exact-assembly theorem. Those are not smuggled into
this completion claim, and no historical source or completion ledger is changed.
