# E2 universal chosen equipment presentations

**Result.** Every small presentation specified in §2 has an explicitly
constructed chosen virtual equipment `F P`. Restriction and term evaluation
give an **isomorphism of categories**

    Hom_ch(F P,E) ≅ Int_ch(P,E),                         (0.1)

including all cell-natural transformations, for every eligible chosen target
E. For normal rather than literally choice-preserving functors the correct
statement is an **equivalence with Int_ch(P,E)**, using transported images of
derived generator profiles. The unmarked case is unconditional; for fixed
extra markings it requires §9's comparison-invariance hypothesis. The
comparison functors and their coherence are in §§8–9. Neither statement
asserts that every normal functor preserves all nonnullary opcartesian cells.
The parameterized C5 and enlarged graph–span presentations in §11 are actual
local presentations, not exhaustive diagrams of their semantic cells.

This is the universal-presentation P component of **original E2 only**. The
companion `reconstruction_theorem.md` supplies the substantive reconstruction,
original-profile recovery, and exact quotient/conservativity qualifications.
The free C5-only envelope is not identified with the enlarged reconstructed
graph–span equipment. No full Lean formalization or E3/E4 acceptance is claimed.

## 1 Sources and conventions

We import the accepted E1 axiom system and 2-category, `../e1_equipment_core_20261031/theorem.md`
§§1–5, with its stated size and classical-choice conventions. The substantive
existing proof `Conservative_Equipment_Envelope.md` (ENV), §§2–7, already
constructs the C5-only term envelope and proves its transformation extension
and choice comparisons. This document credits that proof, extends its exact
scope to the presentation category below, handles derived generator profiles
and selected universal markings explicitly, and records all naturality laws.
`Extended_Local_Presentation.md` (EXT), §§1–8, is the separate local normal-form
reconstruction used by the companion. The source map gives exact paths and
hashes; no inherited source is edited.

The standard infrastructure is Cruttwell–Shulman, *A unified framework for
generalized multicategories*, Definitions 2.1, 3.1, 5.1, 7.1 and 7.6, and
[Theorem 7.24](https://arxiv.org/pdf/0907.2460v3#page=42).
In particular, every VDC functor between full virtual equipments preserves
cartesian cells. **Normal** means preservation of universal nullary cells.
It does not mean strict preservation of chosen objects, nor preservation of
every nonnullary opcartesian cell. Here `Hom_ch` means normal functors that
also preserve the specified restriction and unit choices literally, and
preserve the expressly declared additional markings. Its arrows are all E1
cell-natural transformations, not only invertible or choice-strict ones.

A cell fibre is written

    Cell((H_1,...,H_n);K | f,g),

with the entire horizontal path and its intermediate objects retained. At
arity zero the source is a specified object A and f,g have common domain A;
they need not be equal. Composition is `β α` (first α, then β). A substitution
row includes every shared vertical map `u_0,...,u_n`, including the sole map
`u_0` when n=0. We use E1's classical, single-horizontal-target VDCs, not an
augmented theory with empty horizontal targets.

## 2 The small presentation data

Fix a universe U. All generating data below are U-small; all expressions are
finite, with no bound on arity or depth.

### 2.1 Vertical and horizontal data

A presentation gives a small directed graph `(V_0,V_1)` and parallel path
equations `R_v`. Let

    V = Path(V_0,V_1)/R_v.

This is a quotient category with the specified objects; no object equations
are permitted. Equivalently one may supply V with its identity/composition
table. The vertical equations are settled first. Cell sorts are indexed by
actual arrows of V, so a later cell equation never changes a vertical type.

Give a small set `H_0` of horizontal generator names with endpoints in V.
Define the set `H(P)` of horizontal expressions by the finite grammar

    H ::= h (h∈H_0) | I_A | R(H;f,g),                    (2.1)

where `R(H;f,g):A'⇒B'` for `H:A⇒B`, `f:A'→A`, `g:B'→B`.
There are **no horizontal type equations**. In particular `R(H;1,1)`, H,
and a pre-existing named loop are distinct expressions unless they are the
same literal constructor expression. Their comparisons will be cells.

Give a small set `W` of witness generators, each assigned a full cell sort
over `H(P)` and V. Witnesses may have nonidentity boundaries, repeated source
occurrences, empty source, and profiles containing restrictions or units.
One does not select only universal witnesses. Since all horizontal expressions
are defined before W, these derived profiles introduce no circularity.

### 2.2 Cell relations and selected universal declarations

First form the base raw cell language of §3 with identities, substitution,
κ, η, L and U. One may then give a well-founded small staged list of selected
globular terms

    e_j:p_j⇒K_j                                         (2.2)

to be **contextually opcartesian**, adding its factor constructor `Q_j` after
e_j is specified. At a later stage e_j may use earlier Q's but never itself
or a later Q. A well-founded rank is part of this optional input. Every
individual term remains finite. An empty declaration list is allowed and
is the convention for the unmarked C5-only free envelope.

Finally give a small set R of parallel equations in this completed raw
language. Thus equations may mention substitution, restrictions, universal
units, L, U, and the factors for the selected exact/opcartesian declarations.
All relations have the same complete source path, target, and boundary maps
on both sides. A declaration is a universal assertion with factor laws, not
an ordinary label silently treated as a proof of universality.

An optional declaration that an **existing** unary cell
`χ:R⇒H | f,g` be cartesian is encoded without any horizontal type equation.
Its canonical comparison is `ℓ=L_(H;f,g;1,1)(χ):R⇒R(H;f,g)`.
Adjoin a globular witness `s:R(H;f,g)⇒R` and the parallel local equations
`sℓ=1_R`, `ℓs=1_(R(H;f,g))`. Then `χ=κℓ` is cartesian, and its lift is the
actual term `s L(α)`. Conversely, if an interpretation sends χ to a cartesian
cell, ℓ is its unique invertible comparison with the chosen κ and s is its
unique inverse. Thus this finite local encoding adds no arbitrary factor
choice. It covers the marked-existing-restriction presentations used in the
companion's obstruction; it does not literally identify the named R with
the fresh restriction expression. Declaring an existing nullary universal
is already covered by (2.2).

Other exact labels, such as the graph–span coefficient-exact predicate, are
separate named markings. One can designate small sets of globular terms as
their generators and specify identity/substitution closure or no closure.
These labels do **not** add Q constructors or claim opcartesianness. For an
optional admissible subcalculus choose a horizontal subquiver and globular
term generators; take the least identity/substitution-closed subcalculus
containing them. Neither restriction factoring nor arbitrary interface change
is automatically an admissibility/mark closure rule. Every selected e_j must
be included in the declared admissible subcalculus. Taking all globular cells
admissible is also available.

Work in each fixed vocabulary and closure convention for admissibility and
the named markings. The categories below do not silently vary that vocabulary;
declared forgetting variants are separate functors between the conventions.
A presentation may have no generators for one of the fixed marks. Taking
all globular cells admissible uses that same whole-globular convention on
eligible targets; smaller target admissibility uses the specified generated
subcalculus convention instead.

The morphism convention is preservation of these declared positive markings.
No theorem below asserts reflection of a freely generated marking, and no
negative membership assertion is silently imposed. Where a marking is declared
closed under isomorphism transport, that is explicit extra closure data.

## 3 The raw finite term construction

For each well-typed fibre, form finite terms with these constructors:

1. The named witness generators and `1_H` for every H.
2. Every fully typed substitution `α[β_1,...,β_n]`, including its complete
   shared vertical-map row. If n=0 write `α⟨u⟩`.
3. `κ_(H;f,g):R(H;f,g)⇒H | f,g` and `η_A:()_A⇒I_A | 1,1`.
4. If `α:p⇒H | f u,g v`, its restriction factor

       L_(H;f,g;u,v)(α):p⇒R(H;f,g) | u,v.               (3.1)

5. If α has source `(r,s)` with the chosen junction at A, its unit factor

       U_(r,A,s)(α):(r,I_A,s)⇒K | a,b.                 (3.2)

   The target and outside boundaries a,b are unchanged. The actual position
   is part of the constructor, even if adjacent component types repeat.
6. For a declaration (2.2), and α with source `(r,p_j,s)`, a factor

       Q_(j;r,s)(α):(r,K_j,s)⇒K | a,b.                 (3.3)

Every prefix, suffix and source path may be empty. In all three factor
constructors arbitrary legal outside boundaries are allowed. The inductive
definition includes only terms with finite formation trees and the declared
well-founded stage dependency, so no existence of a free equipment is assumed.

Quotient each fibre by the **least parallel equivalence relation stable under
all constructors**, containing R, the VDC identity/associativity laws, and:

    κ L(α)=α,                  L(κ β)=β;                 (Rβη)
    U(α)[1_r,η_A,1_s]=α,
    U(β[1_r,η_A,1_s])=β;                               (Uβη)
    Q_j(α)[1_r,e_j,1_s]=α,
    Q_j(β[1_r,e_j,1_s])=β.                             (Qβη)

These are typed schemes with all the displayed parameters, not rules on an
untyped word algebra. Leastness is the intersection of all such congruences
(or the finite derivability closure); the indiscrete relation in each fibre
shows this intersection exists. A universe-small set of finite terms and a
set quotient give small cell sets. No confluence, termination or decidable
equality assumption is made.

Quotient closure under L/U/Q is essential to this construction. It expresses
the mandatory cancellation consequences of the imposed universal structures;
it does not promise that unrelated original-profile equations are reflected.
The companion analyzes this precise issue and distinguishes a relative
pre-equipment presentation from a quotient of an already complete equipment.
In fact `reconstruction_theorem.md`, Theorem 6.1, proves that on an already
complete fixed-sort equipment every ordinary substitution congruence respects
L and U: their inverse operations are actual one-hole substitution contexts
using fixed companion/conjoint and unit cells. Thus no extra L/U saturation
cost is claimed in that setting. The relative pre-equipment completion and
selected nonnullary Q declarations are different cases.

## 4 The constructed object is a full virtual equipment

Let `F P` have vertical category V, horizontal expressions (2.1), and the
cell quotients of §3. Substitution is well-defined by constructor congruence;
its identities and associativity are the imposed typed VDC laws, including
the laws for retained nullary vertical whiskering.

For each H,f,g and every source path p, u,v, postcomposition with κ is a
function

    Cell(p;R(H;f,g)|u,v) → Cell(p;H|fu,gv).

L is a well-defined inverse by `(Rβη)`. This proves cartesianness in **every
arity and every boundary factorization**, not only on generators or globular
cells. Similarly substitution of η in any specified context is inverse to U
by `(Uβη)`. Thus η is contextually opcartesian for every surrounding path,
target, and outside boundary. `F P` is a chosen virtual equipment. Each e_j
is contextually opcartesian by the identical Q argument. Consequently its
selected opcartesian marking is true, not merely syntactic annotation.

The identity/substitution closure of actual opcartesian cells is opcartesian:
the relevant contextual substitution maps are composites of bijections.
If isomorphism transport is selected as a closure operation, it too preserves
universality by composing these bijections with invertible unary substitutions.
The optional declared nonuniversal marks are simply the specified subsets of
cell classes. Equations can merge marked representatives; membership then
means that the class has a declared marked representative or derivation.

All universal operations act at arbitrary distinguished occurrences in a
larger diagram. For example,

    L(α[β_i]) = L(α)[β_i]                               (4.1)

whenever typed: postcompose both sides with κ and use associativity and
`(Rβη)`. Injectivity gives equality. Unit/Q factor naturality is proved by
substituting their universal cell in the distinguished block and using its
injectivity. Mixed and repeated operations commute whenever both sides
describe the same fully expanded diagram: cancel each specified universal
bridge in a fixed order. This is exactly E1 Theorem 3.1, now verified for the
constructed quotient. It never cancels an arbitrary surrounding witness.

## 5 The interpretation category and extension on objects

Let E be a chosen virtual equipment with the relevant marking convention.
An object of `Int_ch(P,E)` is finite-term interpretation data:

* a functor `v:V→E_v`, equivalently images of the vertical generators satisfying
  R_v;
* a horizontal image of each generator h over v;
* a cell image of every witness σ in the **recursively evaluated** full sort
  of σ, using E's chosen units and restrictions;
* satisfaction of R under recursive term evaluation, and of every declared
  positive marking; each designated e_j evaluates to a contextual opcartesian
  cell in E.

At Q stage j this last property supplies the unique factor used to evaluate
Q_j. The stage order makes this recursion well-founded. The interpretation
uses no assignments to arbitrary semantic cells. The condition on e_j is a
target universal property among **all** target cells, not merely the image
of the supplied signature.

Evaluate horizontal expressions recursively; evaluate identity/substitution,
κ and η by their target operations; evaluate L,U,Q by the corresponding
unique universal factors. Every defining law holds: the VDC laws hold in E,
the β/η laws are the two inverse laws of the target universal bijections,
and R holds by assumption. Evaluation descends to a chosen-strict normal
marked functor

    Ext_E(I):F P→E.                                    (5.1)

Conversely a functor in `Hom_ch(F P,E)` restricts to these data. It preserves
L automatically by cartesian uniqueness: the image of `κ Lα=α` characterizes
the factor. It preserves U by contextual unit uniqueness, and Q_j because it
preserves the declared opcartesian marking. Induction on horizontal and cell
terms now proves

    Res_E Ext_E(I)=I,      Ext_E Res_E(F)=F              (5.2)

as equalities of the actual vertical functors, horizontal images, and cell
functions. These are not only equality up to isomorphism in this strict
chosen convention.

## 6 Transformations and the full categorical inverse laws

For interpretations I,J, a morphism consists of a vertical natural
transformation `τ:v_I⇒v_J` and unary cells

    τ_h:Ih⇒Jh | τ_A,τ_B                               (6.1)

for each base horizontal generator h. No component is required to be
invertible, admissible or exact. Extend these components recursively to all
horizontal expressions, writing F,G for the evaluations:

    Gκ_(H;f,g) τ_R = τ_H Fκ_(H;f,g),                  (6.2)
    τ_(I_A) Fη_A = Gη_A⟨τ_A⟩.                        (6.3)

In (6.2), vertical naturality makes the right side's boundaries factor through
Gf,Gg with residual τ components; cartesianness of Gκ gives the unique τ_R.
In (6.3), the unit Fη gives the unique τ_I. These formulas retain nonidentity
internal vertical components and the arity-zero whiskering component.

The generator-level conditions on τ are naturality for every witness generator
(a finite list only when W is finite):

    τ_K Fσ = Gσ[τ_H1,...,τ_Hn].                        (6.4)

Its τ components on a derived profile are those just computed, not independent
extra choices. At n=0 the right side is `Gσ⟨τ_A0⟩`. Equations in R introduce no
additional transformation conditions: naturality is an equation about terms
and is preserved by their equalities.

### Lemma 6.1

These data extend uniquely to a cell-natural transformation `F⇒G`.

**Proof.** Use simultaneous structural induction on terms, and the well-founded
order for declared e_j. Identity naturality is an identity law; substitution
naturality follows by associativity and the generator/child hypotheses.
In an empty row the missing horizontal tuple is not a missing condition:
vertical naturality supplies equality of the retained common boundary maps.
Naturality for κ and η is exactly (6.2) and (6.3).

For Lα, postcompose the two proposed naturality composites with Gκ. Equations
(6.2) and `(Rβη)` turn them into the two sides of already established naturality
for α. Cartesian injectivity gives equality. For Uα, precompose the proposed
composites with Fη at that exact source occurrence. Equation (6.3), `(Uβη)`
and naturality of α identify the results. Contextual unit injectivity gives
equality before precomposition.

For Q_j α, precompose at the specified block with F e_j. Naturality of e_j
is already proved at its earlier formation stage. It moves that bridge past
the computed τ components; `(Qβη)` and naturality of α identify the expanded
composites. Contextual opcartesian injectivity of F e_j proves equality.
There is no circular use of naturality of Q_j to prove naturality of its own
defining e_j.

Uniqueness follows because every transformation on `F P` must satisfy
naturality for κ and η, forcing (6.2)–(6.3), and is determined on vertical
arrows/base horizontals by its restriction. There are no further horizontal
constructors for Q. Thus every cell-natural transformation restricts to, and
is recovered from, exactly these data. QED.

Identity and vertical composition are the pointwise E1 formulas. Their
recursive extension agrees with those formulas on every horizontal expression
by uniqueness from the base data. Hence `Int_ch(P,E)` is a category, and Ext
and Res preserve identity and composition. Lemma 6.1 and (5.2) prove the
category isomorphism (0.1), on **both objects and morphisms**.

## 7 Presentation maps and two variable naturality

A precise category `Pres_ch` is obtained as follows. A map `a:P→Q` gives:

1. a functor of the presented vertical categories, specified on their graph
   generators and respecting R_v;
2. a target horizontal term for every source base horizontal, with the mapped
   endpoints;
3. a target cell term class for every source witness generator, with its full
   recursively substituted sort;
4. derivations of the substituted source equations from Q's equations,
   preservation of the declared admissible horizontal subquiver and its
   generating cells, and preservation of each named marking's generators
   within the fixed marking vocabulary.

For selected opcartesian declarations, preservation means a certificate that
the image is in Q's declared universal family, or its explicitly allowed
identity/substitution/isomorphism-transport closure. Such a certificate gives
a factor term for that image: use U or Q for a primitive certificate, the
identity map for an identity, compose the contextual inverse maps for a
substitution certificate, and conjugate by the displayed inverse unary cells
for an isomorphism certificate. Thus substitution of a source Q constructor
has an actual target term, not an unexplained semantic assertion. Different
certificates give equal factors by the already proved universal uniqueness.

Equal maps have the same vertical functor and horizontal expressions, and
equal witness term classes; their chosen proof derivations/certificates are
not additional morphism data. Composition is recursive term substitution.
It respects all relations and certificates; structural induction proves
associativity and identities. This defines the promised small-presentation
category without defining a free object by its desired universal property.
The construction gives a functor

    F:Pres_ch→ChVEq,      a↦F a.                       (7.1)

For a target chosen-strict normal marked functor `K:E→D`, target composition
induces `K_*:Int_ch(P,E)→Int_ch(P,D)`. It applies K to the base data and
transformation components. K preserves factor operations by the uniqueness
argument in §5. Hence direct induction gives the equalities of functors

    Ext_(P,D) K_* = (K∘-) Ext_(P,E),
    Ext_(P,E) a^* = (-∘F a) Ext_(Q,E).                 (7.2)

with the appropriate source presentation on each Ext. Res obeys the same
commuting squares. For a cell-natural target transformation `λ:K⇒L`, the
induced natural transformation has at I the restricted components of
`λ Ext_E(I)`. Its naturality at τ is exactly the E1 interchange/naturality
equation applied to τ's unary component. Ext carries it to that same whiskered
transformation, by Lemma 6.1. Thus (0.1) is natural in presentations and
**2-natural in the strict chosen target 2-category**. This is the precise
two-dimensional universal claim; a merely set-valued hom bijection would be
strictly weaker.

One can likewise allow syntactic presentation 2-cells: vertical natural
transformations and base-horizontal unary term classes satisfying generator
naturality with (6.2)–(6.3). Lemma 6.1 supplies their unique extension;
composition/interchange are E1's formulas. No such enrichment is needed to
reinterpret the more modest category `Pres_ch` just defined.

## 8 Changing target choices and forgetting choices

### 8.1 Actual comparison cells

For cartesian cells `κ:R⇒H | f,g`, `κ':R'⇒H | f,g`, let

    c:R⇒R', d:R'⇒R,    κ'c=κ, κd=κ'.                   (8.1)

They are the respective unique lifts. Postcomposition with κ and κ' gives
`dc=1` and `cd=1`. For universal units η,η' at A, define

    u:I⇒I', v:I'⇒I,    uη=η', vη'=η.                  (8.2)

Unit injectivity proves `vu=1`, `uv=1`. For three choices, `c_23 c_12=c_13`
and `u_23 u_12=u_13`, since each composite has the same post-/precomposition
with the relevant universal cell. Identity and any finite coherence diagram
follow by exactly the same injectivity argument. Nested restrictions are
compared to restriction along composites by (8.1), since composites of
cartesian cells are cartesian in every arity. Nothing identifies their
horizontal expressions as literal types.

### 8.2 Transporting a general presentation interpretation

Equip the same underlying E with two sets of choices c,d. Given I in
`Int_c(P,E)`, keep its vertical and base-horizontal images. Use (8.1)–(8.2)
recursively to obtain invertible globular cells

    b_H:Eval_c(H)⇒Eval_d(H),       b_h=1_h.             (8.3)

If σ has a derived horizontal profile, its d-image must be **transported**:

    I^d(σ)=b_K I^c(σ)[b_H1^(-1),...,b_Hn^(-1)].       (8.4)

At n=0 the indicated row retains the identity vertical source map. One cannot
simply reuse I^c(σ), whose type may be different. Structural induction using
universal uniqueness proves the same formula for every term. Hence every
equation in R transports to a valid equation. Selected opcartesianness
transports because conjugation by these isomorphisms preserves its universal
bijections. Membership in any *selected* marking, or in a selected admissible
subcalculus, is a separate issue. For the following equivalence of fixed-mark
interpretation categories require invariance under these particular b's.
Without it the formulas still compare the underlying interpretations, and
one may explicitly transport the marking to a different marked package; they
do not yield an equivalence with the unchanged fixed-mark category.

For transformations τ use the transported components

    τ^d_H=b^J_H τ^c_H (b^I_H)^(-1),                   (8.5)

with the same vertical components; at base h this is just τ_h. Naturality
follows by substituting (8.4) into (6.4). Thus (8.4)–(8.5) give actual functors
`T_cd:Int_c(P,E)→Int_d(P,E)`. The inverse is T_dc. The identity and three-choice
laws for b imply the inverse and cocycle laws for T on objects **and arrows**.
The b's themselves form invertible cell-natural comparison transformations
of the two evaluation functors. The identity/cocycle equations are equalities
of transformations, not an appeal to unspecified higher coherence.

### 8.3 Unchosen targets

For an unchosen small equipment, simultaneous choices require precisely the
set-indexed choice assumption stated in E1. Each choice gives the category
above; the explicit T_cd and their cocycle identify the choices coherently.
Equivalently, use normal functors into the unchosen equipment and §9's
equivalence. There is no arbitrary choice of factors once a universal cell
has been chosen: its factor is uniquely determined. This passage forgets
chosen representatives, not witnesses, wholes, profile occurrences or
boundary maps.

## 9 Normal functors versus strict chosen functors

Let `Hom_n(F P,E)` have normal VDC functors preserving the selected markings
and all E1 cell-natural transformations. Cartesian preservation is automatic
by CS Theorem 7.24. An additional all-opcartesian-preserving condition is not
inserted. For the fixed-mark equivalence in this section require the positive
markings and admissibility to be invariant under the actual comparison
transports below. The unmarked theorem has no extra condition. If this
invariance fails, (9.5) is not asserted for the unchanged fixed marking:
transporting marks gives a comparison with a *different marked package*,
not an F-dependent redefinition of the fixed category of §5.

Given `F:F P→E`, form a strictly choice-evaluated horizontal assignment from
its values on the base generators. There are invertible cells

    c^F_H:Eval_ch(F|H_0)(H)⇒F(H),    c^F_h=1,           (9.1)

defined recursively as follows. For I_A compare the chosen target unit with
the universal `Fη_A`, which is universal by normality. For R(H;f,g), compare
the chosen restriction of the already strict-evaluated H with `Fκ` after
the comparison c_H. The latter is cartesian, using CS Theorem 7.24 and
invariance under the invertible target comparison. Equation (8.1) gives the
unique invertible c_R. This construction fixes F's vertical functor.

Define the normalized generator assignment

    N(F)(σ)=(c^F_K)^(-1) Fσ[c^F_H1,...,c^F_Hn].       (9.2)

This transported restriction, not raw restriction, is necessary when σ's
profile contains derived horizontals. Induction on terms proves that (9.2)
holds for every term, including L/U/Q. Thus it satisfies R and, by the fixed
comparison-invariance hypothesis, the same marking conditions. Put
`S(F)=Ext_E(N(F))`. Equations (9.1) are a cell-natural
isomorphism

    c^F:S(F)⇒F.                                       (9.3)

For `τ:F⇒G` define Nτ to have its original vertical and base-horizontal
components; on a derived H the resulting extension is

    (c^G_H)^(-1) τ_H c^F_H.                            (9.4)

The recursive uniqueness of (6.2)–(6.3) proves (9.4), and generator naturality
then follows from that of τ and (9.2). These assignments preserve identity and
composition. Equation (9.4) also proves naturality of the counit c in F.

If F is already chosen-strict, all c_H are identities by uniqueness, so N
is literal Res there. Consequently the inclusion

    i:Hom_ch(F P,E)→Hom_n(F P,E)

is fully faithful (the homs allow exactly the same transformations), and
`S i=1`, with invertible natural counit `i S⇒1` given by (9.3). The triangle
identities hold since c is the identity on already strict functors. Therefore

    Hom_n(F P,E) ≃ Int_ch(P,E).                        (9.5)

This does not strictify arbitrary functors between arbitrary chosen equipments
while fixing all their named horizontal images: it uses the **free horizontal
grammar** of `F P`. In EXT every H(G,S) is already a named generator; its
strict-choice compatibility is an extra condition, not an automatic operation
fixing all those images.

For normal target maps `K:E→D`, comparison with D's choices is made by (9.1).
On interpretation categories use `N_D(K Ext_E(-))`. For a composite L K, the
direct comparison and the composite comparison coincide after postcomposition
with the same cartesian cells and precomposition with the same universal
units; induction on H and uniqueness identify them. The same equations,
together with (9.4), hold on transformations. They provide the identity,
composition and 2-cell coherence for the corresponding **pseudonatural**
equivalence in the unchosen/normal convention. We claim no strict 2-adjunction
for that convention without retaining these comparison choices.

## 10 Original core map and fresh horizontal classification

Suppose P begins with an original presented identity-boundary calculus C:
its interfaces inject into V, its component names inject into H_0, and its
local witness generators and relations are among W and R. Evaluating the old
terms gives the canonical strict core map

    j_C:C→Core(F P).                                   (10.1)

It retains the original output whole, complete profile, occurrence positions,
and actual witness class. On occurrence-refinement categories it acts entrywise
on every tuple; composition is inherited typed substitution. Conservativity
does not follow from existence of (10.1).

Every horizontal expression has a unique outer constructor. Thus the enlarged
horizontal universe is exactly: old/base names; fresh units; and iterated
restrictions of those, with each arrow and endpoint retained. Identity and
successive restrictions admit the coherent isomorphisms of §8, not extra type
equalities. This is a grammar classification, not a claim that there are no
accidental further isomorphisms in a particular relation quotient.

For the unmarked C5-only envelope the old empty-graph identity component is
not merely syntactically different from the fresh I: it is **not isomorphic**
to I. ENV §§8–10 supplies a separating chosen equipment. Its graph labels
are finite words, tensor unit the empty word `[]`, while the old component
has the one-entry word `[0]`. A forest isomorphism must induce a monotone
bijection of its input and output occurrence sets, hence preserve word length.
So `[0]` and `[]` are not isomorphic. The free interpretation sends the old
component and fresh unit to these objects respectively; an inverse pair in
the free envelope would yield an impossible inverse pair there. In particular
the old scalar-one nullary is not a universal unit of this free envelope:
normal interpretation would then send it to a unit isomorphic to `[]`.

In the separately enlarged graph–span presentation it is legitimate to choose
`H(0,I_A)` as unit because EXT §5 proves its full universal property. This is
an additional relation/structure of that reconstructed presentation; it is
not an identification imported back into the smaller free envelope.

## 11 Nontrivial parameterized local test presentations

### 11.1 The original C5 local presentation

For finite N (in the substantive test range N≥6), a finite interface category
K, and a finite commutative decoration monoid M, use the original C5 horizontal
components `(G,h)` and actual whole-labelled binary cuts, the genuine old
nullary generators, and unary scalar decorations. The seven local rule forms
are typed rotation, left/right unit, scalar identity/multiplication, and
left/right scalar movement. All full grades, induced subgraphs, retained
wholes and occurrences are the supplied C5 data. ENV §1 imports that exact
local presentation and its accepted comparison, not all semantic operations.

Fix the tagged faithful regular realization `F:K→B` into a small category of
actual finite tagged sets; B and its composition data are **retained input**.
Use its images for the old interfaces and arrows in the presentation. Our
construction adds the fresh (2.1) terms and factor laws, with no arbitrary
old witness declared universal. ENV §§2–7 is precisely this special case of
§§2–9. Its separating graph–span/graph-word models prove equality reflection
on every original profile and on complete old refinement tuples. They do
not prove fullness of (10.1) on new old-profile terms. The companion states
the positive recovery and the generic obstruction at exactly those strengths.

### 11.2 The enlarged graph span presentation

The selected reconstructed class uses EXT's different local presentation:
vertical finite sets/functions; named horizontals H(G,S) for actual finite
spans; unary span-square maps `u_(a,e,b)`; scalar cells d_m; binary graph cuts
c with identity tuple coefficient; and c0 at the diagonal span. Its reusable
local rules are span-square category tables, scalar multiplication/centrality,
matched-boundary binary naturality, nullary naturality, ternary rotation with
actual tuple comparison maps, and genuine diagonal-unit deletion. These are
bounded-shape schemes, not a list of every multicell and true equality.

EXT §§3–5 prove a fixed-sort normal form with exactly the actual graph
partition, endpoint-compatible coefficient function and global scalar. Its
local sketch interpretation categories include all cell-natural transformations
by the ordinary generator induction of §6. When the source and target are
already complete equipments, CS Theorem 7.24 makes cartesian preservation
automatic. **Unit preservation still must be imposed** to select normal
functors; bare VDC functors need not be normal. Thus the inherited EXT §6
wording that treats restriction preservation as an independent full-equipment
obstruction, or equates this convention with all-opcartesian strength, is
not used. Literal chosen compatibility remains a separate strict condition.

The graph–span canonical change-of-choice maps have scalar 1 and actual
bijective tuple coefficients, and leave graph partitions unchanged. They
therefore preserve coefficient-exact marking under these specific transports,
as well as genuine Ex_op. This does not assert that every conceivable unary
isomorphism preserves an arbitrary normalized extra marking.

### 11.3 The free construction and the reconstructed class actually compare

Let `S_EXT` be the §2 presentation with EXT's named horizontals, generators
and local equations. Declare each c0_A contextually opcartesian, using Q;
declare each displayed named pullback cell κ cartesian by §2.2's inverse
comparison encoding. These declarations do not name arbitrary semantic cells
or equations. They are the same uniform unit/pullback schemes for every
already named span. Let `P_EXT=P_(N,M)` be the locally presented equipment
constructed and normalized in EXT and in the reconstruction companion.

Its proved units and restrictions give an interpretation of S_EXT. Section 5
therefore constructs an actual chosen-strict evaluation

    q:F(S_EXT)→P_EXT.                                  (11.1)

In the other direction, send each EXT vertical/horizontal/cell generator to
the identically named generator of F(S_EXT). Its local relations hold there,
so ordinary term interpretation gives a VDC functor

    j:P_EXT→F(S_EXT).                                  (11.2)

The image of c0 is universal by its Q declaration, so j is **normal**. Its
named restrictions are cartesian by their declared inverse comparisons
(also consistent with CS 7.24). It is not chosen-strict: a named diagonal or
pullback horizontal is not the literal fresh I or R expression of F(S_EXT).
Since q returns every EXT generator unchanged,

    q j = 1_(P_EXT)                                    (11.3)

as a functor, not merely up to isomorphism.

There is an invertible cell-natural transformation

    c:j q⇒1_(F(S_EXT))                                 (11.4)

with identity vertical and named-base-horizontal components. At a fresh
restriction use its unique cartesian comparison, and at a fresh I use the
unique unit comparison, exactly as in (6.2)–(6.3). These are invertible because
jq is normal and preserves cartesian cells. All original EXT generators are
fixed by jq, so their naturality equations are identities. For an auxiliary
inverse witness s of §2.2, naturality is forced by its two inverse equations
and the already established naturality of ℓ=Lκ: multiply the latter equation
by the two inverses. Thus there is no false assertion that jq and the identity
literally agree on s's derived source type. Induction proves naturality for
all remaining L/U/Q terms just as in Lemma 6.1.

The components on j(P_EXT)'s named horizontals are identities, so `c j=1_j`.
Applying q to each recursive comparison gives the identity: qj=1, and both
compared universal cells become the same chosen cell of P_EXT, whose unique
self-comparison is identity. Hence `q c=1_q`. These are the triangle laws.
Equations (11.1)–(11.4) exhibit an equivalence of normal virtual equipments,
not a literal isomorphism of their different horizontal-expression sets.
For any eligible target, precomposition with q and j gives inverse equivalences
of **normal-functor and all-transformation categories**, with unit/counit the
whiskerings of c. Their naturality in target functors and transformations is
the E1 interchange law. Additional fixed selected markings require the stated
preservation/comparison conditions; the designated universal declarations
themselves have already been checked.

On any complete profile of named EXT horizontals, c's source and output
components are identities. Its naturality therefore says `j q α=α` in that
fibre. Together with qj=1 this makes q and j mutually inverse on each such
cell fibre, including every original C5 profile and all its occurrence-wise
refinement entries. Composing q with the companion's normal-form isomorphism
`P_EXT≅V(N,M)` gives the promised sound-and-complete reconstruction of the
selected class **from an instance of the generic universal construction**.
This bridge neither asserts `F(C5)≅P_EXT` nor supplies the extra span types
and maps from the smaller old generators.

The companion gives the actual reconstruction, full old-profile and full
occurrence-refinement recovery, activated finite-decoration quotient, and
generator/relation quotient criterion. Those results and this universal
construction together meet E2's positive requirements. Neither is replaced
by the other, and no ordinary-equipment completion is asserted as an E2
requirement.

## 12 Scope of the completed universal component

The proof gives a specified small presentation category, finite raw terms,
typed factor laws, a constructed full chosen virtual equipment, categorical
extension/restriction inverses, target and presentation naturality, selected
universal-mark correctness, and actual chosen/unchosen comparison functors
with identity/cocycle/2-cell coherence. It distinguishes literal strictness,
normality, and all-opcartesian strength throughout. All nonuniversal primitive
witnesses remain legitimate unless a particular quotient identifies them.

The source contribution is an explicit generalization and integration of ENV's
existing proof, not a novelty claim for free algebra, virtual equipments,
span calculus or uniqueness-of-universal-choices arguments. Reconstruction,
original-profile conservativity hypotheses, and quotient costs must be read
with the companion and its independent review. Finite checks support the
examples; they do not replace the unbounded P proofs above.
