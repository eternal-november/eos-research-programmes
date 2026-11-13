# Independent presented-refinement completion and its comparison

**Evidence:** P, author proof submission, not independent acceptance.
**Contract:** v0.1, 24 October 2026, SHA256
`47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
**Released exact target:** `Integrated_Targets.md`, SHA256
`2f8cc8b77165ef9d5fe915799e5291089067b10f0683f82d9f878ba1da1c7f7b`.

This supplies the new P bridge in target §§4–6. It does not redefine the
semantic refinement category, redo the already proved object presentation,
claim a full Lean formalization, or confer scientific acceptance. The
parameter/transport and product/pullback analysis are separate companion
arguments. A4/C5 are positive obligations; the result below is a positive B3
comparison with a certified failure of the completion omitting one mixed
relation family. B4 and the full §3.6 bundle, and all unactivated D/E/F/G/I
obligations, remain outside this proof.

## 1. Quantifiers, inherited results, and exact notation

Fix any natural number N, any finite category K, and any finite commutative
monoid M with identity 1. There is no bound on profiles, term depth, equation
words, or graft histories. The principal instances have N≥6 and a category
with at least three interfaces; the theorem also covers the degenerate
parameters. Taking all N covers all finite ordered graph sizes.

Use exactly the finite signature S(N,K,M) and declared parallel equations
E from `workstream_A/rewrite/A3_LOCAL_COMPARISON.md` §§1–2. Its colours are
whole components W=(G,f:A→B), with literal ordered graph G on [r], r≤N. Its
primitive vertices are labelled binary cuts c, designated nullaries u_A only
at (empty,id_A), and unary d_m^W. Identity leaves x_W are not primitive vertices.
A tree carries its full ordered frontier, including every component, intermediate
interface, and actual arrow. External occurrences of equal components remain
different positions.

The seven oriented rule families are

    R   c(c(x,y),z) → c(x,c(y,z))
    UL  c(u,x)      → x
    UR  c(x,u)      → x
    D0  d_1(x)      → x
    DA  d_m(d_n(x)) → d_(mn)(x)
    DL  c(d_m(x),y) → d_m(c(x,y))
    DR  c(x,d_m(y)) → d_m(c(x,y)).                         (1.1)

Each displayed variable occurs once on either side, in the same frontier
order. The u is an actual nullary term, not a variable or an empty-colour
external leaf. Labels and typing are the exact ones in the inherited source:
in R, a triple partition determines the two binary groupings by unions and
increasing restriction maps, and the whole arrow is the composite of the
retained triple of arrows. Unit rules require the corresponding empty/id cut.
Decoration rules change no input occurrence or its type.

The following previously verified statements are used, not assumed anew:

1. Accepted A1–A3 construct the free typed calculus F(S), the actual least
   declared parallel substitution congruence, and its quotient Q. Write
   pi:F(S)→Q for the strict projection.
2. The A4 proof gives contextual matching, termination by the lexicographic
   measure (B,A,H,D), confluence, and an explicit normal form. Write t↓ for
   its canonical irreducible. Then t↓=N(ev(t)), where ev maps into the
   independently defined full flat-cut calculus D=FlatCut(N,K,M), and

       pi(t)=pi(u) ⇔ t↓=u↓ ⇔ ev(t)=ev(u).                (1.2)

   Equalities include the entire retained profile and whole. The strict
   calculus isomorphism Phi:Q→D, Phi(pi(t))=ev(t), and inverse
   w↦pi(N(w)), are established in `A3_LOCAL_COMPARISON.md` §§3–6.
3. Accepted B1 constructs Raw(S,W): arrows T→U are actual leaf-indexed
   forests F with U=T[F]. Identity is the forest of identity leaves and
   composition is forest substitution. Its elementary histories are precisely
   finite primitive insertions, modulo interchange of incomparable inserted
   vertices; this quotient does not identify different forests.
4. Accepted B2 constructs Ref(A,W) for every lawful calculus A. An arrow
   a→a' is a full tuple b_i at the ORIGINAL slots of a, satisfying a[b_i]=a'.
   Equality is tuple equality, not equality of the composite alone. Composition
   has entry b_i[d_(i,j)] after the canonical ordered occurrence split.

Parameter provenance: THEOREM.md states its normalization result for every N.
A3_LOCAL_COMPARISON.md opens with N≥6 for its principal family. Its quiver,
finite generator/template construction, least-congruence comparison and inverse
maps use only r≤N, never the lower bound 6. For 0≤N<6 use those SAME formulas:
restrictions still have at most N vertices, unions are subsets of the fixed
whole, the designated empty/id units exist, and the normal right-comb proof
uses arity induction, not extra vertices. Every step of its quotient comparison
therefore applies unchanged. This explicitly supplies the small-N extension;
it is not attributed to an unstated range in the inherited adapter. The
mandatory six-vertex certificate and principal nonvacuity floor remain unchanged.

Every category below is first considered at a fixed W. Total categories are
the disjoint unions over W; there are no morphisms across different whole
components, even if their graph parts coincide. Composition p;q means first p,
then q. Proofs of typing equalities are not additional arrow data.

## 2. The independent generators-and-relations construction

### 2.1 The generating graph

Objects are all raw finite S-trees with output W.

A **graft edge** inserts one primitive corolla at a specified external leaf,
with matching output component. A nullary insertion creates no descendants at
that leaf. A **positive equation edge** e:T→U consists of a rule name in (1.1),
a well-typed one-hole context, and the ordered metavariable substitution that
realizes that contextual rewrite. Add a formal inverse e⁻¹:U→T. Matching is
encoded by this actual syntactic data, not by interchangeable proof objects;
identical rule/address/substitution data denote the same edge.

Take finite composable edge words. Quotient by the least category congruence
containing the relations below: this is the ordinary algebraic construction
of a category presentation, with objects unchanged. It exists as a quotient
of a set of finite words. Nothing in its definition mentions D, evaluation,
semantic tuples, or equality of images in a target category.

### 2.2 Raw relations and abbreviation R(T,F)

Impose the inverse relations only for equation edges, not for graft edges.
Impose B1's raw history relations: identities and interchange of adjacent
incomparable inserted vertices. B1 then gives a well-defined abbreviation

    R(T,F):T→T[F]

for any raw forest, independent of its legal elementary execution order.
Conversely these relations identify exactly histories for the same raw forest.
In particular, writing F⋆H for entrywise substitution after splitting H at the
descendant occurrences of F,

    R(T,id)=id_T,
    R(T,F);R(T[F],H)=R(T,F⋆H).                           (2.1)

These are consequences of the known raw category presentation. They are not
relations that compare forests by their eventual semantic values.

### 2.3 Ordinary and mixed relations

The ordinary relations O are the 18 local peak equations in §3, all their
well-typed context/substitution instances, the disjoint-redex squares, and the
variable-overlap squares. A variable-overlap square transports the inner
rewrite to the unique retained occurrence of that variable. Each variable
occurs once on each side, so this involves neither duplication nor deletion.

For each contextual positive equation e:T→U and each elementary graft A at a
leaf of their common ordered frontier, impose the mixed relation

    e;R(U,A)=R(T,A);e[A].                                (MOut)

Here e[A]:T[A]→U[A] is the *same old equation occurrence*, with its variable
subterms and outer-context leaves grafted as prescribed. This edge exists
syntactically because the rule is occurrence-linear and frontier-preserving.
The equation is not an assumed naturality of a semantic comparison.

For each **bare identity-leaf template** l→r in (1.1), each ambient tree T,
and each matching external leaf i of T, impose

    R(T,i:l);T[e]_i=R(T,i:r).                            (MIn)

All other entries of these two forests are identity leaves. R(T,i:l) and
R(T,i:r) are legal multi-step raw histories of the two template trees. The
middle T[e]_i is the one equation edge in the newly inserted template. There
are seven template families with finite labels for fixed N,K,M, in arbitrary
ambient T and i. In particular, MIn is NOT initially declared for arbitrary
semantically equal forests. Its contextual and substituted extension is proved
in §4.2.

Denote the resulting presented category by C=Comp(S,E;W).

## 3. Explicit ordinary coherence, not only object confluence

### 3.1 Complete local joining words

The following table fixes the path relations. An address is a word in L,R,D:
L/R select a binary child; D selects the child of a decoration. The empty
address ε is the root. A word such as `R@ε, UR@R` means apply these rewrites
in this order, interpreting each address in the term produced by the previous
step. The table displays the complete two paths from the common source to
the displayed common target. If target labels differ only by a monoid or
category axiom, they are the same actual finite label; no extra rewrite is
hidden. We keep d_1 in a common target when it occurs: a join need not itself
be irreducible.

|No.|Source|First path|Second path|Common target|
|---|---|---|---|---|
|1|c(c(x,y),u)|R@ε, UR@R|UR@ε|c(x,y)|
|2|c(c(x,y),d_m(z))|R@ε, DR@R, DR@ε|DR@ε, R@D|d_m(c(x,c(y,z)))|
|3|c(u,u)|UL@ε|UR@ε|u|
|4|c(u,d_m(x))|UL@ε|DR@ε, UL@D|d_m(x)|
|5|c(d_m(x),u)|UR@ε|DL@ε, UR@D|d_m(x)|
|6|c(d_m(x),d_n(y))|DL@ε, DR@D, DA@ε|DR@ε, DL@D, DA@ε|d_(mn)(c(x,y))|
|7|d_1(d_n(x))|D0@ε|DA@ε|d_n(x)|
|8|c(c(c(x,y),z),w)|R@ε, R@ε|R@L, R@ε, R@R|c(x,c(y,c(z,w)))|
|9|c(c(u,x),y)|R@ε, UL@ε|UL@L|c(x,y)|
|10|c(c(x,u),y)|R@ε, UL@R|UR@L|c(x,y)|
|11|c(c(d_m(x),y),z)|R@ε, DL@ε|DL@L, DL@ε, R@D|d_m(c(x,c(y,z)))|
|12|c(c(x,d_m(y)),z)|R@ε, DL@R, DR@ε|DR@L, DL@ε, R@D|d_m(c(x,c(y,z)))|
|13|d_m(d_n(d_p(x)))|DA@ε, DA@ε|DA@D, DA@ε|d_((mn)p)(x)|
|14|d_m(d_1(x))|DA@ε|D0@D|d_m(x)|
|15|c(d_m(d_n(x)),y)|DL@ε, DL@D, DA@ε|DA@L, DL@ε|d_(mn)(c(x,y))|
|16|c(d_1(x),y)|DL@ε, D0@ε|D0@L|c(x,y)|
|17|c(x,d_m(d_n(y)))|DR@ε, DR@D, DA@ε|DA@R, DR@ε|d_(mn)(c(x,y))|
|18|c(x,d_1(y))|DR@ε, D0@ε|D0@R|c(x,y)|

In row 6 the second target is initially labelled nm, which equals mn by
commutativity. In row 13, m(np)=(mn)p. Rows 8–12 use actual cut labels: each
path lifts the same blocks into the retained whole, and the increasing-map
restriction identity identifies the internal graphs. The entire retained
arrow string, not just its composite, fixes the intermediate grades; category
associativity identifies the two outer composites. Unit rows require the
indicated empty/id cut and therefore cannot remove an external empty leaf or
an empty nonidentity-grade block.

Every local overlap belongs to this list or a disjoint/variable square.
Indeed, distinct unifiable root heads give rows 1–7. A nonvariable proper
position of a left side is only the left binary vertex in R, the inner
unary vertex in DA, or the decoration child in DL/DR; these yield rows 8–18.
The nullary u has no proper redex position. Equal occurrences of the same rule
are the same edge. Disjoint positions commute. A nested redex in a variable
commutes because that exact variable subtree is retained once, at its uniquely
transported position. This is a classification of actual typed peaks: any
allowed source supplies all required labels, and each listed residual step is
well typed by restriction and category identities. Empty-frontier substituted
variables do not change that argument.

### 3.2 Coherent normalization theorem

Choose a deterministic reduction strategy, for example the first applicable
rule in a fixed preorder of addresses and rule names. Let

    ν_t:t⇒t↓

be its finite positive reduction path; for an irreducible t this is the empty
path. Termination proves finiteness, and inherited confluence identifies its
endpoint with t↓.

**Lemma 3.1.** Modulo O, every two positive paths from t to t↓ are equal.

**Proof.** Use well-founded induction on the contextual termination measure
of t. If t is irreducible both paths are empty. Otherwise compare first edges
e:t→a and f:t→b. If they are identical, the tails are equal by induction at a.
If different, §3.1 supplies an O square

    e;p=f;q,                  p:a⇒v, q:b⇒v.

Normalize v. The paths p;ν_v and the original tail from a both end at t↓:
all terms are reducts of t and have the same normal form. Their source a is
strictly smaller than t, so induction identifies them. The analogous claim
holds at b. Thus the first full path equals e;p;ν_v=f;q;ν_v, equal to the
second full path. The induction applies even when p or q is empty. No assertion
that arbitrary paths are already equal is used. ∎

Consequently, for every positive equation edge e:t→u,

    ν_t=e;ν_u.                                             (3.1)

Both sides are positive normalization paths. Since equation edges are
invertible, the inverse version follows by multiplying (3.1) by e⁻¹.
For an arbitrary pure equation zigzag z:t→u, repeated substitution of (3.1)
and cancellation gives

    z=ν_t;(ν_u)⁻¹.                                         (3.2)

The right side is defined exactly when t↓=u↓. Conversely, a pure equation
zigzag implies pi(t)=pi(u), and therefore equality of normal forms by (1.2).

**Theorem 3.2 (ordinary path coherence).** In the pure equation subcategory,
there is a morphism t→u exactly when pi(t)=pi(u), and any two such morphisms
are equal using O and inverse relations. Its canonical morphism is

    κ(t,u):=ν_t;(ν_u)⁻¹.                                  (3.3)

It satisfies κ(t,t)=id and κ(t,u);κ(u,v)=κ(t,v). This is proved coherence,
not an axiom identifying all parallel equation paths and not an inference
from object confluence alone.

## 4. Deriving the full mixed compatibility

### 4.1 Outer equation paths whiskered by arbitrary forests

For an elementary graft A, MOut is a defining relation. For a forest F,
choose a B1 elementary execution A_1,…,A_s. After an equation e:T→U,
the same execution is possible at the common ordered occurrences on both
sides: old external positions agree, and each insertion creates the same new
ordered typed positions. Apply MOut successively. Raw relation (2.1) then gives

    e;R(U,F)=R(T,F);e[F].                                (4.1)

If a graft position lies outside the context's rewrite subtree, e[F] is the
same disjoint old occurrence. If it lies inside a metavariable subtree, that
subtree has simply received its descendants. There is no frontier position
inside an actual nullary u; a nullary graft instead removes its chosen external
position on both sides. Thus the induction includes all nullary cases without
inventing an occurrence.

Changing the elementary execution of F changes neither raw arrow by B1; the
equation paths e[F] agree by §3.2 (indeed here the contextual edge data give
the same grafted rule occurrence). Taking inverses in the equation direction
derives (4.1) for e⁻¹. Concatenation proves, for any pure equation path z:T→U,

    z;R(U,F)=R(T,F);z[F].                                (4.2)

The endpoints of z[F] are T[F],U[F]. This construction uses the canonical
shared occurrence order, not a choice matching equal component labels.

### 4.2 Inner equation instances in arbitrary forest entries

**Lemma 4.1.** Suppose F,F' differ by one contextual equation step in one
original entry i. Let z:T[F]→T[F'] be the corresponding equation edge in the
whole tree. Then

    R(T,F);z=R(T,F').                                    (4.3)

**Proof.** Write the changed entry as C[l[σ]]→C[r[σ]], where C is a
one-hole raw context and l→r is a bare declaration template. Cut out that
redex occurrence, leaving a single identity leaf of its output component.
Let F^0 be the forest whose i-th entry is C[x] and whose other entries are
unchanged from F. This is a genuine raw forest. Put B=T[F^0], and let j be
the distinguished descendant leaf at that hole. No other leaf is identified
with j, even if its component is equal.

Graft bare l at j, then graft σ into its template variable leaves, using
identity entries at all other leaves. Call this latter forest H. On the r
side use the corresponding forest H'; l and r have exactly the same ordered
template frontier, so H and H' are the same specified tuple in that common
frontier, with identity entries outside the hole. B1 composition gives

    R(T,F)=R(T,F^0);R(B,j:l);R(B[l]_j,H),
    R(T,F')=R(T,F^0);R(B,j:r);R(B[r]_j,H').

MOut for the bare equation inside B and the arbitrary forest H, already
proved in §4.1, reads

    B[e]_j;R(B[r]_j,H')=R(B[l]_j,H);z.

Insert this equality into the first factorization. Then bare MIn at B,j gives

    R(T,F);z
      =R(T,F^0);R(B,j:l);B[e]_j;R(B[r]_j,H')
      =R(T,F^0);R(B,j:r);R(B[r]_j,H')
      =R(T,F').

This proves the contextual and arbitrary-substitution case from the seven
bare-template families. It did not posit equality of semantically equal
forests. It remains valid for σ with nullary entries: the corresponding
external positions disappear on both sides, and no rule variable is duplicated
or removed as a syntactic occurrence. ∎

An inverse forest-entry equation satisfies the reverse equality by invertibility.
Applying Lemma 4.1 successively proves (4.3) for a path in one entry. Applying
it at the finitely many original entries, in their fixed order, proves:

**Corollary 4.2.** If F_i and F'_i are pointwise E-equivalent, then there is a
pure equation path z:T[F]→T[F'] with

    R(T,F);z=R(T,F').                                    (4.4)

Every such z is κ(T[F],T[F']) by Theorem 3.2. In particular the result is
independent of chosen entry paths and their interleaving. For an empty original
frontier the statement is the equality of empty forests and identity paths.

## 5. Independent comparison functors and exact commuting squares

Define P_Q on objects by T↦pi(T). On a graft edge inserting g at leaf i, its
arrow tuple has pi(g) at i and identity operations at all other original
positions. On a general raw arrow it is (pi(F_i)). On a positive or negative
equation edge it is the identity tuple, regarded between the equal quotient
operations pi(T)=pi(U).

These generator images have the required endpoints by strict preservation of
substitution by pi. We verify every relation before forming the induced functor:

* Raw identity/composition relations become the B2 identity and entrywise
  forest-substitution laws, with the same descendant occurrence split.
* Equation inverse relations become identity composed with identity.
* Every O relation has only equation edges and maps to the same identity
  tuple at its common source operation; source/target profiles agree.
* Both sides of MOut map to the full tuple (pi(F_i)), in the same original
  occurrence positions. An equation changes neither that profile nor the
  individual profiles of F_i.
* In MIn, the two tuples agree outside i and have entries pi(l),pi(r) at i.
  Those entries are equal by the declared A3 equation. Thus the complete
  tuples agree; this argument does not equate arbitrary tuples having a
  common total composite.

Therefore P_Q:C→Ref(Q,W) is a well-defined functor. Define

    P_D=Ref(Phi)∘P_Q:C→Ref(D,W).

Its raw forest action is (ev(F_i)); its equation action is the identity tuple.
Let J:Raw(S,W)→C be the identity object map and raw arrow inclusion. The two
comparison equations are, on both objects and actual arrows,

    P_Q∘J = Ref(pi)∘(Raw≅Ref(F(S))),
    P_D∘J = rawEvaluation(ev),
    P_D   = Ref(Phi)∘P_Q.                                (5.1)

For example, at F:T→T[F], both sides of the second equality are the original-
slot tuple (ev(F_i)), with the same entire entry profiles. Preservation of
composition on either route is exactly

    ev(F_i[H_(i,j)]) = ev(F_i)[ev(H_(i,j))].              (5.2)

This equality is the inherited strict-calculus law at the canonically split
pair (i,j), not merely equality of endpoint operations. The identity equation
is equally entrywise. Equality-transport proofs add no new tuple data.

## 6. Mixed path normal forms and complete hom equality

### 6.1 Moving all equations to the right

**Lemma 6.1.** Every finite mixed path p:T→U is equal in C to

    R(T,F);z,                z:T[F]→U pure equation.      (6.1)

**Proof.** Induct on the finite word p. Start with the identity forest and
empty z. Appending an equation edge concatenates it to z. If appending an
elementary graft A:U→U[A], use (4.2):

    R(T,F);z;R(U,A)
      =R(T,F);R(T[F],A);z[A]
      =R(T,F⋆A);z[A].

Here A is read on the common frontier of T[F] and U, and F⋆A splits A by
the actual descendants of the original entries. This produces the next
factorization. The induction covers inverse equation edges by (4.2). ∎

By §3, the final z in (6.1) is necessarily κ(T[F],U).

### 6.2 Canonical entrywise forest

Write F↓ for the forest with (F↓)_i=(F_i)↓. It has exactly the same separately
specified entry profiles as F. Corollary 4.2 and ordinary coherence give

    R(T,F);κ(T[F],U)
      =R(T,F↓);κ(T[F↓],U).                              (6.2)

For clarity, the path α:T[F]→T[F↓] supplied by Corollary 4.2 satisfies
R(T,F);α=R(T,F↓). Ordinary coherence yields
κ(T[F],U)=α;κ(T[F↓],U), which proves (6.2).

Thus for fixed raw endpoints T,U, a canonical arrow representative has shape

    A(T,U;F↓):=R(T,F↓);ν_(T[F↓]);(ν_U)⁻¹,              (6.3)

where the two middle normal-form objects are literally the same. The data
of this representative are an ordered family of normal terms, one at EACH
original source occurrence. The endpoint condition is pi(T[F↓])=pi(U).

### 6.3 The exact equality theorem

**Theorem 6.2.** Let p,q:T→U be arbitrary mixed paths. Compute their normal
families F↓,H↓ by §§6.1–6.2. Then the following are equivalent:

1. p=q in the independently presented category C;
2. F↓_i=H↓_i at every original occurrence i of T;
3. P_Q(p)=P_Q(q) as full semantic refinement arrows;
4. P_D(p)=P_D(q) as full semantic refinement arrows.

**Proof.** (2) makes the canonical representative (6.3) identical, proving
(1). A well-defined functor gives (1)⇒(3) and (1)⇒(4). If (3) holds, full
tuple equality says pi(F_i)=pi(H_i) at every original i, after the same
canonical source-profile transport. Equation (1.2) gives F_i↓=H_i↓, proving
(2). The identical argument with ev gives (4)⇒(2). No cancellation of the
outer T operation is used. ∎

The theorem proves, rather than defines, the presentation's relation on paths.
A normal entry retains its output component, individual frontier and length,
ordered cut partition, complete frontier arrow string, and monoid value.
Consequently equal total composites, equal total monoid products, or equal
component labels at distinct positions are not criteria for arrow equality.

### 6.4 Explicit hom inverse and equivalence

Given b:P_Q(T)→P_Q(U), use the exact-profile canonical representative

    F_i=N(Phi(b_i)).

The defining semantic endpoint and strictness give
pi(T[F])=pi(U), so κ(T[F],U) is defined. Set

    H_Q(b)=R(T,F);κ(T[F],U).                             (6.4)

Then P_Q(H_Q(b))=b entrywise. Conversely, Theorem 6.2 implies
H_Q(P_Q(p))=p for every p:T→U. These are explicit two-sided hom maps.
There is no assumed categorical lifting property: each endpoint is derived
from the given tuple equation and inherited semantic completeness.

Every Q operation has a raw representative and every D witness w has N(w).
Therefore P_Q and P_D are full, faithful and surjective on object isomorphism
classes; indeed their object functions are surjective as maps of sets. They
are not injective on objects: distinct raw trees such as the two binary
associativity groupings have the same quotient value. Hence they are
**equivalences**, not raw-object isomorphisms.

The analogous H_D uses F_i=N(b_i). Define S:Ref(D,W)→C by S(w)=N(w) and
S(b)=H_D(b) at these endpoints. Its identity law follows directly from
N(identity)=the identity leaf, raw identity, and κ(T,T)=id. For composable
b:a→a', d:a'→a'', the composite S(b);S(d) has, by the mixed-normalization
calculation, entrywise class

    N(b_i)[N(d_(i,j))].

Its normal term is N(b_i[d_(i,j)]) by inherited substitution soundness and
completeness. Formula (6.3) therefore equals S(b;d). This proves composition
on full arrow data, rather than only on their endpoint witnesses.

The equation P_D∘S=id is literal on operations and tuples. The maps

    η_T:=ν_T:T→N(ev(T))

form a natural isomorphism id_C⇒S∘P_D. For p:T→U both p;η_U and
η_T;S(P_D(p)) have the same full tuple under P_D, so Theorem 6.2 (now proved)
identifies them. This use of established faithfulness is a proof of coherence,
not a hypothesis. Its inverse is (ν_T)⁻¹. At canonical objects ν is empty,
and P_D(η_T) is the identity tuple. Thus both triangle compatibilities hold.

Finally let C_nf be the **full subcategory** on actual irreducible trees.
Every such tree is the uniquely labelled N(w), and ev(N(w))=w. The restriction
P_D:C_nf→Ref(D,W) and S have inverse object and arrow maps, hence are an
actual category isomorphism. No quotient of the object set is silently added
to the original completion.

## 7. Effective basis and terminating arrow equality algorithm

For fixed finite tables N,K,M the colour and primitive-generator sets are
finite, as are the bare equation labels and the 18 critical shapes. All
remaining infinitude is in finite terms, contexts, addresses, forests and
words. Enumerate these by total constructor count, then finite lexicographic
code. Check component/profile equalities, graph partitions and monoid/category
tables directly. This enumerates all well-typed Rcat, O, MOut and MIn instances.
The classification in §3 and derivations in §4 prove that no unbounded
context or forest case is omitted by that effective schema presentation.
Nothing asserts that the entire category or all arities are finite.

A direct arrow decision algorithm takes a finite generator word and raw
endpoints:

1. Validate each generator's actual source/target, rule instance and occurrence
   address in sequence. Reject ill-typed words, mismatched whole components,
   illegal nullaries, or wrong repeated-leaf positions.
2. Initialize one identity term F_i at every original leaf of T. For an
   equation edge, leave this family unchanged. For a graft edge at a current
   leaf, use the lengths and full ordered profiles of the current F_i to locate
   its unique descendant pair (i,j), and insert that primitive corolla in F_i.
   This is the constructive induction in Lemma 6.1. Current raw word endpoints
   are tracked separately and validated, so an equation cannot invent a graft
   address. When there are no original leaves there can be no graft edge.
3. Normalize each final F_i with the inherited terminating algorithm. Return
   the full normal family as the key at the fixed endpoints T,U.
4. Compare two keys entrywise, including profiles/labels. By Theorem 6.2 the
   keys agree exactly when the arrows are equal in C.

The procedure processes a finite word and finitely many terminating term
normalizations; it does not enumerate equation paths or search for a semantic
lift. Optional canonical proof words can be produced from the constructions
in §§3–6. The existence of those derivations is what licenses the faster key
algorithm; the key was not used to define C.

## 8. Necessity and a precise minimality statement

Let B be the free category on the same graft/equation generating graph, with
equation inverse relations and Rcat imposed, but no O or mixed relations yet.
The generator assignment to Ref(D,W) is already a functor P_B:B→Ref(D,W).
Let K_loc be the category congruence **generated syntactically** by O, MOut
and MIn. Sections 2–7 prove

    K_loc = kernel congruence of P_B on every fixed hom. (8.1)

Equation (8.1) is a theorem: soundness gives one containment and the complete
normal-form proof gives the reverse. It was not the definition of K_loc.

Now consider any candidate B/R on this SAME generating graph, where R is a
specified set or effective schema of local relations, each sound under P_B.
No full/faithful comparison, cancellation, or lifting condition is included
in this candidate class. Soundness is the independently checkable statement
that each proposed relation has equal full tuples. The induced P_R is always
full and essentially surjective: the path (6.4) exists already as a word in B,
and its endpoint follows from the term presentation, regardless of R.

**Theorem 8.1 (local necessity and sufficiency).** The comparison P_R is
faithful, and hence an equivalence, if and only if every displayed O, MOut,
and MIn equation holds in B/R.

**Proof.** If P_R is faithful, the two sides of each listed local relation
have equal P_R-images by the explicit checks in §5, hence must be equal in
B/R. Conversely, if those local equations hold then K_loc is contained in the
congruence generated by R. Soundness of R and (8.1) give the reverse
containment. Thus the congruences agree and Theorem 6.2 applies. ∎

This characterizes a sufficient and necessary **local equational entailment**
criterion, not a decidable test for arbitrary alternative R. Effective
enumerability of an arbitrary presentation does not make all its entailments
decidable. The particular complete basis K_loc has the separate effective
equality algorithm of §7. Nor is every listed family claimed independent:
a family derivable from the others is honestly redundant, not a new obstruction.

## 9. A uniform obstruction when forest-entry compatibility is omitted

Let C_minus be the same completion with all O and MOut but **without MIn**.
For every raw forest F define |F| as the sum of its primitive-vertex counts.
For an elementary graft its contribution is 1; for either equation edge its
contribution is 0. Give a finite mixed word the sum of these contributions.
This defines a functor

    wt:C_minus→B(N,+),                                   (9.1)

where B(N,+) is the one-object category with natural-number endomorphisms:

* Equation inverses and every O relation have weight 0.
* Raw composition has |F⋆H|=|F|+|H|, because every primitive vertex of the
  second forest is inserted once at an actual descendant leaf. Independent
  history interchange therefore preserves the sum.
* The two sides of MOut use exactly the same inserted elementary corolla,
  so both have weight 1; its derived arbitrary-forest version has weight |F|.

These verifications include graph labels, units and repeated occurrences;
wt deliberately ignores them without changing the count argument.

Suppose the parameter class has a component W. For every integer k≥0 let
v_k=d_1^k(x_W), with v_0=x_W. The mixed word

    ℓ_k=R(x_W,v_k);(D0 at the root repeated k times)       (9.2)

is an endomorphism of x_W in C_minus. Its weight is k, so ℓ_k≠ℓ_j for k≠j.
Nevertheless its full semantic refinement tuple is the singleton identity:
ev(v_k)=identity_W. Therefore P_minus is not faithful and has infinitely
many spurious endomorphisms above that one identity arrow. This holds for
EVERY finite commutative M, including the trivial monoid, every N admitting
W, and every nonempty K. In particular it holds on the entire required
nondegenerate graph family, not only a unary toy: insert v_k at either of the
two nonempty repeated middle occurrences of the six-vertex four-leaf example
and keep the other original entries identity. The same invariant gives
unbounded spurious loops at that mixed-interface object.

The obstruction is exactly failed pointwise equation compatibility for newly
grafted material. MIn for D0 makes R(T,i:d_1(x));D0=id_T; iteration removes
all ℓ_k, and §§4–6 show that the complete repair removes exactly semantic
tuple equalities and no others. In particular it does not identify unequal
local monoid-value tuples merely because their products agree. This supplies
a repaired positive theorem on the same full unbounded parameter family,
not an obstruction substituted for C5's mandatory positive presentation.

## 10. Other discriminating boundaries and examples

### 10.1 A precisely specified object-only quotient fails

A thin reachability quotient whose objects are semantic witness classes and
whose homs merely say that some raw representatives refine has at most one
arrow per fixed pair. It cannot recover the present Ref(D). For example use
the six-vertex four-block cut with grades (a,id_1,id_1,b) and M=Z/3 additively,
source value 0. At its four original occurrences compare unary local-value
tuples (0,0,0,0) and (0,1,2,0), leaving all block partitions unchanged. Both
are arrows to the SAME full target witness of total value 0. They differ at
each of the two repeated middle occurrences and are unequal by B2 tuple
equality and Theorem 6.2. The repaired completion retains both. Thus this
named object-only candidate fails on witness information, not on a change
of whole or target profile.

### 10.2 Ordinary localization needs path coherence

Before O or mixed relations, the free groupoid on equation steps retains
a nontrivial loop at d_1(d_n(x)) obtained by the D0 edge followed by the inverse
of the distinct DA edge. Both edges have the same target d_n(x). This reduced
edge word is nonempty, hence is not the free-groupoid identity, although its
semantic tuple is the identity. Row 7 of O fills exactly that peak. This is
a diagnostic for ordinary localization without coherent relations; no claim
is made that row 7 remains independent after *every* mixed relation is added.

### 10.3 Rotation really identifies internal structure

The two distinct raw binary groupings c(c(x,y),z) and c(x,c(y,z)) have the
same retained three-block full witness but different internal vertices and
raw prefix order. R gives their coherent equation isomorphism in C. Refining
different original occurrences of an outer binary cut yields distinct tuples
even when this rotation makes their final operation classes equal. That is
exactly the difference between the B1 thin raw category and the completed
semantic category, not artificial chronology arrows.

### 10.4 Rotation, units and scalar aggregation do not imply movement

For a concrete undeclared-equation separator, take M={1,e}, e²=e. Remove both
DL and DR, retaining R,UL,UR,D0,DA. Interpret every component by the set
{0,1}; every binary cut by Boolean OR; u by 0; d_1 by the identity function;
and d_e by the constant-0 function. This is a typed multicategory model with
all component carriers equal but their types retained. OR is associative and
unital, and the two unary functions satisfy the prescribed monoid action, so
all retained declarations hold. At inputs x=0,y=1,

    c(d_e(x),y)=1,          d_e(c(x,y))=0.

Thus the DL equation is not derivable from those retained declarations.
The full graph-cut semantics equates the terms because both retain total
value e and the same full cut. This negative control shows why the mixed
object presentation needs the movement equations; it is not another proof
of their already inherited positive completeness.

### 10.5 A witness-collapsing parameter map need not be faithful

Let h:M→M' be a monoid homomorphism with s≠t but h(s)=h(t). At any binary cut
of value 1, take the two unary-entry tuples (d_s,d_t) and (d_t,d_s). They have
the same target full cut of value st=ts but are unequal tuples. After h, their
entries agree. This works for arbitrary commutative monoids, not only groups
or cancellation models; the six-vertex repeated-component context embeds it
without empty principal blocks. Compatibility of the comparison with h
therefore cannot mean that every h induces an equivalence or reflects arrows.
The separate parameter-transport proof must preserve this distinction.

## 11. General criterion and scientific disposition

The syntactic proof used only: a finite typed planar signature; parallel
same-order, once-each variable templates; a terminating decidable contextual
rewrite relation; complete effective local-peak fillers; the ordinary raw
forest category; and the two explicit mixed families. These are structural
hypotheses, not categorical full/faithful conclusions. They give the same
comparison with Ref(F(S)/E) on that general class. For the mandatory family,
all are instantiated explicitly: matching/termination/object completeness are
inherited A4 proofs, the full local O words are §3.1, and the mixed extensions
are proved in §4. No convergent-basis hypothesis is silently imposed on
arbitrary extra equations or on unrestricted monoid presentations.

The exact ordinary-coherence baseline is Samuel Mimram, *Rewriting techniques
for relative coherence*, Logical Methods in Computer Science 21(3:7), 2025,
§3.2, Definitions 3.11–3.15 and Propositions 3.16, 3.19–3.20 (pp. 7:18–20).
In its abstract 2-rewriting system take objects to be our typed terms, edges
to be contextual positive rewrites, 2-relations to be the O fillers, and its
designated W to be all those edges. Inherited termination and §3.1 verify the
terminating/coherently-locally-confluent hypotheses. Proposition 3.16 yields
coherent confluence; Propositions 3.19–3.20 yield normalization-path
compatibility and equality of parallel equation zigzags. Lemma 3.23 supplies
the normal-object inclusion equivalence for his presented GROUPoid. Our Comp
also has noninvertible grafts, so its normal-object equivalence in §6.4 is
not literally an application of that groupoid-only lemma: it uses the same
elementary categorical argument that the full subcategory contains an object
isomorphic to every object. This abstract O application imposes no ban on
nullary term objects. Thus §3.2 is a direct instantiation/reproof, and the
normal-subcategory argument is standard as well, not a new coherence principle. Actual mixed
raw-graft relations and full tuple comparison still require the checks given
here; their packaging alone does not establish originality.
[Published primary source, §3.2](https://lmcs.episciences.org/16103/pdf).

This is a coherent-presentation/category-of-substitutions construction. The
ordinary normalization and local-peak-to-path-coherence mechanism are standard
mathematical infrastructure; the present dossier verifies the exact
occurrence-linear, unit-sensitive mixed presentation and the actual full
arrow comparison required here. It claims no new general categorical theorem
or scientific significance merely from that verification. In particular,
the monoid-enriched flat model is separately to be compared with the standard
profile-typed product, and Ref with its corresponding profile-typed pullback.
Those semantic product facts and elementary multiplication fibres must not be
counted as independent contributions. If the strongest baseline comparison
exhausts the surviving increment, the correct outcome is a Gate 2 direction/
significance decision, not a renamed novelty claim or full-bundle acceptance.

The P proof is complete for its stated technical comparison. Mandatory L and
independent C support, source audit, independent correctness/depth review,
fresh reproduction, transport proofs, and the parent's final acceptance
remain separate evidence obligations. This author document cannot promote
itself to ACCEPTED or activate B4/F or any other deferred phase.
