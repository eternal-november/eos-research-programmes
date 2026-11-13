# E3 — Substantive graph-cut and graph–span virtual equipments

31 October 2026. Author P proof for original contract E3, lines 450–466.

**Result.** For every finite groupoid K, graph bound N≥0, and finite commutative
monoid M, the graph-cut construction G(N,K,M) below is a full virtual equipment.
Its horizontal arrows retain a whole ordered graph and an actual interface
arrow. Its cartesian restriction of grade h along f,g is **g⁻¹hf**, with a
unique lift that retains the actual ordered partition and scalar, not merely
existence of a cut. Independently, S(N,M), with all finite sets and functions
vertically and actual finite spans horizontally, is a full virtual equipment
with genuinely noninvertible vertical maps. It retains multiple apex witnesses,
whole graphs, ordered cuts, and scalar values. The faithful finite-Yoneda graph
span comparison is bijective on every cell fibre over its full image profiles
and boundaries; it preserves chosen restrictions by an explicit coherent
isomorphism, not by a false literal equality of pullback sets.

Both models can lack any composite of a genuine two-nonempty-graph path in
the **unchanged horizontal universe**, despite possessing all cartesian
restrictions and universal units. We classify their opcartesian cells, give
positive universal assemblies and nonuniversal witnesses, recover the original
C1/C5 calculus and its occurrence-sensitive refinement categories, and compute
actual cut and interface-change fibres. These computations are used, not merely
mentioned, in E2 separation/reconstruction and the E4 representability boundary.

**Evidence boundary.** This is the uniform mathematical proof, not a claim that
all of it is Lean-formalized. The separately authored formal bridge, finite
certificates, prior-art comparison and independent audit have their own scope
records. No E4 ordinary-completion theorem, unrestricted Segal/interchange
claim, novelty claim, historical-ledger change, or upload is asserted here.

## 1. Sources, conventions and information retained

The principal inherited proofs are:

* **C1:** `research/workstream_C1/proof/C1_Model_Theorem.md`, §§1–7, for the
  independently defined whole-graph/arrow/ordered-partition calculus and its
  increasing-restriction and occurrence-substitution laws.
* **C5:** `research/workstream_integration/proof/Semantics_Transport_Factorization.md`,
  §§1–2,6, for the global M decoration and actual refinement/cut scalar fibres;
  the original local presentation and quotient/core comparison are credited
  there, not replaced here by the kernel of an interpretation.
* **SPAN:** `structural_extracted/GraphSpanModel.md`, §§1–9, supplies the
  substantive second model, all its universal-property proofs, the faithful
  original-core comparison and the graph/scalar obstructions. We reuse and
  state their actual formulas below rather than count them as new constructions.
* **ENV/EXT and accepted E1/E2:** the accepted E1 axiom system, E2 universal
  chosen-envelope theorem and graph–span local-presentation reconstruction;
  exact paths and sections are in `source_obligation_map.md`.
* **D2/D3/I4:** the completed actual-coefficient and retained-diagram results,
  used only at their stated labelled, boundary-compatible scope in §9.

The conventional equipment baseline is Cruttwell–Shulman, *A unified framework
for generalized multicategories*: Example 2.7 (span multicells), Definition 5.1
(contextual opcartesianness), Definition 7.1 (cartesian restrictions), Definition
7.6 (virtual equipments), and Theorem 7.24 (cartesian preservation). The
companion literature comparison verifies exact primary-source locations.
The standard machinery, the equation gk=hf, finite Yoneda, and pullbacks are
not novelty claims. The work here is their explicit compatibility with the
retained full C1/C5 witnesses and the stated failure boundaries.

Use E1's small/set-sized classical conventions. Finite sets are actual tagged
sets in a fixed small universe closed under the finite tuple constructions;
functions, spans and cells are not divided by isomorphism. Fix ordered simple
undirected graphs on [r]={0,…,r−1}, r≤N, with literal vertex-count and edge
relation equality. The full graph family is used for the negative classification.
The existence/law proofs also work for any induced-closed graph family; the
negative cross-edge argument then requires that family's stated cross-edge
freedom. If U⊆[r], let i_U be its increasing enumeration. We use

    i_(i_U V)=i_U i_V,       (G|U)|V=G|i_U V.                (1.1)

C1 proves these by uniqueness of increasing enumeration. Empty graphs, empty
blocks and empty source paths are different data. The full path retains every
intermediate interface and every occurrence, including repeated equal components.
No bound on arity, tree depth or number of empty slots is imposed.

Composition βα means first α then β. For a path p with grades h_1,…,h_n,
write c(p)=h_n⋯h_1, and c(()_A)=id_A. A cell with source p:A_0⇒A_n, output
H:B⇒C, and vertical boundaries f:A_0→B, g:A_n→C is written
`Cell(p;H | f,g)`. Substitution rows include **all** shared boundary maps,
including the sole precomposition map for an outer nullary. All equalities
compare the actual witness data; proofs of typing equations are not extra data.

## 2. Primary model G(N,K,M): all cells and substitution

Let K be a finite groupoid and M a finite commutative monoid with identity 1.
Objects and vertical maps are exactly K. A horizontal is an actual pair

    (G,h):A⇒B,                h∈K(A,B), |G|≤N.             (2.1)

For p=((G_i,h_i))_(i=1)^n and H=(G,h):B⇒C, the cell set consists of pairs

    (U,m),   U=(U_1,…,U_n), m∈M,                            (2.2)

where U is an ordered partition of the entire actual vertex set of G,
`G|U_i=G_i` exactly, and

    g c(p)=h f.                                            (2.3)

Thus the full cell is indexed by the whole H, the complete path p, and both
boundary arrows; neither the whole nor its cross edges are reconstructed from
its pieces. At n=0, U is empty and G must be empty, but f and g need not be
equal: the equation is g=hf. This is an ordinary nullary-source cell, not an
augmented nullary-target cell. Each fixed fibre is finite.

Let α=(U,m):p⇒H have boundaries f,g. A composable row has cells
β_i=(V_i,n_i):q_i⇒(G_i,h_i) with boundaries u_(i−1),u_i, where
u_j:C_j→A_j. Define

    α[β_i] = ( (i_(U_i)(V_(i,j)))_(i,j), m∏_i n_i ),        (2.4)

with expanded source q_1⋯q_n and boundaries fu_0,gu_n. Each child equation
is u_i c(q_i)=h_i u_(i−1); multiplying these in path order gives

    u_n c(q_1⋯q_n)=c(p)u_0.                                (2.5)

Consequently gu_n c(q)=hfu_0. This proof needs no cancellation; empty q_i
contributes c(q_i)=id and its equation u_i=h_i u_(i−1), not an erased
boundary condition. The lifted blocks partition G and have the correct
graphs by (1.1). For n=0 a row is one map u:C→A and no child cells;
α⟨u⟩ retains its empty U and scalar m and has sides fu,gu.

The identity on (G,h) is the full singleton block with scalar 1 and identity
sides. Right and left identities follow by lifting along the full block and
multiplying by 1. For three levels, every final block is the same subset by
(1.1); every final occurrence is visited in the same lexicographic order;
(2.5) equates the boundary grades. Each scalar is the product of exactly the
same outer, middle and inner vertex scalars, including nullary scalars.
Associativity and commutativity of M equate the two products. Thus all E1
virtual-double-category axioms hold at arbitrary arity and depth. This is
C1/C5's actual substitution extended to full boundary sorts, not a new
reachability relation.

## 3. Cartesian restrictions, units, choices and exact marks in G

### Theorem 3.1 — witness-level cartesian restriction

For H=(G,h):B⇒C and f:A→B, g:D→C, set

    H[f,g]=(G,g⁻¹hf):A⇒D.                                 (3.1)

Choose κ:H[f,g]⇒H with sides f,g, the full singleton block, and scalar 1.
Its grade equation is g(g⁻¹hf)=hf. For every finite p:X⇒Y and u:X→A,
v:Y→D, composition with κ is a bijection

    Cell(p;H[f,g] | u,v) ≅ Cell(p;H | fu,gv).               (3.2)

**Proof.** A right-hand cell has equation gv c(p)=hfu. Left multiplication
by g⁻¹ gives v c(p)=(g⁻¹hf)u, exactly the left-hand equation. Its unique
lift is **the same ordered partition U and the same scalar m**. Conversely
multiplication by g restores the original equation. Substitution through
κ leaves U unchanged and multiplies its scalar by 1. Any lift factoring to
the specified cell must therefore have exactly that U and m. This is actual
witness equality, not uniqueness only after forgetting decoration. At n=0,
c(p)=id_X and U is empty; the same equation proves the whole nullary fibre,
including u≠v. The lift commutes with arbitrary substitution because the two
routes have the same lifted blocks and scalar, or by uniqueness in (3.2). ∎

Here choices can be split: the identity restriction equals H, and

    (H[f,g])[u,v]=H[fu,gv],
    v⁻¹g⁻¹hfu=(gv)⁻¹h(fu).                                (3.3)

The corresponding cartesian cells compose identically. Any other cartesian
choice is uniquely isomorphic to this one over H: lift each cartesian cell
through the other, and their composites are identities by uniqueness. All
finite comparison coherence follows by the same uniqueness. We do not infer
such a formula for arbitrary finite categories: g need not be invertible
there. Section 6 gives the specified span envelope instead.

### Theorem 3.2 — universal units in every surrounding context

Set I_A=(empty,id_A), and η_A:()_A⇒I_A to have empty partition and scalar 1.
For any prefix r and suffix s meeting at A, substitution of η_A gives a
bijection

    Cell((r,I_A,s);H | f,g) ≅ Cell((r,s);H | f,g).           (3.4)

Indeed the I_A position has the unique empty block, and inserting/deleting
that **specified** empty block is inverse; insertion/deletion of its identity
grade leaves (2.3) unchanged. The scalar remains m. This proof works with
empty r or s, arbitrary outside f,g, repeated components, and other empty
blocks. Multiple insertions commute by their actual occurrence positions;
(1.1) proves compatibility with substitution. Thus η_A is contextual
opcartesian, not merely a weak composite or a nullary satisfying unit equations.
Other nullaries of scalar m remain distinct. In particular a nullary of
nonunit scalar is not silently declared universal. ∎

Together §§2–3 prove that G(N,K,M) is a **full virtual equipment**, without
assuming any nonnullary horizontal composite exists.

### Markings

Admissibility is the whole globular core, unless the explicitly named original
C1/C5 subcalculus is selected. Mark `Ex_op` as **all contextual opcartesian
globular cells**. Its complete decidable criterion is proved in §7:

    Ex_op(α:p⇒H) ⇔ s(p)≤1 and m is a unit in M,             (3.5)

where s(p) is the number of nonempty input graphs. The normalized exact
submark `Ex_op^1` additionally requires m=1. For cut/coefficient applications
use the separate `Ex_coeff` mark m=1; it concerns the forced identity-boundary
graph-span coefficient, which is bijective. It does **not** imply Ex_op when
s(p)≥2. We never call an arbitrary cut an opcartesian assembly.

## 4. Second model S(N,M): genuine noninvertible interfaces and apex witnesses

This is SPAN's existing V(N,M), renamed only to distinguish it from G.
Objects are all actual finite tagged sets and vertical arrows all functions.
A horizontal is

    (G,S):A⇒B,       S=(A ←l E →r B).                      (4.1)

The actual finite apex E and both functions are retained. For a path p of
spans define the boundary-marked compatible-tuple set

    P(p)={(a_0,e_1,a_1,…,e_n,a_n):
           l_i(e_i)=a_(i−1), r_i(e_i)=a_i}.
    P(()_A)=A,           π_0=π_n=id_A at arity zero.        (4.2)

A cell from p to (G,B←l E→r C) with sides f,g consists exactly of

    (U,φ,m),   U an ordered induced-graph partition,
    φ:P(p)→E,    lφ=fπ_0, rφ=gπ_n,    m∈M.                (4.3)

Equality retains **all three coordinates**. Different maps of witnesses and
apex automorphisms remain genuine cells. Nullaries require G empty and have
an actual function φ:A→E, both boundaries, and arbitrary m.

For a composable row β_i=(V_i,ψ_i,n_i) with common boundary maps u_i,
extract the q_i-subtuple z_i from z∈P(q_1⋯q_n). If c_i is the corresponding
boundary value, define

    T_β(z)=(u_0(c_0),ψ_1(z_1),u_1(c_1),…,
                          ψ_n(z_n),u_n(c_n)).             (4.4)

The shared u_i makes this tuple compatible. The composite cell has lifted
blocks i_(U_i)(V_(i,j)), coefficient φT_β, scalar m∏n_i, and sides fu_0,gu_n.
For an outer nullary T_β=u_0. The identity's coefficient is the unary tuple
projection ρ_H:P(H)→E. The full law proof is SPAN §3: (1.1) handles graph
coordinates; evaluation of both associations on a fixed final tuple applies
the same innermost, middle and outer functions to the same subtuples; the
same multiset of scalar factors gives equality. Empty subpaths retain their
own ψ_i(c_i) and boundary coordinate. These formulas explicitly establish
all laws, not merely the slogan that spans form an equipment.

### Theorem 4.1 — all-arity restrictions, with arbitrary functions

For f:A′→A, g:B′→B restrict (G,A←l E→r B) to the same graph and span apex

    E[f,g]={(a′,e,b′): f(a′)=l(e), g(b′)=r(e)}.            (4.5)

The legs are the first/third projections. The cartesian cell has the full
block, middle projection, and scalar 1. Given α=(U,φ,m) with boundaries
fu,gv, its unique lift has the same U,m and coefficient

    φ̄(z)=(uπ_0(z),φ(z),vπ_n(z)).                          (4.6)

The equations for α place the triple in (4.5); its first/third coordinates
are forced by the lifted boundaries and its middle coordinate by factoring
to α. Thus uniqueness is coordinatewise, including U and m, for every arity
and arbitrary f,g, including noninjective and nonsurjective maps. At arity
zero use π_0=π_n=id. This reproduces SPAN Theorem 4.1.

Identity and iterated restrictions are coherently, not literally, identified:

    (a″,(a′,e,b′),b″) ↦ (a″,e,b″),
    a′=u(a″), b′=v(b″).                                  (4.7)

The inverse inserts the displayed forced coordinates. They are endpoint-
preserving unary cells of scalar 1. Every finite coherence diagram deletes
or inserts precisely the same coordinates. No false strict equality of
nested tuples is assumed. Other cartesian choices compare by uniqueness.

### Theorem 4.2 — universal units

Choose I_A=(empty,A←id A→id A) and η_A with coefficient id_A and scalar 1.
Inserting I_A at a specified junction inserts an empty graph block and a
forced apex/boundary coordinate equal to the junction value a. Deleting them
is the inverse bijection P(r,I_A,s)≅P(r,s). Pulling an arbitrary output
coefficient back along this bijection gives the unique factor; the scalar
is unchanged. This holds for all r,s and all outer boundaries, including
r=s=(). It proves contextual opcartesianness, SPAN Theorem 5.1.

Thus S(N,M) is a full virtual equipment. A concrete noninvertible vertical
arrow is q:{0,1}→{*}, q(0)=q(1)=*. It has no inverse because any putative
inverse would make the constant composite on {0,1} its identity. Its
restriction cells still satisfy (4.6). Noninvertible interface change is
therefore **inside the actual model**, not represented only by an external
map between groupoids.

Its admissibility is the whole globular core; Ex_op is all opcartesian cells,
with criterion (§7)

    Ex_op(α) ⇔ s(p)≤1, φ bijective, m a unit.               (4.8)

Ex_op^1 additionally requires m=1. The separate coefficient mark Ex_coeff
means φ bijective and m=1, without the s(p)≤1 condition. These are explicit
predicates on full cells, not new identifications or selected-only cell sets.

## 5. Morphisms and faithful intermodel comparison

A structure morphism means an E1 VDC functor preserving units (normal),
with the stated preservation of extra markings. Chosen restrictions may be
preserved coherently; literal preservation is claimed only where formulas
justify it. Cartesian preservation is not asserted as a novel independent
axiom. Full faithfulness below always names its exact cell sorts; it is not
vertical fullness or essential surjectivity on ambient horizontals.

### 5.1 Parameter maps

For a functor q:K→L of finite groupoids and a unital monoid homomorphism
μ:M→M′, with the same graph bound, define G(q,μ) by

    A↦qA, f↦qf, (G,h)↦(G,qh), (U,m)↦(U,μm).             (5.1)

Equation (2.3), composition and identities are preserved. A groupoid functor
preserves inverses, so (3.1), κ and η are preserved literally with the chosen
formulas. Units of M map to units; therefore Ex_op, Ex_op^1 and Ex_coeff are
preserved. If q is faithful and μ injective, the map on each fixed source
cell fibre is injective and grade validity is reflected. It is surjective
onto that image-boundary/profile cell fibre when μ is surjective (and q
faithful to reflect the equation). Injectivity on horizontal names additionally
requires q injective on objects. Full equality recovery needs both conditions;
we do not silently infer them for arbitrary parameter maps. Reflection of
Ex_op holds if μ reflects units; it holds for injective maps of **finite**
monoids, because if μ(m) is invertible then some positive power of μ(m) is 1,
so the same power of m is 1 by injectivity. Reflection of scalar-1 markings
requires μ⁻¹(1)={1}. Enlarging N preserves these same structures and exact
markings by §7; it does not manufacture a composite of two nonempty graphs.

The analogous scalar map S(N,M)→S(N,M′) keeps every graph, span and function
and applies μ to the cell scalar. The same preservation/reflection statements
apply; its cell faithfulness is exactly scalar injectivity. These give actual
morphisms uniformly over the parameter families.

### 5.2 Finite faithful realization and the graph-span functor

For a finite category K (in this subsection initially a groupoid), define

    F(A)={(A,C,t): C∈Ob(K), t:C→A},
    F(h)(A,C,t)=(B,C,ht),        h:A→B.                     (5.2)

The sets are finite and tagged by A. Each contains (A,A,id_A), so distinct
object names give distinct sets. Functoriality follows from category laws;
if F(h)=F(k) for parallel h,k, evaluation at id_A gives h=k. Thus F is
faithful, generally not full. For groupoid maps F(g) is bijective.

For u:X→Y let Γu=(X←id X→u Y). Define

    J:G(N,K,M)→S(N,M),
    J(G,h)=(G,ΓF(h)).                                      (5.3)

For any full source path p, following the functions F(h_i) gives a canonical
bijection τ_p:F(A_0)→P(Jp), inverse π_0. It includes the n=0 identity map.
On a cell with boundaries f,g set

    J(U,m)=(U, F(f)π_0, m).                                (5.4)

The left-leg equation forces precisely this coefficient. The right-leg
equation is

    F(h)F(f)π_0=F(g)F(c(p))π_0,

which, since π_0 is bijective and F faithful, is equivalent to hf=gc(p).
Hence (5.4) is a **bijection on every full boundary cell fibre whose
horizontals and boundary maps are the images of the specified G profile**.
Reading U,m is its inverse. This includes arbitrary nonglobular and nullary
sorts, not just positive globular examples. Substitution commutes: both
coefficients are forced to be F(fu_0)π_0, while blocks and scalars follow the
identical lifted-partition/product formulas. Thus J is an actual VDC functor,
injective on named objects/horizontals and faithful on all these witnesses.
It does not say that every function between F(A),F(B) comes from K, that
ambient spans are graph spans, or that an arbitrary ambient refinement with
new intermediate horizontals is original.

The unit image is literally the chosen identity graph span. For restrictions,
let k=g⁻¹hf. There is an explicit invertible unary comparison

    θ_(h;f,g): ΓF(k) → (ΓF(h))[F(f),F(g)],
    a′ ↦ (a′,F(f)(a′),F(k)(a′)).                           (5.5)

It has scalar 1 and the full graph block. Its inverse is first projection:
in the pullback triple, the middle value is F(f)(a′) and bijectivity of
F(g) forces b′=F(k)(a′). It commutes with the cartesian cells since middle
projection gives F(f), precisely Jκ. Identity and successive restriction
comparisons commute because both insert the same uniquely prescribed
coordinates (or by cartesian uniqueness). This is coherent preservation,
**not** equality of the apex F(A′) with a triple set. J is normal and
preserves/reflects Ex_op, Ex_op^1 and Ex_coeff on globular cells by (3.5),
(4.8): their coefficient F(id)π_0 is a bijection and all graph/scalar data
are unchanged. Nonexistence of two-nonempty-graph composites is retained.

### 5.3 A precise witness-forgetting comparison

The finite relation equipment Rel has finite sets/functions vertically,
horizontals R⊆A×B, and one cell from R_1,…,R_n to T with sides f,g exactly
when every compatible relation path (a_0,…,a_n) implies T(fa_0,ga_n).
For n=0 this means T(fa,ga) for every a. Substitution is implication along
the row. Restrictions are inverse images along (f,g), and units are the
diagonal relations. The identity and contextual-unit bijections hold because
the relevant cell sets are propositions and the diagonal step is uniquely
forced. A finite path has universal composite its existential endpoint
relation; inserting or deleting the existentially quantified intermediate
values gives equivalence of the contextual implications. These formulas
prove the full equipment and representability assertions used here.

Define

    Q:S(N,M)→Rel,
    Q(G,A←E→B)={(l(e),r(e)):e∈E},                         (5.6)

and send each cell to the indicated implication, witnessed by applying φ
to any compatible tuple of apex choices. Such choices exist for every finite
relation path; conversely a tuple always gives a relation path. Substitution
and units are preserved. Pullback support is the inverse-image relation,
so restrictions are preserved as relations (not by retaining apex triples).
Ex_op is preserved: when (4.8) holds, the bijective φ makes target support
the composite support; unit scalars impose no issue after forgetting M.
But Q is not faithful, does not reflect opcartesianness, and forgets the
whole graph, partition, scalar, apex multiplicity and actual coefficient.
The following failures are explicit:

* The two wholes in §8 have the same relation images.
* Distinct scalar unary cells 1 and 0 over an identity span have the same
  relation image, although the scalar-0 cell is not opcartesian.
* The maps from a two-point apex to a one-point apex and its identity have
  relation-level universal images; Q cannot reflect coefficient bijectivity.

The intermediate projection S→Span(FinSet) forgetting just graphs and
scalars keeps actual apices/functions and preserves all selected universal
structures. It also fails to reflect graph/scalar universality. Neither
forgetful morphism is an information-preserving ordinary completion of the
witness calculus: it succeeds in representing paths by discarding precisely
the information which §§7–9 show cannot be erased.

## 6. Exact original-core and refinement comparisons

Let D(N,K,M) be **the independently defined original** C1/C5 core: horizontal
(G,h) and globular operations with ordered partition U, grade c(p)=h, and
scalar m, with C1/C5 substitution. For a groupoid K, its fibres, identities,
nullaries and substitution are exactly Core(G(N,K,M)); the identity comparison
is an isomorphism of full path-profile calculi, not merely a bijection on
component names. In particular a globular nullary exists only at
(empty,id_A), with one actual witness for each m. A nonidentity loop does
not become a designated unit.

For **any finite category** K, even noncancellative/noninvertible, (5.2) is
still faithful. The formulas (5.3)–(5.4) on identity-boundary cells give

    D(N,K,M) → Core(S(N,M)),                               (6.1)

bijective on every original horizontal-profile operation fibre. Indeed the
left identity leg forces φ=π_0; the right equation and faithfulness force
h=c(p). At n=0 it forces G empty and h=id_A, so no extra original-profile
nullaries appear. This is SPAN §6's explicit restriction envelope, not an
unsupported claim that an arbitrary C1 category has g⁻¹hf restrictions.
Original K embeds faithfully, not necessarily fully, into the finite-map
vertical category. It also reflects vertical isomorphisms. If F(h):F(A)→F(B)
is bijective, a preimage of (B,B,id_B) has the form (A,B,t), because F retains
the C tag; hence t:B→A and ht=id_B. The two elements (A,A,th) and
(A,A,id_A) have the same image under F(h), so injectivity gives th=id_A.
Thus h is invertible. Consequently every original noninvertible arrow maps
to a genuinely nonbijective function. The separate q in §4 also establishes
noninvertibility without assuming that K itself has any such arrows.

For a faithful functor q:K→L injective on objects, D(N,K,M)→D(N,L,M) is
bijective on each original-image operation fibre: graph data are identical
and faithfulness reflects q(c(p))=q(h). It need not cover new profiles using
arrows outside qK. This applies to the principal chain [2] embedded in the
three-object groupoid of §8; it does not identify their vertical categories.

**Refinement theorem.** For a fixed retained original whole W, each of these
full-profile comparisons induces an isomorphism of Ref(D)(W) onto the full
subcategory of the ambient globular refinement category on decomposition
objects whose entire component paths and whole lie in the named original
image. A refinement is an actual occurrence-indexed tuple (t_i) with its
complete child paths and equation a[t_i]=b. Each t_i lies in an original
operation fibre, hence has a unique preimage. The equation is preserved by
substitution and reflected by fibre injectivity. Tuple composition is
entrywise substitution, so both inverses are functors. Empty child runs,
repeated equal types, separate local scalars and all graph embeddings are
retained. This does **not** classify factorizations through arbitrary added
span horizontals, nor identify different tuples with equal evaluated root.

## 7. Sharp representability boundary and positive exact assembly

Write s(p)=number of nonempty input graphs and r=their total vertex count.
In this section graphs range over the full ordinary ordered graph family.

### Theorem 7.1

For either G(N,K,M) (on an actual path in K) or S(N,M), a path p has a
contextual opcartesian composite **iff s(p)≤1**. If s(p)≥2, it has no weak
opcartesian composite either. For nonempty K, G is representable on all
finite paths iff N=0; the same equivalence holds for S.

**Positive construction in G.** Let G_p be the unique nonempty graph, or
empty when all are empty. Let C_p=(G_p,c(p)). Its assembly has full block
at the unique nonempty input, empty blocks elsewhere, and scalar 1. In
any surrounding context, union the blocks belonging to the p substring.
Only one can be nonempty, so this gives the unique inducing G_p block;
the inverse splits it into that block and the specified empty positions.
The grade c(p) gives exactly the same outer equation in both contexts;
the scalar is unchanged. Hence contextual substitution is bijective.
At p=() this recovers the universal unit, including its actual interface.

**Positive construction in S.** Use

    C_p=(G_p,A_0 ←π_0 P(p) →π_n A_n),                     (7.1)

with coefficient id_(P(p)) and scalar 1. The same graph correspondence
applies. Compressing a substring tuple to its single stored apex in P(p),
or expanding it, is an endpoint-preserving bijection in any context. It
includes empty substrings. Output coefficient functions therefore factor
uniquely; scalars factor uniquely through 1. This is SPAN Theorem 7.1's
actual contextual, not merely context-free, proof.

**Negative proof.** If r>N, there is no cell with source p, since any
partition output must have r vertices. If r≤N and at least two graphs are
nonempty, put them in consecutive blocks of [r]. Let G⁰ have their induced
edges and no cross edges; let G¹ add an edge between chosen vertices of
two nonempty blocks. Both receive cells from p and G⁰≠G¹. In G choose
outputs (G^ε,c(p)), scalar 1. In S choose outputs
`(G^ε,A_0←A_0×A_n→A_n)` with coefficient z↦(π_0z,π_nz), scalar 1.
These functions exist even for empty tuple/endpoint sets. If κ:p⇒C were
weakly opcartesian, factoring these two cells would require unary globular
cells C⇒(G⁰,…) and C⇒(G¹,…). A unary graph partition is the full vertex
set, forcing graph(C)=G⁰=G¹, a contradiction. No scalar, span apex or
choice of restriction repairs it. For N=1 the two singleton path is blocked
by the bound; for every N≥2 the **genuine cross-edge** obstruction applies
in the unchanged universe. ∎

### Corollary 7.2 — classification of arbitrary assembly cells

If s(p)≤1, compare any globular α:p⇒H with the canonical composite κ_p.
Its unique unary factor is invertible iff its scalar is a unit in G, and
iff its coefficient is a bijection and its scalar a unit in S. An inverse
must invert those coordinates, and their coordinatewise inverses suffice.
If α itself is universal, the two factorizations between α and κ_p are
inverse by uniqueness. Conversely an invertible unary factor preserves
universality. This proves (3.5) and (4.8), including nullaries, for every M.
In particular unit tests on scalar values can change universality: the
same graph/profile/partition and coefficient with scalar 1 is exact while
scalar 0 in a monoid with nontrivial absorbing zero is not.

### Exact E4 contribution, without claiming E4 completion

This is a checkable model criterion: count the nonempty graphs, test the
finite coefficient table for bijectivity, and test scalar units. It gives a
parameterized genuinely nonrepresentable positive input class N≥2,
K nonempty, for which E4 must add horizontals or weaken its information
preservation. More precisely, no ordinary equipment with exactly the same
objects, vertical arrows and horizontal objects can be related by a functor
that fixes these names and is bijective on **every old full boundary cell
fibre**: a universal composite
in it would lift via those bijections to an old universal composite,
contradicting Theorem 7.1. This obstruction is at full-cell recovery, not the
weaker assertion that equality-conservative inclusions may add no new cells.
The S→Span→Rel comparisons show the actual loss alternative: both graph
wholes can acquire the same composite only after graph information has
been forgotten. This does not establish E4's mandatory positive ordinary
completion or its universal property; it supplies the nonrepresentable
class, exact obstruction and preservation test that such a theorem must use.

## 8. Concrete nonthin, nonreconstructive, three-interface instances

Use the **original C1 principal graph**, not a substitute empty example.
Take N=6, vertices 0,…,5, edges

    E⁰={01,12,13,24,34,45},       E¹=E⁰∪{05},
    U=({0},{1,3},{2,4},{5}).                                (8.1)

Both middle induced graphs are literally the ordered two-vertex one-edge
graph. Let K have objects 0,1,2 and arrows (i,j,σ), σ∈S_3; composition
is (j,k,τ)(i,j,σ)=(i,k,τσ), and inverse is (j,i,σ⁻¹). This finite groupoid
has 54 actual arrows. Let s=(01), t=(12), a=(0,1,s), b=(1,2,t).
Use full grade path

    (a,id_1,id_1,b),        output ba=(0,2,ts).             (8.2)

The faithful functor [2]→K sends its generating arrows to a,b. It recovers
the original chain-core profiles without claiming that chain arrows were
invertible in the original category.

Let M={1,e,0}, e²=1, 0 absorbing. The witnesses (U,1) over G⁰ and G¹
have **identical full input components and grade path**, but distinct
retained wholes and distinct output fibres. Leaves cannot reconstruct the
missing cross edge 05. Each also has separate scalar witnesses (U,e),(U,0).
The middle two components are equal, yet have separate occurrence addresses.
Refine slot 2 by ordered local blocks ({0},{1}); refine slot 3 by the
**opposite** proper cut ({1},{0}), all grades id_1 and scalar 1. The flat
lifted partition is

    ({0},{1},{3},{4},{2},{5}),                              (8.3)

retaining the reversed occurrence order in slot 3. Refining only slot 2
or only slot 3 gives distinct occurrence-sensitive refinements; replacing
both by identical component names does not merge them.

There are also distinct **parallel** refinement endomorphisms of the same
four-input witness: put unary scalar values (1,1,1,1), or (1,e,e,1), at
its four positions. Each preserves the full graph/grade profile, and the
product is 1 in either case, so each satisfies w[t_i]=w. The actual tuples
differ at both repeated middle positions. Their images under J remain
distinct because it retains each scalar and is fibre-faithful; their
images under Q coincide. Thus the monoid is not an irrelevant decoration.

For an explicitly nontrivial boundary restriction use any σ,φ,γ∈S_3,
with h=(0,2,σ), f=(2,0,φ), g=(1,2,γ). Then

    g⁻¹hf=(2,1,γ⁻¹σφ).                                   (8.4)

All types change as prescribed, and the noncommutative label order matters.
The lift of either principal graph witness (with appropriately typed
boundaries) keeps every actual block and scalar; it does not recalculate
a graph from leaves. The independent finite tests use noncommuting
permutations to distinguish (8.4) from reversed/order-dropped formulas.

An arbitrary principal witness (8.1) is **not** opcartesian: s(p)=4. A
separate unary witness on any H, with full graph block and scalar 0, is
not opcartesian even though its graph obstruction vanishes: postcomposition
sends unary scalars 1 and e to the same scalar 0, violating uniqueness.
The corresponding scalar-1 unary identity is universal. More substantively,
for any nonempty G take the two-input path ((G,a),(empty,b)). The cell to
(G,ba), with blocks (V(G),∅) and scalar 1, is a genuine contextual exact
assembly by Theorem 7.1. Its J-image has bijective coefficient and is
opcartesian in S. On this **same binary profile**, changing only its scalar
from 1 to 0 gives a nonopcartesian parallel witness: postcomposition by the
distinct unary scalars 1 and e again yields the identical scalar-0 cell.
Thus the genuinely multiary positive assembly has a nonuniversal companion
without changing any graph, grade, partition or coefficient. These positive
and negative witnesses coexist in each
full model; no nonuniversal primitive is discarded.

Finally, S has independent multiple **apex** witnesses: over one-point
interfaces take an empty-graph span with apex {x,y}. Its distinct unary
self-cells can use id or the transposition x↔y (both scalar 1); its nullary
cells can choose x or y. These are different full coefficients. The
transposition is invertible; a collapse {x,y}→{x,y}, x,y↦x is not.
Restrictions preserve their actual functions by (4.6); Q forgets them.

## 9. Cut, refinement and interface comparisons that use the witnesses

### 9.1 Exact original cut fibre

Fix an original full witness w=(G;U_1,…,U_n;h_1,…,h_n;m) and a specified
proper contiguous interval [i,j] of length at least two. Put U=∪_(k=i)^j U_k.
Any factorization through one intermediate **original** component forces

    C_w=(G|U, h_j⋯h_i).                                   (9.1)

The outer blocks are the outside U_k and their union U; the inner blocks
are i_U⁻¹(U_i),…,i_U⁻¹(U_j). Their induced graphs are correct by (1.1).
Thus only outer/inner scalars a,b vary, and reading them gives a bijection

    Fact_core,[i,j](w) ≅ {(a,b)∈M²:ab=m}.                  (9.2)

The inverse attaches them to those forced actual graph/grade cuts. This
classifies the full core-restricted fibre, **not** every ambient span
factorization. For m≠1, (1,m) and (m,1) are different factorizations. In
the example M={1,e,0}, the fibre over 0 is the five pairs with at least
one coordinate 0; the fibre over 1 contains (1,1),(e,e). All remain
different after J and after (6.1). For M={1} these fibres are singletons.
This is an exact decoration-dependent factorization boundary, not only
a count of decorated objects.

The stronger nongauge obstruction from SPAN §8 uses M={1,z}, z²=z:
(1,z),(z,1),(z,z) are distinct factorizations over z and cannot be made
equal by an intermediate invertible unary cell. Its only scalar unit is
1, and an original graph span has no nonidentity endpoint-preserving apex
automorphism because its left leg is the identity. Any zigzag of such
isomorphisms composes to that identity automorphism. Hence simply replacing
factorization sets by isomorphism classes does not remove the failure.

### 9.2 Exact interface-change fibre with noninvertible vertical maps

Take spans S:A←E→B and T:B←F→C and maps f:A′→A,g:B′→B,h:C′→C.
The canonical coefficient comparison

    P(S[f,g],T[g,h]) → (P(S,T))[f,h]                      (9.3)

forgets the lifted middle coordinate b′. Over an actual feasible target
tuple (a′,e,t,c′) its fibre is exactly

    {b′∈B′:g(b′)=r_S(e)=l_T(t)}.                          (9.4)

It is bijective iff every feasible middle value has exactly one lift,
surjective iff every such value has at least one. This includes empty
feasible support. For one-point A,B,C,E,F and B′={0,1}, g constant,
(9.3) is a two-point-to-one-point map. All cartesian restrictions exist,
but the exact-composite comparison is not invertible. Take all graphs
empty (or just one input graph nonempty) and scalar 1: both composites
are actual opcartesian assemblies by §7. The failure is therefore genuine
witness-sensitive base change, not a nonrepresentable graph artefact.
Rel sees only existential support and forgets this multiplicity.

For a longer finite run, the same proof gives a product of its internal
lift fibres. For a nullary unit the separate comparison is the diagonal
A′→A′×_A A′, invertible iff the boundary map is injective. One must not
replace that test by an empty internal product. On groupoid image maps all
F(g) are bijections, so the comparisons pass; the second model's q detects
the additional noninvertible-interface obstruction.

### 9.3 Retained cut/refinement diagrams

Use I4 only on its **actual labelled** coefficient branch: every occurrence,
proper cut certificate and elementary refinement stage is retained; no
arbitrary orbit descent or symmetric reorder is imported. For a proper cut
vertex v with actual bijective certificates β_v:P(S_children)→S_v and
β′_v:P(S′_children)→S′_v, define its comparison recursively by

    k_v=β_v P(k_children) (β′_v)⁻¹.                        (9.5)

At leaves k is the actual supplied coefficient φ; scalars multiply over
the named stages. Formula (9.5) is therefore a model-level function, not
an arbitrary bijection between equally sized sets. Here invertibility is
that of the **evaluated coefficient comparison over the retained provenance**;
it is not invertibility of the arity-changing occurrence-refinement forest.
For example a binary split can induce a bijective coefficient without
possessing an inverse forest contraction. At fixed interfaces it
is invertible stagewise when each retained leaf coefficient is bijective
and each scalar is a unit (or scalar 1 for the normalized submark). Under
interface change first factor through the cartesian reindexing (4.6),
and then use (9.3); its lift-fibre condition must also pass. A root map
alone can mask a failed retained stage, so no root-only converse is claimed.

The mixed comparison for two compatible planar cuts is induced by flattening
the same named atom tuples, then regrouping. Substituting the same retained
leaf functions before or after regrouping gives the same function pointwise;
(1.1) equates graph embeddings, and commutativity of M equates exactly the
same finite product. This proves the applicable cut/substitution squares
inside these models and supplies the concrete maps used by D2/I4. Reversed
nonparallel occurrence orders do not receive an invented comparison.
In the principal fixture, the graph pieces alone neither restore edge 05
nor distinguish the scalar tuples (1,1,1,1) and (1,e,e,1); the retained
data do. In the q example, relations cannot restore the two lifts (9.4).
The witnesses therefore do actual work in the comparisons.

## 10. Actual E2 use and exact limits

E2's accepted universal theorem constructs the chosen free envelope of the
original local presentation and supplies its interpretation into every
eligible chosen equipment. For finite groupoid K, G is such a target: send
original binary-cut generators to their actual partitions, scalar generators
to their M values, nullaries to η, restrictions to (3.1), cartesian factors
to the unchanged (U,m) of (3.2), and unit factors to insertion of the
specified empty block in (3.4). The C1/C5 local equations hold by §§2–3,
so this is an actual interpretation, not an assumed free target. Extension
then gives a functor Eval_G from the E2 envelope. Under the established
C5 presentation isomorphism Q≅D, its composite with the original-core map is
the identity comparison D≅Core(G) of §6. Thus

    i(a)=i(b) for parallel original cells ⇒ a=b,            (10.1)

by applying Eval_G. Distinct scalar refinements and the original graph
witnesses are separated by exactly their retained coordinates, not by a
terminal semantic observation. This establishes the stated equality-
conservativity use; fullness of the free C5-only envelope is not inferred.

For an arbitrary finite K use the actual core interpretation (6.1) into S
instead. E2's extension into a chosen target and the same fibre injectivity
prove (10.1) there, without adding fictitious inverses in K. Separately,
E2's **enlarged** span presentation reconstructs S: its generators are unary
span squares, unary scalars, binary graph cuts and the designated nullary;
the local square/monoid/naturality/rotation/unit laws yield the normal form

    u_(f,φ,g) d_m c_flat(U;p).                             (10.2)

The evaluation of (10.2) is exactly (U,φ,m) in (4.3). Equality reflection
requires every coordinate and the original full sort. Dropping φ, U, or m
would invalidate this inverse: §8 and §9 supply explicit collisions.
This is the accepted E2 reconstruction's substantive use of the same model,
not a new assertion that the smaller C5-only signature generates all spans.
The map J commutes with this evaluation by (5.4), and the change-of-choice
map is (5.5), which is compatible with the E2 coherent chosen/unchosen
comparison. Thus the connection includes actual cells and comparison maps.

No conclusion here identifies all Ex_coeff cuts with opcartesian composites,
changes the original horizontal universe to conceal nonrepresentability,
or replaces multiple witnesses/wholes by a posetal relation. The two main
families satisfy the full equipment axioms while retaining exactly the
obstructions and successes the E3 tests request.
