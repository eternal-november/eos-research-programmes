# A convergent mixed presentation of decorated typed graph cuts

Status: complete mathematical proof draft for non-author review. This supplies A4's semantic normalization dependency; it does not declare the whole C1/C5 or A4 obligation discharged.

## 1. Parameters and strict restriction convention

Let K be an arbitrary finite category, M an arbitrary finite commutative monoid with identity 1, and N a natural number. The statements below hold for every N; the principal certificates use N >= 6. Represent a graph by a simple undirected edge relation on [r]={0,...,r-1}, r <= N. Graph equality is equality of r and the edge relation, not unlabelled isomorphism.

For U subset of [r], let i_U:[|U|] -> [r] enumerate U increasingly. Define G|U on [|U|] by pulling edges back along i_U. For V subset of [|U|], write U[V]=i_U(V). Then

    i_(U[V]) = i_U composed with i_V,
    (G|U)|V = G|(U[V]).                                      (restriction)

These are literal equalities of increasing maps and ordered graphs: both enumerations are the unique increasing bijection onto U[V]; checking the two graph edge relations then gives the second equality. Disjoint unions of subsets below are set unions, not disjoint graph unions: all edges in the retained whole remain available.

The component (G,f) has interfaces A,B when f:A -> B in K. A profile is a full ordered list ((G_1,f_1),...,(G_n,f_n)) with f_i:A_(i-1) -> A_i. Intermediate objects and arrows remain part of that list even for empty graphs or identity arrows.

## 2. The independently defined semantic calculus

A flat witness from that profile to (G,f) is

    (G; U_1,...,U_n; f_1,...,f_n; m),

where (U_i) is an ordered partition of [r], allowing empty blocks, G_i=G|U_i, f=f_n ... f_1, and m in M. It retains G itself and the actual subsets U_i. For n=0 it exists only when r=0, A_0=A_n=A and f=id_A; its value m is arbitrary. Thus an empty graph with a nonidentity loop arrow has no nullary witness, and an empty graph with unequal endpoints has none either. For n=1 the partition is ([r]), f_1=f, and its possible witnesses are exactly the M-values. Identity is the unary witness with value 1.

Given an outer witness with blocks U_i and value m and, at each separate occurrence i, an inner witness on G|U_i with blocks V_(i,1),...,V_(i,k_i), arrow string (g_(i,j)), and value n_i, define substitution by

    blocks: (U_1[V_(1,1)],...,U_1[V_(1,k_1)],
             ...,
             U_n[V_(n,1)],...,U_n[V_(n,k_n)]),
    arrows: concatenation of the g_(i,j),
    value:  m times product_i n_i,
    whole:  the unchanged G and f.

Typing follows from (restriction) and composition in K. A nullary refinement of an occurrence is possible only at (empty,id_A), so deleting that occurrence's arrow preserves the composite and all remaining boundaries. The two unit laws follow from whole-set restriction and identity factors. Associativity follows from i_U i_V i_W = i_(U[V[W]]), equality of the lexicographically ordered triples (i,j,k), category associativity, and commutativity/associativity of M. Commutativity is genuinely used: outer-then-inner flattenings can order factors n_i,p_(i,j) differently. Since no substitution changes the outer graph and each inner graph is a restriction, every bound r <= N is closed. This is not a depth truncation.

All choices are finite in each fixed profile and output. Empty blocks allow unbounded arity even for fixed N. This elementary calculus construction is included only to avoid circularly assuming C1/C5; no all-degree cut theorem is imported.

## 3. Finite signature and exact local rules

The signature has the following generators; identity leaves are not primitive generators.

- For each graph G, ordered bipartition (U,V), and arrows a:A -> B, b:B -> C, a binary generator c_(G;U,V;a,b) with inputs (G|U,a),(G|V,b) and output (G,ba).
- A nullary u_A with output (empty,id_A).
- For every component W and every m in M, a unary generator d_m^W:W -> W in the multicategory sense. This unary notation does not mean an interface arrow.

All binary and nullary generators have semantic decoration 1; d_m has semantic value m and identity underlying cut. There are finitely many colours and generators for fixed N,K,M. Terms are the A1 occurrence-linear planar presentations on this signature. Every displayed metavariable occurs exactly once on both sides of every rule. The u_A is a nullary term and has no external occurrence. An identity leaf of colour (empty,id_A), in contrast, is an external occurrence and never matches u_A.

Suppress only uniquely recoverable cut labels when writing c(x,y). The seven rule schemas are:

    R:   c(c(x,y),z) -> c(x,c(y,z))
    UL:  c(u_A,x)    -> x
    UR:  c(x,u_B)    -> x
    D0:  d_1(x)     -> x
    DA:  d_m(d_n(x))-> d_(mn)(x)
    DL:  c(d_m(x),y)-> d_m(c(x,y))
    DR:  c(x,d_m(y))-> d_m(c(x,y)).

The exact typing of R is essential. Choose an ordered triple partition (U,V,W) of the whole G and composable a:A_0 -> A_1, b:A_1 -> A_2, c:A_2 -> A_3. On the left the outer partition is (U union V,W), with arrows (ba,c), and the inner partition is (i_(U union V)^-1 U,i_(U union V)^-1 V), with arrows (a,b). On the right the outer partition is (U,V union W), with arrows (a,cb), and the inner partition is (i_(V union W)^-1 V,i_(V union W)^-1 W), with arrows (b,c). The child colours agree by (restriction), and the output arrows agree by category associativity. Every well-typed left-nested binary pair uniquely supplies these data by lifting its inner blocks into the outer whole. No intermediate arrow is guessed from a composite.

UL is only the generator labelled by (empty,[r];id_A,f) applied to (u_A,x). UR is only ([r],empty;f,id_B) applied to (x,u_B). They do not remove a leaf of empty graph colour, an empty block carrying a nonidentity arrow, or an arbitrary nullary primitive from another signature. DL and DR change no cut label; the new decorator is at the cut's output colour. DA and D0 act at a single colour.

Rules apply in every well-typed one-hole tree context. Finite tables for K and M, finite adjacency matrices, and finite subset lists decide all typing and matching tests. R computes its replacement using unions, increasing enumerations, and category composition. Its matching never asks to solve an equation for missing factors. Thus matching and one-step enumeration are decidable, with finitely many reducts for every term.

Every rule preserves the ordered frontier, endpoints, output colour, complete flat partition and full frontier arrow string. Decoration preservation for DL uses (m p)q=m(pq); for DR it uses p(m q)=m(pq), explicitly using commutativity. R uses associativity; unit rules use the identity. Hence evaluation is invariant under reduction and under the parallel substitution congruence E generated by the unoriented rules. This does not assume equality in this model defines E.

## 4. Termination in arbitrary contexts

For a term t define four natural numbers:

1. B(t): number of binary cut vertices.
2. A(t): sum, over binary vertices v, of the number of binary vertices in v's left subtree; unary decorations are ignored for this count.
3. H(t): sum, over decoration vertices d, of the number of binary strict ancestors of d.
4. D(t): number of decoration vertices.

Order tuples (B,A,H,D) lexicographically. This is well-founded on N^4.

- UL and UR strictly lower B by one, regardless of changes to later coordinates.
- R preserves B. Writing B(x)=b_x, B(y)=b_y, its two affected contributions to A change from (1+b_x+b_y)+b_x to b_x+b_y; A decreases by 1+b_x. All other internal contributions are unchanged. At ancestors of the redex, subtree B is unchanged, so their contributions are unchanged too. H may increase, which is harmless after the strict A decrease.
- DL and DR preserve B and A and move exactly one decoration across exactly one binary ancestor. All other decorations keep their binary ancestor counts, so H decreases by one. This remains true within every context.
- DA preserves B,A. If its redex lies under h binary ancestors, it removes one decoration at that cut-depth, so H decreases by h. If h=0, H is unchanged and D decreases by one. Decorations inside x have unchanged binary ancestor counts.
- D0 has the same H,D calculation as DA.

These calculations prove strict lexicographic decrease for every contextual step, including all unit and decoration values. Therefore there is no infinite rewrite sequence. Neither raw vertex count nor decoration depth alone would prove this theorem.

## 5. Canonical witnesses and irreducibles

For a flat witness w with n blocks, construct a term C(w) ignoring m:

- n=0: u_A. This case has whole (empty,id_A).
- n=1: the identity leaf at (G,f). It is not u_A, even if G is empty and f=id_A.
- n>=2: let V=U_2 union ... union U_n and b=f_n ... f_2. Use the binary cut of G with partition (U_1,V), arrows (f_1,b), left identity leaf at (G|U_1,f_1), and right child recursively C(G|V; i_V^-1 U_2,...,i_V^-1 U_n; f_2,...,f_n).

Define N(w)=C(w) if m=1, and N(w)=d_m(C(w)) otherwise. This is well-typed by (restriction), has exactly the original ordered frontier, and evaluates to w by induction on n. In particular it supplies surjective generation, including all nontrivial decorated nullaries. N(w) is irreducible: C(w) has no internal nullaries for n>0, no decorations, and no left-nested binary cut; its left identity leaves cannot trigger unit elimination. The optional root decoration is nonidentity and unnested.

Conversely let t be irreducible. No decoration can have a decoration parent (DA), nor a binary parent (DL/DR), and no identity-valued decoration can occur (D0). Thus there is at most one decorator, at the root, with value different from 1. Remove it temporarily. A nullary u_A can have no binary parent (UL/UR); if the remaining term is not itself u_A, no nullary occurs. Any binary left child would trigger R. Consequently the remaining term is either a single identity leaf or a right comb of identity leaves.

For a right comb with fixed whole and flat evaluation w, the root's left block is U_1 and its right block is the union of the remaining blocks. Its left arrow is f_1 and its right arrow is their composite, because each child term is well-typed. The remaining graph and all restriction embeddings are then forced; induction determines every internal cut label. The leaves, including repeated types, remain the ordered occurrences of w's profile. Its root decorator, if any, is exactly w's total m. Hence

    irreducible(t) implies t = N(eval(t)).                     (NF-injectivity)

This argument does not recover a whole from isolated pieces. It starts from the retained whole and actual partition. Two partitions with identical induced graphs generally give different cut labels and different normal forms.

## 6. Global confluence and presentation completeness

Termination gives an irreducible descendant of every term, for example by repeatedly taking the first redex in a fixed traversal. Semantic invariance and NF-injectivity show that every such descendant is N(eval(t)). Thus all reduction paths from t have the same terminal term. If t reduces to a and b, terminate from each: both reach N(eval(t)). This proves confluence without assuming any external critical-pair theorem.

For parallel presentations s,t, the following are equivalent:

    s E t;
    N(eval(s)) = N(eval(t));
    eval(s) = eval(t).

The first implies the third by semantic soundness of every generating equation and substitution. The third implies the second by the explicit N construction. The second implies the first because each term reduces using equations in E to that same normal form. Evaluation of N(w) is w, so equality of normal forms implies equality of semantics as well. Thus this is soundness AND completeness for the independently declared local equations, not a quotient defined to have all semantic equalities.

A normalization algorithm can use terminating rewriting or the direct independent two-stage computation t -> eval(t) -> N(eval(t)). The theorem proves their equality and that the direct output is E-equivalent to t. Comparing finite graphs, subsets, arrow strings, and M-values decides E. No claim about arbitrary additional equations follows.

## 7. Exhaustive critical-overlap audit

Labels in this section are exactly those of section 3; joins inherit unions, increasing restriction maps and arrow composites. Let bar_d_m(t) mean d_m(t), with D0 applied afterward if m=1. Each row lists a peak source and a common reduct. The arrows to the displayed reduct use the named rules at the indicated structural positions; no symmetry of leaves is used.

| # | Competing rules/position | Source | Common reduct |
|---|---|---|---|
| 1 | R / UR at root | c(c(x,y),u) | c(x,y) |
| 2 | R / DR at root | c(c(x,y),d_m(z)) | d_m(c(x,c(y,z))) |
| 3 | UL / UR at root | c(u,u) | u |
| 4 | UL / DR at root | c(u,d_m(x)) | d_m(x) |
| 5 | UR / DL at root | c(d_m(x),u) | d_m(x) |
| 6 | DL / DR at root | c(d_m(x),d_n(y)) | d_(mn)(c(x,y)) |
| 7 | D0 / DA at root | d_1(d_n(x)) | d_n(x) |
| 8 | R / R at left cut | c(c(c(x,y),z),w) | c(x,c(y,c(z,w))) |
| 9 | R / UL at left cut | c(c(u,x),y) | c(x,y) |
| 10 | R / UR at left cut | c(c(x,u),y) | c(x,y) |
| 11 | R / DL at left cut | c(c(d_m(x),y),z) | d_m(c(x,c(y,z))) |
| 12 | R / DR at left cut | c(c(x,d_m(y)),z) | d_m(c(x,c(y,z))) |
| 13 | DA / DA at inner decoration | d_m(d_n(d_p(x))) | d_((mn)p)(x) |
| 14 | DA / D0 at inner decoration | d_m(d_1(x)) | d_m(x) |
| 15 | DL / DA at left decoration | c(d_m(d_n(x)),y) | d_(mn)(c(x,y)) |
| 16 | DL / D0 at left decoration | c(d_1(x),y) | c(x,y) |
| 17 | DR / DA at right decoration | c(x,d_m(d_n(y))) | d_(mn)(c(x,y)) |
| 18 | DR / D0 at right decoration | c(x,d_1(y)) | c(x,y) |

For row 6, left-first movement gives d_m(d_n(c(x,y))), whereas right-first gives d_n(d_m(c(x,y))); DA joins them precisely by mn=nm. Row 13 uses (mn)p=m(np). Row 8 is the ordinary directed pentagon; each side rotates to the listed four-leaf right comb, and the actual labels agree by the strict restriction lemma and category associativity. In rows 2,11,12, moving the decoration first gives d_m(c(c(x,y),z)), which rotates once, while rotation first puts it at one of three frontier positions and one or two movements lift it to the same root. Rows 1,9,10 use the unique empty identity cut and the unit axioms in K. Rows 4,5 move then eliminate or eliminate directly. In rows 15,17 aggregation then movement gives the common reduct; movement then movement then aggregation does too. Rows 7,14,16,18 use the monoid identity. These calculations remain valid when some metavariables have empty frontier or empty-colour leaves.

Why the table is exhaustive: the only nonvariable proper positions of left-hand sides are the left C of R, the inner D of DA, and the child D of DL/DR; u has no reducible proper position. These give rows 8-18. Distinct root rules with unifiable left-hand sides give exactly rows 1-7; same-rule root overlaps are identical. All other root combinations have incompatible head symbols at a tested child. Redexes in disjoint subtrees commute. A redex lying in a metavariable position of another rule commutes with that rule because each metavariable is retained exactly once, unchanged as a term, on both sides. Therefore every local peak belongs to the table or one of those trivial classes. This is a typed overlap argument: an instantiation must satisfy all labels and boundaries, and unions/restrictions construct well-typed joins. An untyped pattern alone is not a claim that every arbitrary labelling is allowed.

## 8. Interface and refinement uses, with their boundary

Let Q be the A3 quotient by E. The proven evaluation is a fibrewise bijective strict calculus morphism Q -> GCut(K,N,M). Its inverse is w -> [N(w)]. The inverse preserves substitution: evaluating both proposed sides yields the same flat substituted witness, and injectivity gives equality in Q. This supplies an explicit isomorphism of calculi once Q's generic construction is available.

Conditional on the generic A3 quotient and B2 occurrence-tuple category constructions and their laws, their instantiations here are isomorphic: an arrow out of q with k original leaves is the k-tuple (b_1,...,b_k) satisfying q'=q[b_i]; map each entry through evaluation. The inverse maps each entry to its canonical class, retaining its own frontier length, type and position. The defining equation and arrow composition are preserved by the calculus isomorphism. Distinct tuples must not be replaced by the same composite. This is a transfer between two ALREADY defined semantic refinement categories, not a discharge of their generic construction obligations. It is not B3's proposed quotient/completion of raw refinement arrows and supplies none of its ordinary/mixed coherence relations.

A functor F:K -> L sends each arrow in the entire string to F(f_i); a monoid homomorphism h:M -> M' sends the decoration to h(m). These maps commute with flat substitution and evaluation because they preserve identities, composition and multiplication. Applying them to a syntax normal form may create d_1 and hence require normalization. Precisely, normalizing the mapped term equals the normal form of the mapped full witness. For an isomorphism of K and an isomorphism of monoids the equality is literal on canonical syntax. Ordered-graph transport along an increasing bijection commutes with the canonical restriction maps by uniqueness of increasing enumeration. These are the exact elementary relabeling comparisons used here, not a proof of arbitrary noninvertible interface descent or the full D-workstream.

## 9. Nondegenerate six-vertex certificate

Take K to contain the three-object chain 0 -> 1 -> 2, with arrows a:0 -> 1 and b:1 -> 2. Let G have ordered vertices 0,...,5, edges {1,2},{3,4},{0,5},{2,3}, and ordered blocks

    U_1={0}, U_2={1,2}, U_3={3,4}, U_4={5};
    arrow string (a,id_1,id_1,b).

The middle components are literally the same ordered two-vertex one-edge graph with arrow id_1, and both are nonempty. A left comb and right comb evaluate to this same retained cut after rotations. Refining occurrence 2 by its ordered singleton cut and leaving occurrence 3 as an identity gives five leaves; refining occurrence 3 instead gives a different five-block partition although the repeated component types initially matched. These are distinct occurrence-indexed substitutions.

For a nontrivial decoration monoid use Z/3Z additively. For example decorations 1 on the first repeated component and 2 on the second aggregate to 0 after movement, so a decorated left-comb term and the undecorated canonical right comb agree only through genuinely mixed movement, aggregation and rotation. A sole decoration 1 remains as a distinct full witness on the same cut. For unit interaction insert a binary cut (empty,id_1) next to either middle component, supply the actual u_1, and put decoration 1 on u_1: movement preserves that value before the nullary unit is eliminated. It must not be discarded.

Removing the cross-block edge {0,5} from G leaves all four induced components unchanged but changes the whole colour and retained semantic witness. Swapping vertices between U_2 and U_3 can similarly preserve induced component types while changing the ordered partition. Normal forms retain both distinctions; neither is an equation of the presentation.
