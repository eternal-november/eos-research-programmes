# Typed cover descent for witnessed decomposition calculi

Status: proof candidate, 29 October 2026. This note separates a new programme-level comparison from standard algebraic ingredients. Chinese-remainder reconstruction, congruence lattices, and finite relational composition are established mathematics. The contribution under test is a precise arbitrary-cover comparison for the existing typed witness calculus, its semantic refinements, and its specified cuts and interface transports. It is not a new proof of laminar 2-Segal coherence, and it does not by itself discharge the old presentation-level F3/I4 obligations.

## 1. Retained sorts and actual witness data

Let M be the programme's nonsymmetric path-typed witness calculus over a fixed interface/component base. Its operation fibre M(p;w) has an ordered full input profile p and output component w. Identities and occurrence-wise substitution are those of M. The output whole/component type w and the full profile are therefore ANCHORS supplied to this comparison. This theorem reconstructs operation witnesses over those anchors; it does not discover an unknown whole type from observations. All views below retain this base literally: endpoints, colors, input order, arity, repeated occurrence positions, and enabled nullary profiles are not quotiented.

Write a fibre simply as W. A partial description i is a family E_i of equivalence relations on operation fibres, stable under typed substitution. Thus if a E_i a' and b_k E_i b'_k at every named input occurrence, then a[b_k] E_i a'[b'_k]. These are genuine parallel substitution congruences. Their quotient calculi M_i=M/E_i and all joins M/(E_i vee E_j) are actual calculi. Joins are the equivalence closure of the union, computed separately in each full profile; they are substitution congruences because a finite substitution can change its arguments one at a time along relation chains.

This identity-on-base scope is substantive. If a view erases a leaf occurrence, changes an intermediate component, or treats two profile orders as equal, a common typed skeleton must first be reconstructed. The theorem below does not silently supply it. Crossing diagrams may be compared only with their named occurrence correspondence and boundary transport retained; incompatible planar profiles are a prior obstruction, not a permission to add symmetry.

For a nonempty finite set S of views, put R_S=intersection_{i in S} E_i. Define the compatible-view fibre

  P_S(W) = { (c_i) in product_{i in S} W/E_i :
             c_i and c_j have the same image in W/(E_i vee E_j)
             for every i,j in S }.

Compatibility is an independently specified pairwise-overlap test. It is not defined as the image of W. The comparison

  eta_S : W/R_S -> P_S(W),  [x] -> ([x]_i)_i

is always injective. Surjectivity is the question.

An empty W causes no difficulty for a nonempty cover: all its quotient fibres and P_S are empty. The empty cover is excluded; absence of all descriptions must not be treated as identifying a whole.

## 2. Exact all-subfamily recognition criterion

Use relational composition A;B, where x(A;B)y means that some z satisfies xAz and zBy. For S nonempty and j outside S define the finite relational test

  (intersection_{i in S} E_i);E_j
       = intersection_{i in S}(E_i vee E_j).                 (CR)

The forward inclusion always holds. The reverse inclusion is the nontrivial test. It says that a whole representative compatible separately with the j-view can be adjusted within all already retained views at once. Its computation uses relations on W, joins by connected components, intersections, and relational composition; it does not enumerate a candidate common-refinement tree or assume a joint witness.

**Theorem 1.** The following are equivalent, fibre by fibre:

(a) eta_T is a bijection for every nonempty subfamily T of the given finite cover.
(b) (CR) holds for every S and j outside S.

Proof of (b) => (a): induct on |T|. A singleton quotient has the property. Given a compatible tuple on S union {j}, use induction to obtain a representing a for its S-coordinates, and choose b representing its j-coordinate. Pairwise compatibility gives a (E_i vee E_j) b for every i in S. By (CR), choose c with a R_S c and c E_j b. Then c realizes all coordinates. If c and c' realize them, c R_(S union {j}) c', proving uniqueness of the joint class.

Proof of (a) => (b): if a lies in the right-hand relation with b, the tuple consisting of a's classes on S and b's class on j is pairwise compatible. A representative c supplied by (a) gives a R_S c E_j b. QED.

The result is exact for hereditary reconstruction, meaning every subcover as well as the entire cover. It is not a claim that surjectivity for one full cover alone forces every subcover to lift: extra coordinates may prevent a bad partial tuple from extending to that full cover. Testing (CR) only in one chosen order is sufficient for that order's induction if all needed subcover comparisons have already been established, but the order-independent theorem uses the stated all-subfamily criterion.

For finite fibres, the test is decidable. It can be exponential in the number of views, and total fibre sizes may themselves be large. No general polynomial discovery or verification claim follows. A failure produces explicit a,b,S,j satisfying every overlap relation on the right but no common adjustment on the left, hence a compatible partial-description tuple with empty joint-witness fibre.

A useful sufficient subclass is a distributive lattice of pairwise permutable congruences containing the E_i and their finite meets and joins. Then

  R_S;E_j = R_S vee E_j = intersection_i(E_i vee E_j),

so (CR) holds. It is not enough that only the displayed generators commute; the meet relation used in the first equality must also permute with E_j. An arithmetical congruence lattice supplies this uniformly.

## 3. Higher obstructions and the distinction from 2-Segal coherence

Pairwise successful reconstruction is insufficient. Let W be the even-parity binary strings of length m>=3. Let E_i identify strings with the same ith bit. Any proper collection of specified bit values extends to an even-parity string, and every pair overlap quotient is terminal. Thus every proper subcover reconstructs. A full assignment of odd parity does not. At m=3, the generated congruence lattice is the nondistributive diamond; its generators nevertheless permute pairwise.

This is also a genuine substitution-level calculus counterexample, not only a set construction. Take one color, unary operations the additive group W of even-parity vectors over F_2, identity the zero vector, and unary substitution vector addition; take all other operation fibres empty. Each E_i is the kernel of the ith-coordinate group homomorphism, hence a genuine parallel substitution congruence. Thus the same failed cover occurs in an actual typed calculus. This deliberately minimal calibration establishes a structural obstruction, not an ambitious discovery example or a full cut-compatible model.

This gives unbounded minimal obstruction arity: no fixed maximum number of pairwise or bounded-subfamily checks can certify all covers in the unrestricted class. The failure concerns observations of one witness fibre. It is logically different from reassociating a fixed witnessed factorization. A calculus can have perfectly coherent interval cuts while a selected family of observation quotients has this higher failure. The theorem does not assert that every arbitrary parity relation extends to a cut-compatible calculus congruence; that extension must be supplied in any claimed model, as discussed in Section 8.

## 4. Construction on the calculus, not merely on witness sets

Define P_S(M) to have the same base as M, operation fibres P_S(M(p;w)), identities componentwise, and occurrence-wise substitution componentwise. The overlap equations are preserved because each map M/E_i -> M/(E_i vee E_j) is a calculus morphism. Therefore P_S(M) is an actual typed nonsymmetric witness calculus.

**Theorem 2.** If (CR) holds in every operation fibre, eta_S is an isomorphism of typed calculi

  M/R_S  isomorphic to  P_S(M).

The underlying maps are those in Theorem 1. They preserve units and substitution by construction. Their inverses preserve substitution because the two possible results have the same image under the injective eta_S. This proves every finite tree comparison, including repeated occurrences and enabled nullary grafts. It does not invoke a choice of representatives in M.

The construction is natural. A base-preserving calculus map F:M->N that preserves every E_i induces all quotient and compatible-tuple maps. The square involving eta_M, eta_N and F commutes literally. If view names are removed, reconstructed joint classes map by the canonical quotient M/R_T -> M/R_S for S subset T; these maps compose strictly. Different orders of successively reconstructing the same view family agree as maps of joint classes because all have the same view coordinates. Actual representatives may differ within R_S; that ambiguity must not be erased.

This is stronger than a theorem about event-chart gluing in a fixed finite operational model: the operations reconstructed here are the calculus operation fibres and their arbitrary-arity substitution. It is narrower in a different direction because the views are identity-on-base congruence quotients with retained occurrence skeletons.

## 5. Semantic refinement comparison and its exact limitation

An occurrence-indexed semantic refinement has a fixed typed forest skeleton sigma, an outer operation a, one operation b_k at each named old occurrence, and a flattened operation c satisfying the actual equation

  a[b_k] = c.

The skeleton records the ordered frontier blocks, repeated positions, intermediate component colors, and empty blocks. It is not merely a list of operation labels. In this theorem the shared typing and boundary data are fixed in the skeleton, so admissible substitution uses the indicated operation fibres. If extra shared boundary variables or cross-slot constraints remain free, the forest domain is a dependent joint sort, and its reconstruction must be proved separately as in Theorem 3b; separate slotwise reconstruction is not a substitute.

Form the category of compatible view refinements by requiring one common skeleton sigma, compatible families of outer and flattened operations, and compatible operation tuples b_k, with the refinement equation in every quotient view. Composition is the programme's occurrence-wise substitution of forests.

**Theorem 3.** Under Theorem 2 this compatible refinement category is isomorphic to the semantic refinement category of M/R_S. For each occurrence k reconstruct its unique R_S-class of b_k. The outer and flattened classes reconstruct similarly. The refinement equation holds in M/R_S because it holds in every view and eta is injective. Composition and identities agree because Theorem 2 preserves substitution and the skeleton is unchanged. Thus all finite histories with the same occurrence-indexed semantic forest have the existing comparison laws; no extra parallel arrows or swaps are invented.

This does NOT assert that Ref(M)/R_S is automatically Ref(M/R_S), nor that every such arrow lifts with arbitrary fixed representatives a,c in M. The exact actual lift fibre is

  { (b_k) : b_k lies in its reconstructed class,
              a[b_k]=c in M }.

It can be empty even when the quotient refinement equation holds. A quotient-level equality is not an actual refinement witness. When R_S is diagonal in every relevant fibre, the distinction disappears. Otherwise the actual equality constraint and its fibre must be retained. Additional unique-lifting/cut conditions can make particular lifting problems decidable or unique, but are not silently assumed here.

### Fixed-endpoint recovery from a local lifting certificate

Fix an actual outer witness a and a fully typed occurrence skeleton sigma. Let U be the **joint admissible forest domain** for sigma, including shared boundary variables and compatibility constraints. It is not presumed to be a product of independent slot sets. Let c_a:U->W send an actual forest to its flattened witness. Let K_U and K_W be the common view kernels on these two sorts, and suppose c_a is congruent.

The exact additional condition is class-image saturation:

  c_a([u]_{K_U}) = [c_a(u)]_{K_W} for every u in U.       (FL)

The inclusion from left to right is congruence. The reverse says that changing the flattened representative within its observed class can be realized without changing the observed forest class. It is stronger than operation congruence or object-level reconstruction.

**Theorem 3b (fixed-endpoint lifting).** Suppose the proposed compatible view forests reconstruct to a class [u] in U/K_U (for example, Theorem 1 holds on the joint forest sort U). Let b be an actual desired flattened witness, with [b]=[c_a(u)] in W/K_W. Under (FL), there is u' in [u] with a[u']=b exactly. Thus the actual outer witness, actual flattened witness, occurrence skeleton, and every observed forest are all retained. The solution set is the discrete fibre c_a^{-1}(b) intersect [u]; its multiplicity is not removed. Conversely, existence for every u and every such b is precisely (FL).

A generator certificate makes (FL) derivable without enumerating every equivalence class. Suppose K_W is generated as an equivalence relation by explicit elementary moves G (including all required typed contexts). Check: for every u and every elementary move c_a(u) G b, there is u' K_U u with c_a(u')=b. Include reverse moves. Starting at u, lift successive edges of any finite G-zigzag to b. Transitivity keeps the final forest in [u], proving (FL). A finite/effective structural residual schema can certify these moves uniformly; checking a few bare equations without their required contexts is insufficient. The converse holds when the chosen moves are contained in K_W.

Saturated congruent maps compose: if f([x]_K)=[f(x)]_L and g([y]_L)=[g(y)]_N, then (g f)([x]_K)=g([f(x)]_L)=[g f(x)]_N. For partial maps one must also establish domain saturation and use the appropriate joint domain. Consequently a tower of certified cut-factor maps supports successive exact lifting. This does not assert that arbitrary chosen lifts agree; retain the solution fibres, or prove a separate uniqueness/coherent-choice condition.

Nullary cases cannot be suppressed. If U is genuinely a singleton, (FL) forces the K_W-class of its unique output to be a singleton. Thus a nontrivial nullary witness kernel obstructs universal fixed-endpoint recovery even though quotient substitution is valid. In a virtual double category, an empty horizontal forest can still carry a varying common vertical boundary: U is then not a singleton. The test applies to that actual joint domain, not a fictional empty product.

Theorem 3b also identifies where higher crossing tests belong: on joint forest and equation domains, not only on the separate operation slots. A family can pass slotwise reconstruction but fail joint forest reconstruction through a shared interface constraint. One may apply (CR) directly to these domains; or prove a schema-level domain theorem implying it. No such implication is obtained from ordinary substitution congruence alone.

## 6. Retaining the actual whole and provenance

For a reconstructed class z in M/R_S, retain the discrete witness fibre

  Lift(z)={a in M(p;w): [a]_R_S=z}.

It is nonempty exactly for realizable compatible data under (CR), and consists of all actual explanations. Recovering one unique witness is equivalent to R_S being diagonal; surjectivity of eta alone does not establish it. Nontrivial automorphisms, if the ambient model uses groupoids rather than sets, require an additional groupoid descent theorem; this note does not identify such morphisms or infer equivalence from set-level results.

Substitution gives an actual map

  Lift(a*) times product_k Lift(b_k*) -> Lift(a*[b_k]*).

It need not be surjective. Keeping this map, instead of replacing each fibre by a point, preserves which choices assemble into which whole. Likewise the exact refinement lift fibres in Section 5 preserve the actual root equation. One may use quotient classes for evidence bookkeeping while retaining these fibres for semantics. This does not introduce any equation between two actual wholes in M.

### Why choosing representatives is an additional obstruction

Surjectivity of every reconstruction map does not supply a substitution-preserving choice of actual witnesses. Consider the unary one-color calculus whose operation monoid is Z/4 under addition, viewed through parity Z/4 -> Z/2. A single view always satisfies (CR). Any unit-preserving monoid section would send the nonzero element of Z/2 to an odd element of Z/4. Doubling that odd element gives 2, whereas doubling the nonzero element of Z/2 gives 0, which the section must send to 0. No such section exists. All evidence fibres are nonempty; a coherent actual choice still fails.

For fixed endpoint refinement lifting, take the unary monoid {0,1} with composition maximum and unit 0, and its terminal quotient. The view has a refinement from the image of 1 to the image of 0. In the actual calculus no b satisfies max(1,b)=0. The actual refinement fibre is empty. These examples are independent of whole-type discovery: the one type remains fixed throughout.

The correct canonical reconstruction is therefore fibre valued. Its total operation set consists of pairs (z,a) with a in Lift(z). The projection (z,a)->a is a bijection on every fibre and an isomorphism of calculi when substitution is defined by the actual witness maps above. It reconstructs M without adding equations between actual witnesses. The base z is useful partial-description data, but the attached a is not disposable. On semantic refinements retain the actual equation fibre, not the unrestricted product of the operation fibres. This is a representation of residual information, not an automatic efficient recovery algorithm.

A strict actual section exists exactly when one can choose representatives for all required sorts/operations satisfying every unit, substitution, cut and transport equation in the specified structural presentation. On a finite presentation this is a finite constraint problem once finite candidate fibres and a complete relation basis are supplied; on the unbounded programme signature no finite decision claim follows without that basis. Merely selecting the first representative independently per fibre is unsound.

### No canonical least repair by splitting views

There need not be a least viewwise information refinement that makes a cover reconstruct. For the three binary coordinate views of W={000,011,101,110}, making any one view the identity repairs reconstruction: its exact witness class forces consistency of the others. The three resulting repairs are incomparable under coordinatewise refinement. Any least repair below all three would leave each coordinate view unchanged (in two of the three repairs that view is unchanged), hence would be the original failed cover. Contradiction.

This obstruction is to repairing joint reconstruction by splitting the views, not to the established existence of a complete shell for one deterministic operation signature. It explains why a canonical framework cannot promise a least extra sensor/view refinement in general. A retained joint-realization relation or a chosen noncanonical repair is additional data; neither is free.

## 7. Cuts, partial operators, and interface transport

Suppose M already carries specified interval cuts. A cut at I is a partial map

  cut_I: M(p;w) -> coproduct_K M(p/I->K;w) times M(p_I;K),

possibly an inverse to the declared substitution bijection on its domain. The intermediate K is part of the result. Unit/nullary tests and cut coherence are those of the given cut calculus, not consequences of ordinary substitution.

A view kernel E_i is **cut admissible** exactly when:
- the cut domain is a union of E_i-classes;
- related operations have the same intermediate K and E_i-related outer and inner cut witnesses.

If cuts satisfy exact reassembly subst(cut(a))=a, substitution congruence implies the reverse direction as well: root relatedness iff the cut outputs are componentwise related, on the cut domain. Without this reassembly law, the admissibility test gives only forward preservation and no reverse equivalence is claimed. This is an actual relation test on the designated cut operation, not the assertion that every substitution congruence preserves cuts.

The same definition applies to any specified partial interface-transport operation: its domain must be saturated and its output must respect E_i. For a total transport only the second condition remains. Domain reflection is essential: agreement of output values where both operations happen to be defined does not preserve which cuts or transports are allowed.

Under these tests, each quotient inherits the operators. Meets and joins of admissible congruences are admissible: for a join, follow a relation chain and use domain saturation and output compatibility at every edge. Consequently all overlap quotients used in P_S inherit them.

**Theorem 4.** If the kernels satisfy these tests and (CR), eta_S is an isomorphism of the entire specified typed partial structure. Its reconstruction commutes with cuts, transports, and every finite mixed expression of substitution, cuts and transport. In particular all already-proved local mixed diagrams of M descend and reconstruct coherently; no diagram is replaced by an equality after forgetting witness data.

Proof: domains and output coordinates are preserved in every quotient. Coordinatewise application defines the operation on P_S, with the common domain witnessed by any reconstructed class. Eta and its inverse commute by injectivity, as in Theorem 2. Induct on the finite expression. QED.

This is a transfer theorem, not a proof that the original C5 presentation meets the cut-admissibility tests. For a finite explicit structural presentation, they can be checked on its finite primitive operation tables. For an unbounded presentation, one needs a complete finite or effective schema and a proof that its local checks cover every generated context. Merely declaring the desired cut laws in a new signature does not prove conservativity of the old presentation. That old-to-structural-presentation bridge remains a separately named obligation. The companion proof `Mixed_Presentation_Criterion.md` supplies a sufficient residual-machine certificate reducing domain-reflecting congruence descent to generator checks in arbitrary typed contexts. It does not by itself imply the reverse fixed-endpoint saturation (FL), and it does not establish that the original C5 presentation has the required residual basis.

### Transporting the cover itself

There is a second, different issue. A restriction map f:W'->W can induce new view relations f^*E_i on W'. Even if the old cover reconstructs, the new cover need not. Inverse image preserves meets, but need not preserve joins or relational composition. A context can create new correlations.

A sufficient checkable condition is that f is surjective. Every intermediate point in a relation chain then lifts, giving

  f^*(E vee F)=f^*E vee f^*F,
  f^*(E;F)=f^*E;f^*F.

Pulling back (CR) consequently proves (CR) for the transported cover. For nonsurjective f, require the corresponding image-relative chain and middle-point lifting properties, or check (CR) directly on the pulled-back relations. These are explicit finite relation tests when W,W' are finite.

Counterexample: W={00,01,10,11}, E and F equality of the first and second coordinates. They reconstruct W. Restrict to W'={00,11}. Both inverse-image relations are diagonal, so their join is diagonal; the inverse image of E vee F is total. The old overlap description would permit incompatible pairs on the restricted context. Here the recomputed overlap repairs the test: the new cover itself still satisfies (CR). For an actual failure even after recomputing overlaps, instead restrict to the L-shape W'={00,01,10}. Its row and column kernels still have total join, but the compatible row-1/column-1 pair has no witness because 11 is absent. Thus the pulled-back cover itself fails (CR). Generic inverse-image functoriality is not enough for contextual reconstruction. No claim about equipment cartesian restrictions follows from a bare set map without verifying that its witness map satisfies the relevant test.

## 8. What is and is not delivered

The graph-independent result is an arbitrary-cover recognition and reconstruction theorem on actual typed operation fibres, with a morphism-level calculus comparison, exact semantic-refinement comparison, retained actual-whole fibres, and transfer through specified admissible cuts/interface operators. It separates higher cover descent from laminar 2-Segal coherence and makes whole nonidentifiability explicit.

The relation criterion must be established on each relevant fibre of the chosen model. An arithmetical congruence subclass is a useful uniform positive hypothesis; the finite tests cover more cases. No claim is made that every witness calculus has such quotients, that CULF implies recovery of a whole, that arbitrary crossings share a planar profile, or that the old C5-only generators present every new structural operation.

To count this as a full F3/I4 discharge, the programme still needs the independently specified local presentation bridge: concrete view kernels on its unbounded mixed cut/graft/transport family, complete schema-level admissibility checks, and the appropriate ordered-crossing comparison. The parity group example proves a genuine substitution-calculus higher obstruction, but must not be advertised as a cut-compatible mixed calculus model until its cut tests are supplied. This boundary is part of the theorem statement, not a later disclaimer.
