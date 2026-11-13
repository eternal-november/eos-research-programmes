# Full witness arrows, parameter comparison, and the scalar-product boundary

P-level proof for the technically released integrated target. Contract v0.1
SHA256 `47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`;
target SHA256 `2f8cc8b77165ef9d5fe915799e5291089067b10f0683f82d9f878ba1da1c7f7b`.
This is an author proof, not an acceptance record. Scientific significance is
explicitly separate from correctness. No F/D/E/B4 obligation is discharged.

## 1. Quantifiers, independent objects, and imported facts

Throughout, N is any nonnegative integer, K any finite category, and M any
finite commutative monoid with identity 1. Principal examples use N≥6 and K
with at least three objects and composable nonidentity arrows. The proofs have
no bound on arity, tree depth, number of empty blocks, or refinement length.
The effective versions use explicit finite K and M tables. The empty category
has no components; universal statements on its components are vacuous and it
is not a principal certificate. We write products multiplicatively even when
an example is the additive cyclic group.

An ordered graph G has vertices [r]={0,…,r−1}, r≤N. Its equality includes the
full edge relation, not only its isomorphism class or induced pieces. For
U⊆[r], i_U:[|U|]→[r] is the increasing enumeration and G|U its induced pullback.
The inherited restriction lemma gives

    i_(i_U(V)) = i_U ∘ i_V,       (G|U)|V = G|i_U(V).          (1.1)

Components are W=(G,f:A→B). A profile p=(X_1,…,X_k) contains its entire
composable arrow string f_i:A_(i−1)→A_i and graphs, not merely endpoints.
A full flat witness a∈D(W;p) is an ordered partition (U_1,…,U_k) of [r],
including empty blocks, with X_i=(G|U_i,f_i), composite f_k⋯f_1=f, and value
m∈M. The whole W remains part of the fibre. Two whole grades f≠f' give
different fixed-output fibres even if G is identical.

For k=0 there is a witness only at W=(empty,id_A), and then its value is an
arbitrary m∈M. For k=1 the underlying cut is the singleton block [r] and arrow
f, with arbitrary value m; only m=1 is the identity operation.

Substitution at original slot i replaces U_i by the lifted ordered blocks
 i_(U_i)(V_(i,j)), concatenates the entire child arrow strings, and changes
m to m·∏_i n_i. All graph edges of G remain. Repeated equal X_i still have
separate slots. The bound N is closed because inner graphs are induced
restrictions, not because arity/depth is bounded.

We import, rather than reprove or count as new, the following reviewed results:

* A1–A3's actual typed `Calc`, free tree calculus, least parallel congruence,
  and actual quotient Q=Presentation.quotient E.
* A4's seven finite local templates R,UL,UR,D0,DA,DL,DR, all-context
  termination and completeness for the independently defined D; canonical
  raw term N(w), eval(N(w))=w, and strict inverse maps Phi:Q→D and
  Psi(w)=[N(w)]. These are THEOREM.md and A3_LOCAL_COMPARISON.md, not a new
  semantic-kernel definition of E.
* B1's actual raw forest category, B2's actual occurrence-tuple Ref construction
  and strict interpretation functors. Its arrow tuple retains each entry's
  entire profile and is not quotiented by equal composites.

Small-N provenance is explicit: the inherited THEOREM.md is all-N, while
A3_LOCAL_COMPARISON.md states N≥6 for its principal adapter. For 0≤N<6 its
same quiver, generator and equation tables, induced restrictions and canonical
right combs remain defined; all proofs use only r≤N and arity induction.
Restrictions stay within the bound and no step requires an additional vertex.
Thus the identical quotient/inverse construction proves the small-N cases
here. This is a verified parameter extension of those formulas, not a claim
that the adapter text already stated the wider range. The principal six-vertex
and multi-interface certificate requirement is not weakened.

The new independent syntactic completion theorem is in
`Completion_Comparison.md`. Only statements expressly referring to Comp below
use that theorem; §§2–4 and §6 are proved directly from the independent flat
model and therefore do not assume the sought completion comparison.

## 2. Explicit full semantic hom sets

### 2.1 Admissible ordered runs

Fix the SAME output component W=(G,f:A→B) and objects

    a=(U_1,…,U_k; f_1,…,f_k; m),
    b=(V_1,…,V_l; g_1,…,g_l; m').

The source profile has interfaces A_0,…,A_k. For a vector
lambda=(l_1,…,l_k) of nonnegative integers with sum l, put
s_i=∑_(h<i) l_h. Run i is the ordered interval of target indices
s_i+1,…,s_i+l_i. Call lambda admissible if all the following hold:

1. The union of the actual sets V_j in run i is U_i. Thus every V_j of that
   run lies in U_i. Empty source blocks and empty target blocks remain actual
   entries; an empty V_j is not deleted.
2. The complete subpath of the target profile in run i has endpoints
   A_(i−1),A_i, and its composite arrow is f_i. This requires equality of
   the actual intermediate endpoints and arrows, not merely a common outer
   composite. For l_i=0 the empty path exists at a single interface, so
   A_(i−1)=A_i, f_i=id, and condition 1 forces U_i=empty.

The condition is decidable from the supplied finite data. For l_i>0, full
run arrows g_j, not just their composite, are retained as the child profile.
For each admissible lambda, the only possible underlying cut at original
slot i has blocks

    ( i_(U_i)^(-1)(V_(s_i+1)), …,
      i_(U_i)^(-1)(V_(s_i+l_i)) )                         (2.1)

in the coordinates of G|U_i, and that full subpath of (g_j). Here inverse
means the inverse bijection [|U_i|]→U_i, only on subsets V_j⊆U_i. No
inverse arrow in K is used.

### 2.2 Hom-description theorem and inverse maps

There is a canonical bijection

 Hom_Ref(D)(a,b) ≅
   ⨿_(lambda admissible) { (n_1,…,n_k)∈M^k : m·∏_i n_i=m' }.       (2.2)

The disjoint-union label lambda is retained. Homs across unequal W are empty
in the total disjoint-union category, even if the graphs agree.

Proof. A semantic arrow is a tuple t_i with output X_i and a[t_i]=b. Let l_i
be the length of its full profile and n_i its value. The substitution profile
law identifies the profile of b with the ordered concatenation of these full
profiles, so their lengths sum to l and determine the indicated runs. The
arrow endpoint equality compares actual ordered partitions: the run's lifted
blocks equal exactly the corresponding V_j, and their union is U_i. Its arrow
string compares to the entire string g_j, with the child output grade f_i.
Thus lambda is admissible. Injectivity of i_(U_i) forces (2.1); each child's
remaining independent datum is n_i. The value part of the endpoint equation
is precisely m·∏n_i=m'. This defines the forward map without forgetting an
entry's profile or local value.

Conversely, take admissible lambda and n satisfying that equation. Define
t_i by (2.1), the full run path, whole X_i=(G|U_i,f_i), and n_i. Its blocks
partition [|U_i|]. By (1.1), restricting its whole to the j-th block gives
the j-th target component graph. Its full run path has composite f_i.
For a zero-length run the conditions give exactly the allowed nullary
component (empty,id), so t_i is a legitimate nullary of value n_i. The tuple
is therefore typed. Substitution lifts its blocks back to V_j, returns the
full target arrow string, and has value m'; hence a[t_i]=b. Reading lengths
and values returns the original data, while reconstructing a tuple from its
lengths/values returns each of its forced blocks and arrows. These two maps
are inverse as actual tuples. QED.

This proof establishes equality of arrows, not merely equality of their
endpoint operations. It retains empty-run labels n_i, which are not recovered
from later descendant entries because a zero-length run has no descendants.

Boundary cases. If k=0, lambda is the empty vector and its sum is zero, so
l=0; the value condition is m=m'. Thus a nullary object has only its identity
arrow, even though there are many nullary objects with different values. If
l=0 and k>0, every source occurrence must be (empty,id) at the appropriate
interface, and the full tuple of k nullary values remains arrow data. An
empty graph carrying a nonidentity grade never passes this test.

For finite M, each fixed hom set is finite and is effectively enumerated by
all weak compositions of l into k parts (with the k=0 case above), testing
admissibility and all M^k value vectors. In particular

 |Hom(a,b)| = (# admissible lambda) ·
             |{ n∈M^k : m·∏n_i=m' }|.                         (2.3)

This formula is not a theorem that frontiers reconstruct wholes or that all
finite-degree cut structures have unique factorization. W is fixed and
retained throughout.

### 2.3 Composition, identities, and nonthinness

Let alpha:a→b have data (lambda,n_i), and beta:b→c have data
(mu,r_j), where mu=(h_1,…,h_l). At original source slot i, the composite
has

    L_i = ∑_(j in run i) h_j,
    N_i = n_i · ∏_(j in run i) r_j.                         (2.4)

Its local blocks are the final c-blocks in the resulting concatenated run,
pulled back into U_i; its interface string is that same full final subpath.
To prove this, apply B2's actual tuple composition t_i[u_(i,j)]. The ordered
slot-expansion identifies its final positions with pairs (i,j), and (1.1)
identifies their lifted subsets. The output of the run's grade multiplication
is f_i by category associativity; its decoration is exactly (2.4). The total
endpoint value is

 m·∏_i(n_i·∏_(j in run i)r_j)
   = (m·∏_i n_i)·∏_j r_j = m'·∏_j r_j,

using the commutative monoid laws. This proves the formula on arrow DATA.
For l_i=0, both sums and products over its descendants are empty, so L_i=0
and N_i=n_i. A nullary label survives composition and is not replaced by 1.

Identity has l_i=1, the singleton unchanged block/path, and n_i=1 at every
slot. Formula (2.4) proves both units entrywise. For three arrows, both
parenthesizations identify the same ordered triples of descendant slots;
their lengths and products agree by finite-sum associativity and the monoid
laws. Therefore the formula itself gives the same B2 category, not a different
endpoint-only quotient category.

For example, at an object with two original slots in additive Z/2 and source
value 0, unary identity cuts at those slots with values (0,0) and (1,1) give
distinct parallel endomorphisms. Both total values are 0; their individual
entries differ. The same example can be inserted at the two nonempty repeated
middle components of the six-vertex four-slot mixed-interface cut, leaving
values 0 at the other slots. This is nonthinness at fixed endpoints, not merely
two different-target refinements. In the idempotent monoid {1,e}, a source
value e has 2^k different unary-value endomorphisms for a fixed k-slot profile:
e·∏n_i=e for every vector, while (2.2) keeps every vector distinct. These
are consequences of a standard scalar factor, not independent novelty.

## 3. Strongest product and typed-pullback baseline

### 3.1 The profile and scalar calculi

Fix the SAME component quiver J of pairs (G,f). Let Prof(W) consist of all
full typed paths p from W.source to W.target, with profile p. There is exactly
one Prof operation in each such fibre, including the empty path only when
these endpoints coincide. It does not require the path's grades to compose
to W.grade; that restriction belongs to Cut, not Prof. Identity is the
singleton path (W), and substitution is ordered typed path expansion. A1's
path laws give its units and associativity.

Let Scalar_M(W;p)=M for EVERY such admissible full path p, independent of
whether a graph cut exists. A scalar operation is the pair (p,m). Set

    1_W=((W),1),
    (p,m)[(q_i,n_i)] = (expand(p,q), m·∏_i n_i).             (3.1)

These are actual fibres over complete paths and fixed W. Both units follow
from the monoid unit and empty/singleton products. Associativity compares the
same ordered triple occurrence indexing and the product of the outer,
intermediate, and innermost values. Associativity and commutativity of M allow
the two displayed nestings to be rearranged to the same finite product. Thus
Scalar_M is a lawful fixed-base Calc. The forgetful map Scalar_M→Prof sends
(p,m) to p and is strict. Its nullary fibres at arbitrary loop components
cause no enlargement of Cut's nullary fibres in the pullback below.

Let Cut=FlatCut(N,K,{1}), with its whole, partition, grades and full path.
The profile map Cut→Prof is strict. Construct a fibrewise pullback P: at W,
pairs (a_0,(p,m)) satisfying profile(a_0)=p, with identity and substitution
coordinatewise. Their profile agreement is preserved because both maps are
strict. Equality witnesses are proof-irrelevant and are not extra operations.

### 3.2 Explicit isomorphism of calculi

Define

    F:D→P,      F(a_0,m)=(a_0,(profile(a_0),m)),
    B:P→D,      B(a_0,(p,m))=(a_0,m), using profile(a_0)=p.  (3.2)

These maps preserve fixed output W and every full profile. They are inverse
by reading the same actual partition, graph, arrows and M-value. In particular
at a nullary component outside (empty,id) both D and P have an empty fibre,
because Cut has no such witness; the scalar factor alone cannot create one.
The identity pair in P maps to D's identity value 1 and unchanged block. For
substitution, both routes produce the same lifted blocks and full expanded
arrow string, and (3.1) produces exactly m·∏n_i. Hence (3.2) is an actual
strict isomorphism

    D ≅ Cut ×_Prof Scalar_M,                                (3.3)

not just a cardinality identity or an analogy. The whole retained graph is in
Cut and is not reconstructed from the scalar factor or the leaves.

### 3.3 Refinement preserves this typed pullback

Define the categorical pullback of Ref(Cut) and Ref(Scalar_M) over Ref(Prof)
explicitly. Its objects are pairs of operations with the same fixed output
and the same complete profile. A morphism is a pair of refinement tuples with
EQUAL images as Ref(Prof) arrows. This equality means, at every original source
slot, equality of the ENTIRE child profile, not just the concatenated target
profile. It therefore retains the same length/segmentation at that slot, its
component list, and all intermediate endpoints/grades. Equal endpoint
profiles alone do not define this pullback.

Map a D-object to its Cut/scalar pair. Map a D-arrow (t_i) to the pair of
tuples (underlyingCut(t_i)) and ((profile(t_i),value(t_i))). Their images in
Ref(Prof) agree entrywise, so this is a pullback arrow. The coordinate endpoint
equalities are exactly the underlying-cut and scalar-value coordinates of the
D endpoint equality. Conversely a compatible pair of tuples has identical
child profiles slot by slot, and pairing each cut child with that scalar child
by (3.2) gives a typed D tuple. Its two endpoint coordinates give the D
endpoint equation. The two assignments are inverse on objects and arrows.

Identities pair the same original singleton profiles and value 1. Composition
in both factors uses the SAME profile splitting precisely because the child
profiles agree; coordinatewise composition is therefore (2.4). This proves
an isomorphism of actual categories

 Ref(D) ≅ Ref(Cut) ×_(Ref(Prof)) Ref(Scalar_M).               (3.4)

A naïve Cartesian product would allow incompatible segmentations/child
profiles and is incorrect. The needed compatibility is nevertheless ordinary
pullback/category-of-substitutions structure; replacing a naïve comparator
by the correct pullback removes any claim that scalar labels create a new
kind of semantic refinement theory. Equations (2.2)–(2.4), many parameter maps,
and the multiplication fibres below are standard consequences of this
explicit decomposition.

## 4. Parameter maps and strict semantic comparisons

Let theta=(F,h,ι), where F:K→L is any functor, h:M→M' is any monoid
homomorphism, and ι is a bound inclusion N≤N'. The component map is
(G,f:A→B)↦(G,Ff:FA→FB). On a full witness, keep G and all actual subsets U_i,
apply F to every intermediate object and individual arrow f_i, and apply h
to the retained value m. This is well typed: F preserves the full composite
f, and graphs/induced restrictions are unchanged. Identities and nullaries
are preserved because F(id)=id and h(1)=1. For substitution, both routes
lift the same subsets, concatenate the same image strings, and have value
h(m·∏n_i)=h(m)·∏h(n_i). Thus theta_D is a strict base-changing calculus
map, with the slot numbering 1,…,k unchanged even when F identifies objects
or arrows.

The Ref map sends an entire arrow tuple (t_i) to (theta_D(t_i)). In (2.2)
coordinates it keeps its length vector lambda, maps every individual grade
in every run by F, and sends n_i to h(n_i). Its target equation is the image
of m·∏n_i=m'. Distinct tuples can become equal when h or F is noninjective;
no faithfulness is claimed. Formula (2.4) proves identity/composition
preservation entrywise, including zero-length runs.

Identity parameter maps act literally as identities. Composition applies
composite functors/homomorphisms entrywise, so it is literally composition on
objects and arrow data. The product maps of §3 commute on the nose: forgetting
a scalar and then applying F is the same cut, and forgetting a cut then
applying (F,h) is the same scalar-profile pair. Their Ref pullback comparisons
likewise commute on every full tuple, not merely on endpoint objects.

Ordered carrier relabeling may separately use a specified increasing
bijection j:[r]→[r'] (or between explicitly ordered finite carriers). It sends
G to the transported edge relation and U to j(U). Its restricted bijections
satisfy j∘i_U=i_(jU)∘j_U by uniqueness of increasing enumeration. This
identity proves all nested block/substitution comparisons. On standardized
initial-segment carriers an increasing bijection forces r=r' and is the
identity; the more general wording is a coordinate comparison, not an
unannounced graph-permutation symmetry. Arbitrary F is a comparison map, not
an invertible interface change. Only parameter isomorphisms yield inverse
maps. None of these statements supplies arbitrary groupoid-action descent,
noninvertible relational restriction, or virtual-equipment structure.

## 5. Syntax, completion, and coherent normal sections under parameters

This section uses the independently proved syntactic completion theorem,
not a full/faithful assumption. Write nu(t):t→N(eval t) for its coherent
chosen pure-equation normalization path; nu of a normal term is the identity.
Its key conclusions are: every two pure equation paths with the same endpoints
are equal under the LOCAL O relations, and every mixed Comp arrow is uniquely
determined by its full original-slot tuple of normalized forest entries.

### 5.1 Generator maps and all relation families

The raw syntax map theta_S sends each cut label to the same graph/subsets
with the image arrow string, u_A to u_(FA), and d_m^W to
 d_(h(m))^(theta W), WITHOUT prematurely deleting d_1. It maps identity leaves
to identity leaves and preserves every occurrence slot and graft. Therefore
it maps raw generators and their B1 composition/interchange relations to
raw generators and relations. It sends each of the seven equation templates
to the SAME target template instance: R uses F's composition preservation;
UL/UR use its identities; D0/DA use h's unit/product; DL/DR keep the cut label
and move the image value. This statement remains true if h(m)=1: a target
D_1 vertex is still a legitimate raw syntax vertex before normalization.

Consequently equation inverses and contextual instances map to corresponding
target paths. Each explicit O critical join word maps to the same word at
the image parameters, including degeneracies; the target O family includes
these instances. Disjoint and variable squares map to themselves because no
occurrence is deleted by theta_S. MOut maps to its target outer-equation
whiskering square. Bare MIn maps to its target insertion/template relation;
its derived arbitrary-context/forest version follows from those same mapped
relations. Hence this is an actual functor theta_C:Comp→Comp' on the
INDEPENDENT presented categories. No target semantic equality was used to
define its action or validate the relation basis.

The raw quotient map theta_Q is well-defined by the same template check and
the least-congruence universal property. Its composition is strict because
raw label maps and quotient representatives compose strictly. The actual
comparison maps satisfy on objects and arrows

    theta_C J = J' theta_Raw,
    P_Q' theta_C = Ref(theta_Q) P_Q,
    P_D' theta_C = Ref(theta_D) P_D.                         (5.1)

For raw arrows this equality applies theta to every original forest entry;
for equation edges both sides are the identity tuple after the same profile
transport. Generator equality and functoriality prove equality on arbitrary
words. The inherited quotient/semantic square Phi' theta_Q=theta_D Phi holds
on every represented tree by evaluation of mapped primitive generators, and
surjectivity of pi gives all quotient objects. Its arrow version is then
entrywise the same equality. Thus (5.1) is not only an object-level diagram.

### 5.2 The normal section is coherent, not literally invariant

For a full semantic object w define the isomorphism

    alpha_(theta,w) = nu'(theta_S N(w)):
      theta_S N(w) → N'(theta_D w).                         (5.2)

The endpoint is correct by evaluation preservation. If h kills a nonidentity
value, theta_S N(w) can contain a d_1 vertex whereas N'(theta_D w) does not.
Thus literal equality of the two raw objects is FALSE in general; (5.2) is
the required equation isomorphism.

Let S:Ref(D)→Comp be the explicitly constructed canonical-object section:
S(w)=N(w), and S(b_i) inserts N(b_i) at the original slots then follows the
coherent equation path to N(w'). For any semantic arrow b:w→w',

 theta_C(S(b)); alpha_(theta,w')
   = alpha_(theta,w); S'(Ref(theta_D)(b)).                   (5.3)

Proof without circular hypotheses. The left mixed path has normalized forest
entries N'(theta_D b_i), because theta_S N(b_i) evaluates to theta_D b_i.
For the right path, MOut moves alpha_(theta,w) past the raw insertion, and
MIn normalizes the inserted entries; it has exactly those same full original
slots and normalized entries. Their remaining pure equation paths have the
same endpoints and agree by O coherence. The proven path-normal-form theorem
therefore gives (5.3). This is also a consequence of the already proved
faithfulness of P_D', not an assumption of it.

For the identity parameter alpha is identity. For composable theta,eta,

 alpha_(eta theta,w)
   = eta_C(alpha_(theta,w)); alpha_(eta,theta_D w).          (5.4)

Both sides are pure equation paths from eta_S theta_S N(w) to
N''(eta_D theta_D w), so the independently proved O coherence gives equality.
No higher unmentioned coherence axiom is needed; repeating (5.4) makes all
associative compositions agree because category composition is associative.
The normalized parameter map between canonical full subcategories is

  on arrows b: alpha_(theta,w)^(-1); theta_C(S(b));
               alpha_(theta,w'),

which equals S'(theta_D b) by (5.3). It is therefore strictly compatible with
identity/composite parameter maps when indexed by the full semantic objects.
This is the exact sense in which normalization commutes with transport.

## 6. Complete local factorization fibres and their limits

Fix a full witness w=(G;(U_1,…,U_n);(f_1,…,f_n);m), n≥3, and a proper
contiguous interval [i,j] with 2≤j−i+1≤n−1. Write

    U = U_i ∪ … ∪ U_j,
    h = f_j⋯f_i : A_(i−1)→A_j,
    K_w=(G|U,h).

Consider the actual F1-shaped substitution map: its domain is the disjoint
union over ALL components K of outer witnesses with profile obtained by
replacing that subpath by K, paired with inner witnesses from the original
interval subpath to K. The map substitutes the inner witness at that one
outer occurrence and uses identity witnesses at every other outer slot.
No interval-cut axiom or simplicial structure is assumed.

### 6.1 The structural factors are forced

For a pair mapping to w, equality of the expanded partition forces the
outer distinguished block to be U. Its induced graph therefore forces the
graph of K to be G|U. The interval's full grade string has composite h, so
the output grade of the inner operation forces K's grade to be h; its
endpoints are already A_(i−1),A_j. Thus K=K_w, including actual arrow and
whole graph. The other outer blocks are U_1,…,U_(i−1),U_(j+1),…,U_n in
order. The inner blocks must be i_U^(-1)(U_i),…,i_U^(-1)(U_j), and their
full arrows are f_i,…,f_j. Formula (1.1) proves all input component equalities.
Conversely these structural outer/inner cuts are valid and substitute to the
underlying full witness. They keep all cross edges in G and all edges of
G|U, including edges between interval blocks.

Only the outer and inner values, call them a and b, are free. The substitution
value is ab, so there is an explicit bijection of the FULL fibre

    Fact_[i,j](w) ≅ { (a,b)∈M² : ab=m }.                    (6.1)

The forward map reads these two values. The inverse equips the forced cuts
above with them. The preceding uniqueness proves both inverse laws. This is
a fibre over a fixed retained whole AND partition, not an inference of G from
its pieces. Consequently its failure of injectivity cannot be blamed on
cross-edge loss.

### 6.2 Exact local uniqueness boundary

The map is surjective for every m, since (1,m) is a solution. If M is trivial,
(6.1) is a singleton for every witness. If M is nontrivial, choose m≠1.
The pairs (1,m) and (m,1) are distinct elements of the fibre; hence that
witness has at least two distinct factorizations. For every nonempty K and
N≥3 this can be demonstrated with three nonempty blocks and any retained
ordered graph at one interface, using identity grades. The mandatory mixed-
interface six-vertex model supplies a further nondegenerate instance. For
smaller N, empty blocks also provide n≥3, but are not the principal example.
If no objects/witnesses exist, a universal uniqueness assertion is vacuous;
we do not claim that vacuity forces M trivial.

Thus, in every nonvacuous stated family containing such interval witnesses,
ALL these local factorization maps are bijective iff M is the one-element
monoid. This is a sharp LOCAL boundary, not the full F1 recognition theorem.
For a particular m the answer is exactly its multiplication fibre, not a
blanket group formula. For example in {1,e}, the fibre of 1 is {(1,1)}, while
the fibre of e is {(1,e),(e,1),(e,e)}. In a finite group the fibre of m has
|M| elements. These elementary counts are consequences, not significance
claims or substitutes for the actual maps.

### 6.3 Unary, nullary, and chosen-shape iteration

Unary D(W;(W)) is precisely M, with only 1 the identity. The designated
nullary fibre D((empty,id_A);empty) is precisely M, with the chosen u_A
having value 1; all other nullary fibres are empty. Thus the nontrivial
M enrichment fails normalized-unary and unique-nullary hypotheses that a
stronger recognition theorem may require. No extra nullary is silently
redeclared an identity, and valid nonidentity unary witnesses are not removed.

If one separately defines a one-slot or full-interval substitution map in the
same way, its structural intermediate is respectively that slot's component
or W and the same multiplication-fibre calculation applies. These are not
additional proper intervals in (6.1). An inserted empty-interval operation
would require a designated (empty,id) component at a specified boundary and
an explicitly inserted empty outer block; it is additional unit data, not
an interval assumed by the theorem. We do not infer its coherence from (6.1).

For a FIXED planar substitution-tree shape whose vertices are semantic
operations, and a fixed full frontier witness w, the same descendant-union
argument determines each intermediate graph as the restriction to the union
of its descendant external blocks, and its grade as their ordered composite.
Nullary vertices force empty/id and unary vertices the same component. If
this shape is well typed, has q≥1 vertices, and every vertex's ordered children
are prescribed, all underlying vertex cuts are forced. Its complete value
fibre is then

    { (m_v)_(v in vertices) ∈ M^q : ∏_v m_v=m }.             (6.2)

Proof: apply (1.1) down the shape; the root whole is retained, each child's
support is the union of its descendant leaves, and the displayed structural
cuts flatten back to w by induction. Substitution multiplies precisely all
vertex values. Reading values and equipping those forced cuts are inverse
maps. For a vertex-free shape, only the actual identity operation is realized:
one external leaf equal to W and value 1. Formula (6.2) is NOT extended to
q=0 without that boundary condition.

Regrouping a chosen collection of factors multiplies their values; it can
forget their individual placements. This statement is about an externally
fixed shape and its fibre, not a canonical choice of factors or a bijective
comparison among all cut shapes. No simplicial identities, coherent chosen
cut operators, all-degree 2-Segality, CULF, F3 equivalence, or objective
incidence descent follow from these calculations alone.

### 6.4 Relation to operations, equations, and refinement tuples

A4's object presentation places all values at the root normal form: DA
aggregates, DL/DR move a value through a cut, and D0 removes only value 1.
Consequently it deliberately identifies different internal placements with
the same total value in a SINGLE operation. Equation (6.1) identifies exactly
why that operation normal form cannot uniquely recover the two factor values.
It does not identify different total values.

In Ref(D), by contrast, a tuple consists of separate operations at the original
source slots. The equations normalize the internal placement WITHIN each
entry. They do not move a value between different entries merely because
the resulting total m·∏n_i is unchanged. The bijection (2.2) and the Comp
arrow-normal-form theorem keep the n_i and child profiles separately. This
is why the Z/2 (0,0)/(1,1) example remains parallel and unequal, while two
presentations of either entry itself can become equal. A local cut of the
entry can again have fibre (6.1); no stronger cut uniqueness is restored by
retaining the tuple. These are precise inputs and boundaries for F1–F3,
not acceptance of those obligations.

## 7. Contribution and gate disposition

The independent object presentation and A4 normalizer were already verified;
this dossier does not claim to discover them again. Sections 2–4 and 6 are
explicit coordinate realizations of standard profile/scalar product and
category-of-substitutions machinery. Monoid labels are not physical data by
default. They do not produce scientific significance merely by being called
witness decorations, nor does multiplication-fibre arithmetic count as a new
recognition theorem.

The syntactic ordinary/mixed local-basis theorem is a separate technical bridge:
it must be proved from independently given path relations, and cannot be
replaced by (3.4). Its exact relationship to established coherent-presentation
theorems is assessed in the source/baseline audit. If that audit finds no
mathematical increment beyond specialization/integration, the correct outcome
is a technical correctness result with scientific-scope shortfall and a Gate 2
direction decision, not a fabricated novelty claim. Full §3.6 includes B4;
C1 still requires F2 use; D/E/F/G/I remain unactivated and open.
