# A nonthin dependent mixed test: probability presentations crossed with lists

Status: direct construction and proofs, plus finite regression checks. This is a difficult positive control of existing machinery, NOT a novelty claim, general recognition theorem, or adopted new contract. The negative tests reject two particular implicit-sharing recipes, not sharing itself.

## 1. The uniform test, not one closed simulation

Work in a fixed universe of sets (with a larger universe for categories). **Not FinSet:** List(B) need not be finite. Let Prob+ contain nonempty finite full-support normalized real probability spaces and deterministic measure-preserving maps. K_A = (Prob+)^A, with reindexing by precomposition. Its extension is e_A(P)=sum_(a:A) P_a; unit is the singleton family; dependent accumulation is

 (P tensor Q)_a = sum_(x:P_a) Q_(a,x),
 mass(x,y)=p_a(x) q_(a,x)(y).

The weight-preserving tuple bijections give its ordinary contextad structure, as in the earlier verified probability-family construction. Nothing here assumes new lax contextad axioms. List is a monad on Set, regarded as a singleton-fibre contentad, d_B(*)=List(B), with singleton unit and flattening multiplication. A mixed arrow A=>B is (P,f), f:e_A(P)->List(B). Its output list can have sample-dependent length and repeated elements. This is an actual dependent-family construction, not a constant grading.

A square (P,f)=F -> F'=(P',f') over u:A->A' and v:B->B' is a measure-preserving family alpha_a:P_a->P'_(u a) satisfying

 f'(u a,alpha_a x) = List(v)(f(a,x)).                         (S)

Vertical and globular compositions are actual compositions of these maps. Parallel distinct noninvertible cells are retained, not identified when their resulting output laws agree.

**Acceptance requirement:** define composition once for every such family, all set maps, and every such square; prove units, associator, pentagon, triangle, horizontal cell functoriality, associator naturality, reindexing, pure-middle balancing, and conservative context-only/content-only inclusions. This is stronger than matching a closed finite endpoint distribution. We do NOT demand that any contextual equivalence retain every internal witness; rather this chosen presentation-level semantics explicitly retains maps of witnesses, and its law quotient is assessed separately.

## 2. Derived crossing, with an explicit independence convention

For R in K_B, define a family C(R) over List(B):

 C(R)_[b1,...,bn] = product_(i=1..n) R_bi,
 mass(r1,...,rn) = product_i q_bi(ri).

Here and throughout, these independent products are the symmetric monoidal probability tensors on Cartesian carriers, NOT categorical products in the category Prob+ of measure-preserving maps. The empty product is the singleton probability space. The crossing map is

 chi_R: e_List(B)(C(R)) -> List(e_B(R)),
 ([b_i],(r_i)) |-> [(b_i,r_i)].                             (X)

The products range over **occurrences**, not distinct labels. A repeated b causes two fresh samples. This is the intended semantics of this test, NOT a theorem that every valid semantics must sample independently. Shared randomness can be supplied in an earlier retained context and explicitly passed forward; nothing prohibits that.

For a probability-family map theta:R->v*R', C(theta) sends (r_i) to (theta_bi(r_i)) over List(v). It is measure-preserving since

 sum_(r_i:theta_bi(r_i)=r'_i) product_i q_bi(r_i)
 = product_i sum_(r_i:theta_bi(r_i)=r'_i) q_bi(r_i)
 = product_i q'_(v bi)(r'_i).                              (P)

Thus noninvertible maps, not merely permutations, act. Identity and composition hold coordinatewise. The square for chi commutes literally: both paths produce [(v b_i,theta_bi(r_i))]. This includes noninjective v; it never deduplicates positions.

## 3. Both multiplications, and units, proved before packaging

**List unit:** C(R)_[b] is canonically R_b and chi sends r to [(b,r)].

**Context unit:** C(I_B) has exactly one point over every list; chi simply inserts the unique singleton coordinates. The empty list is essential: its product still has one point, not zero.

**List multiplication:** for a finite list of finite lists b_ij, the canonical map

 product_i product_j R_bij -> product_(i,j in lexicographic order) R_bij

concatenates the tuples. It is bijective, including empty inner/outer lists, and preserves weight because the products associate. Both crossing-then-flattening paths return [(b_ij,r_ij)] in the same order. Repeating this at any number of list levels yields the same occurrence address and coordinate, so associativity coherence is equality of the resulting maps, not just of distributions.

**Context accumulation:** for P over B and Q over e_B(P), the required comparison is the canonical dependent distributivity bijection

 product_i (sum_(x_i:P_bi) Q_(bi,x_i))
  -> sum_((x_i):product_i P_bi) product_i Q_(bi,x_i),
 ((x_i,y_i))_i |-> ((x_i)_i,(y_i)_i).                       (D)

Both weights are product_i p_bi(x_i) q_(bi,x_i)(y_i). The inverse pairs coordinates. For general maps phi:P->v*P' and psi:Q->(v odot phi)*Q', either path applies phi to every x_i and psi_(bi,x_i) to every y_i. Hence (D) is natural for simultaneous noninvertible changes at both levels. This is a direct proof; invertible interchange/Beck-Chevalley was NOT assumed as an input condition.

All mixed coherence between flattening and (D) is checked by indexing a leaf with its finite occurrence address and recording the successive dependent samples along its ancestry. Every comparison only changes parentheses. Every route has the same final address-labelled sample tuple, with the same product of conditional factors. The coordinate identity proves equality of maps (including witnesses), hence pentagon/triangle and naturality. Finiteness ensures these rearrangements and product-of-sum formulas are legitimate. No convergence or disintegration theorem is hidden here.

## 4. The resulting cell-preserving composition

For F=(P,f):A=>B and G=(Q,g):B=>C, write f(a,x)=[b_1,...,b_n]. Define

 (G circ F).context_a = sum_(x:P_a) product_i Q_bi,
 weight(x,(y_i))=p_a(x) product_i q_bi(y_i),
 (G circ F).output(a,x,(y_i)) = concat_i g(b_i,y_i).         (M)

This is finite full-support normalized at each a, even when A,B,C are infinite. Each list is finite and each involved fibre finite. Unit at A uses the singleton probability family and output [a].

For a third H=(R,h), let g(b_i,y_i)=[c_i1,...,c_i m_i]. The associator sends the left-grouped sample

 ((x,(y_i)), (z_ij) in concatenated occurrence order)

 to the right-grouped sample

 (x, ((y_i,(z_ij)_j))_i).

It is an explicit bijection. Both weights are p_a(x) product_i q_bi(y_i) product_(i,j) r_cij(z_ij), and both outputs concatenate h(c_ij,z_ij). The empty/variable-length blocks do not lose their boundaries: those are recoverable from g(b_i,y_i). The inverse splits the z tuple using precisely these lengths. Units remove the unique singleton coordinates.

For composable squares alpha:F->F' over (u,v) and beta:G->G' over (v,w), horizontal composition is

 (x,(y_i)) |-> (alpha_a(x),(beta_bi(y_i))_i).              (H)

Equation (S) ensures identical position counts, with target labels v(b_i). For fixed target sample (x',(y'_i)), sum over the alpha-preimages x. For each x, equation (P) gives product_i q'_(v bi)(y'_i); by (S) this is independent of the chosen x in the alpha fibre. The remaining sum is p'_(u a)(x'). Thus (H) is measure-preserving even when alpha and beta are noninjective and different source labels merge under v. Output compatibility follows by List(w) preserving concatenation. Identity, vertical composition, and interchange follow coordinatewise. Associator naturality sends each x,y_i,z_ij through alpha,beta,gamma respectively along both paths. Together with the addressed-tuple coherence proof, this supplies a bicategory of globular cells and the corresponding endpoint squares/pseudo-double composition; it does not throw away cells to make associativity work.

**Conservative inclusions:** a context-only arrow uses singleton output lists, and (M) becomes the original dependent-pair contextad composition. A content-only arrow uses singleton context fibres, and (M) becomes List Kleisli substitution. Both inclusions preserve their specified units/compositions through the displayed canonical isomorphisms. Base reindexing a'=>(u a') is literal substitution into (M). This preserves all dependent fibres and cells, not merely their pushforward laws.

## 5. Exact relation to coends and existing mixed machinery

Let M(A,Z) be the category of context-only presentations e_A(P)->Z and their probability maps; N(Z,B) is the discrete category Set(Z,List B). The already proved local Cat-coend/comma lemma specializes to

 integral^Z M(A,Z) x N(Z,B) ~= Mixed(A,B).

The functor sends (P,x:eP->Z,y:Z->List B) to (P,yx); inverse splits at Z=eP and x=id. The proof on noninvertible morphisms uses the same balancing along e(alpha), not passage to isomorphism classes. Thus the mixed local hom category is already an ordinary strict Cat-coend, including its actual parallel cells.

For the opposite ordering N(A,Z) x M(Z,B), define the crossing on (f:A->List Z,Q,g:eQ->B) by context product_i Q_f(a)i and output [g(f(a)_i,y_i)]. Balancing a pure map v:Z->Z' replaces f by List(v)f on one side and Q' by v*Q' on the other. The fibres and positionwise maps are literally the same product, hence the crossing descends through pure-middle balancing. This is exactly where the earlier finite quotient/domain normalization failed. The calculation is valid on the noninvertible cell generators too by (P).

The laws in sections 3–4 are the actual lifted crossing laws for this family, and derive the mixed composition directly. On isomorphism classes, the one-sided categories are identity-on-objects extensions of Set, hence promonads in Prof; the crossing supplies the corresponding distributive law. At the retained-cell level, the explicit local Cat-coend and explicit coherent mixed bicategory are established here. A general equivalence between all such weak indexed structures and one chosen pseudo-Profunctor ambient has NOT been established; this example does not silently assert it. That global recognition theorem remains a possible theoretical target, rather than an obstruction to this concrete positive construction.

## 6. Nonthin cells are real, not decorative labels

Take the uniform source sample P={0,1}^3 with coordinates (u,v,w) and target P'={0,1}^2 with coordinates (u,t). Let f(u,v,w) be [] when u=0 and [b0,b1,b0] when u=1, and let f'(u,t) have the same rule. The two maps alpha(u,v,w)=(u,v) and beta(u,v,w)=(u,w) are distinct, parallel, noninvertible probability-preserving cells between genuinely nonconstant mixed arrows. Target flip(u,t)=(u,1-t) is a nonidentity automorphism preserving the body. Flip*alpha and flip*beta remain distinct. Horizontal composition with a later family having different probability spaces over b0 and b1 acts on the retained first sample as alpha/beta and on all three later occurrences coordinatewise. The cells remain distinct: choose u=1,v=0,w=1, and any supported later sample tuple. This is not a quotient relation masquerading as a 2-cell. It simultaneously involves sample-dependent list length, repeated outputs, distinct later context types, noninvertible parallel maps, and a nontrivial automorphism.

The nonconstant dependent regression separately varies input fibre sizes, output-list length, output labels, second-stage fibre sizes, and subsequent enabled sample indices; its cells act in multiple stages simultaneously. Constants suffice only to expose parallel cells; they are not the whole test. Empty lists legitimately erase their unused context data, so no false claim of global faithfulness of every whiskering is made.

## 7. Two exact failures of local label-based sharing

Consider the alternative recipe 'for each distinct label in the current list, draw once and reuse that draw at every repeated label.' This is a meaningful proposed local policy, but NOT natural under arbitrary set maps and NOT compatible with all List multiplication.

**Noninjective base-change failure.** Let B={a,b}, B'={x}, v(a)=v(b)=x, and R'_x be a fair bit. Pullback R=v*R' gives the same bit fibre at a and b. On the list [a,b], the per-label recipe has two independent draws: outputs disagree with probability 1/2. After List(v), that gives two possibly unequal bits at x. On [x,x], the recipe uses one draw copied twice: disagreement probability 0. No output-preserving measure-preserving comparison between these two experiments can exist in either direction, since such a comparison preserves the output law. The missing naturality cannot be restored by choosing a different bijection of the existing fibres.

**Flattening failure.** For [[b],[b]], share separately within each inner list: the two singleton blocks draw independently, giving disagreement probability 1/2. Flatten first to [b,b] and share in the flattened list: disagreement probability 0. The recipe fails the content multiplication law, not merely a desired operational endpoint test.

These statements are restricted: a persistent explicitly named cache/world can keep the correct joint sharing across boundaries; alternatively restrict base maps or change the objects to record aliasing identities. Neither is ruled out. What fails is inferring persistent sharing solely from equality of the current visible labels while demanding arbitrary reindexing and flattening. We do not claim the independent crossing is the unique possible law.

## 8. Strongest relevant baseline and scope

Primary baseline: Mauro Jaskelioff and Ondrej Rypacek, *An Investigation of the Laws of Traversals*, arXiv:1202.2919, EPTCS 76 (2012), https://arxiv.org/abs/1202.2919. Theorem 3.7 proves finitary containers traversable; Lemma 4.1 proves preservation of Kleisli composition for a **commutative** monad. Its proof specifically uses that the monad multiplication is an applicative morphism. We do not infer this law for arbitrary monads. Lists are the finite-position container at issue here. The paper does not by itself assert our retained probability-presentation cell theorem; that is proved above directly.

Evaluation E sends (P,f) to the kernel a |-> [ell |-> sum_(x:f(a,x)=ell) p_a(x)] in D(List B). On globular cells it sends all probability-preserving maps to equality of this kernel. In particular alpha and beta above have the same image; E is not locally faithful. The construction (M) evaluates to Kleisli composition for D composed with List, but this law-only quotient is not itself a solution to the retained-cell obligation.

To obtain the law-level transformation with full typing, index a probability family R over D(B) by R_mu=support(mu), with the inherited positive weights. Apply (X) to a list of such distributions, then forget the distribution labels in each pair (mu,b). This gives the familiar independent-product transformation List(D B)->D(List B), where D is finite normalized distribution. A set map B->B' induces the measure-preserving map from each support to the support of its pushed distribution, so the stated base-change calculation proves naturality of this transformation. Its compatibility with D multiplication is the finite product-of-sums identity (commutativity allows regrouping choices); its compatibility with List multiplication is ordered block flattening; both units are singleton/Dirac. Thus it is the standard distributive-law pattern, not evidence that a new generalized contextad is necessary. The displayed elementary calculations prove this exact specialization without relying on an unaudited generic theorem.

Contextad baseline: Capucci–Myers, *Contextads as Wreaths*, https://arxiv.org/abs/2410.21889 , Definition 3.26 and Section 6. The finite probability-family contextad is our earlier verified construction satisfying Definition 3.26, not a verbatim example claimed from that paper. Promonad comparison: Román, *Promonads and String Diagrams for Effectful Categories*, https://arxiv.org/abs/2205.07664 , Theorem 3.9/B.2, with its earlier source audit retained. These supply structural descriptions, not a derivation of (X). Our choice and verification of (X) are explicit.

The List contentad has terminal fibres in this test. Nonthin structure is in the dependent context fibres and the resulting mixed hom categories; this is NOT yet a test with independently nonthin context and content fibres on both sides. The exact global mixed-ambient equivalence for general such pairs remains outside the theorem.

The result's significance is methodological: an existing traversal/product construction passes a stronger uniform dependent and nonthin test, while the nearby implicit-cache recipe fails genuine naturality and multiplication. A law-only kernel semantics passes extensional execution but is not faithful on the retained sample maps. This locates exactly what each comparison preserves. No separation from all existing indexed, bicategorical, container, or game models has been proved, and no efficiency advantage is claimed.

## 9. Reproducibility

`check_nonthin_categorical.py` implements exact rational checks for the nonconstant dependent fixture, simultaneous stagewise noninvertible maps, composition/associator naturality, product crossings, and the two sharing counterexamples. Its output states finite test counts. These are regression checks, not a finite substitute for the all-families proofs above. Run with both normal Python and python -O; checks explicitly raise errors and do not rely on removable assert statements.

Regression outcome (normal Python and -O, outputs identical): 105701 explicit checks. Of these, 13133 are associator naturality comparisons over all samples of the chosen two-input fixture; 13133 each check associator outputs and each of the two three-stage cell outputs. There are 40 nested finite product flattening checks and 5 noninvertible product-map checks. The largest three-stage fibre has 12939 points. Counts include repeated structural checks (for example 52532 tuple-consumption checks); they are not 105701 independent theorems. The general pentagon/triangle are proved by addressed tuples above, not inferred from these finite counts.

Independent review covered sections 1–8 and checked the noninjective-middle-map mass argument, dependent sum/product bijection, variable block inverse, empty products, addressing coherence, local coend limits and sharing counterexamples. No substantive defect found. This is an independent mathematical check, not external publication peer review or machine formalization.
