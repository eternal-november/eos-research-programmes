# Original mixed presentation: source inventory and minimum extension

29 October 2026. Source audit, not a new proof or obligation discharge.

## Abstract

The original seven-rule calculus already has complete normal forms and an independently presented refinement category. It does **not** itself contain arbitrary interface restrictions. These belong to a separate free equipment envelope, whose new cells have not been classified by those normal forms. A later finite-span presentation has such a classification, but expressly adds many generators. The next theorem must bridge this precise gap rather than quietly substitute that larger presentation.

## Source key

Paths below are relative to `references/contract/`.

* **A** `extracted/witnessed_decompositions/research/workstream_A/rewrite/A3_LOCAL_COMPARISON.md`
* **T** same directory, `THEOREM.md`
* **C** `extracted/witnessed_decompositions/research/workstream_integration/proof/Completion_Comparison.md`
* **S** same directory, `Semantics_Transport_Factorization.md`
* **V** `structural_extracted/proof/Conservative_Equipment_Envelope.md`
* **E** same directory, `Extended_Local_Presentation.md`
* **G** same directory, `Global_Cut_Repair.md`
* **Q** same directory, `GraphDependent_Quotient_and_Cut_Memory.md`
* **N** same directory, `TerminalRestriction_NoGo.md`

## 1. Frozen original sorts and generators

Parameters: finite category K, finite commutative monoid M with unit 1, graph size bound N. The general normalizer is all-N; A's principal adapter states N≥6 and S §1 explicitly extends that adapter to small N. No arity/depth bound. Principal tests require multi-interface, nonidentity arrows and N≥6.

An ordered graph G has vertex carrier [r], r≤N; equality retains its adjacency matrix, not only graph isomorphism. For U⊆[r], i_U:[|U|]→[r] is the increasing enumeration. Literal identities:

    i_(i_U(V)) = i_U i_V;       (G|U)|V = G|i_U(V).

A component W=(G,f:A→B) includes both endpoints. A full profile is the actual ordered path

    p=((G_1,f_1:A_0→A_1), …, (G_n,f_n:A_(n−1)→A_n)).

An original operation has the same outer endpoints as its output; there are no additional nonglobular boundary maps. Neither intermediate objects nor individual arrows may be recovered merely from the composite. Repeated equal components remain different occurrences. [A §§1–2; T §§1–3]

| Original generator | Exact source and output |
|---|---|
| c_(G;U,V;a,b) | ((G|U,a:A→B),(G|V,b:B→C)) ⇒ (G,ba:A→C), U⊔V=[r], either block may be empty |
| u_A | empty path **at A** ⇒ (∅,id_A) |
| d_m^W | singleton path (W) ⇒ W, for each m∈M |
| Identity leaf x_W | Structural tree leaf, not an extra primitive generator |

No exchange, copying, contraction, graph-isomorphism quotient or deletion of arbitrary empty-graph components is present.

## 2. The seven original equation templates

Each declaration initially uses identity leaves in one exact full profile. Arbitrary metavariable instances and contexts arise through the least parallel substitution congruence, not a semantic-kernel definition. [A §§2–3]

| Rule | Formula | Essential typing/data |
|---|---|---|
| R | c(c(x,y),z)=c(x,c(y,z)) | Triple partition (U,V,W) and arrows (a,b,c). Left outer labels (U∪V,W;ba,c), inner blocks i_(U∪V)^−1(U,V); right outer (U,V∪W;a,cb), inner i_(V∪W)^−1(V,W). Both keep all three actual frontier arrows. |
| UL | c(u_A,x_W)=x_W | Only labels (∅,[r];id_A,f), W=(G,f:A→B) |
| UR | c(x_W,u_B)=x_W | Only labels ([r],∅;f,id_B) |
| D0 | d_1(x_W)=x_W | At one fixed full W |
| DA | d_m(d_n(x_W))=d_(mn)(x_W) | At one fixed full W |
| DL | c(d_m(x_X),x_Y)=d_m(c(x_X,x_Y)) | Same binary cut label; right d is at output W |
| DR | c(x_X,d_m(x_Y))=d_m(c(x_X,x_Y)) | Same qualification; semantic soundness uses commutativity of M |

Profiles have respectively 3,1,1,1,1,2,2 external leaves. u_A is zero-leaf; x_(∅,id_A) is one-leaf and cannot trigger UL/UR. Decorated nullary values are not deleted. [T §3]

## 3. Existing normal forms and actual cut/refinement data

FlatCut operation:

    w=(G; U_1,…,U_n; f_1,…,f_n; m),
    U_1⊔…⊔U_n=[r],  G_i=G|U_i,  f_n…f_1=f,  m∈M.

The full profile p and output (G,f) are retained. Substitution lifts child blocks by i_(U_i), concatenates their **whole paths**, and multiplies outer and all child scalar values. The whole G including cross-edges does not change. [A §4]

Canonical N(w): a right comb with root first block U_1, remaining union V and remaining-arrow composite; recurse on G|V. For n=1 use x_W; for n=0 use u_A. Add only one root d_m when m≠1. Theorem T §§4–6 proves termination by lexicographic (binary count,left-binary count,decoration binary-depth,total decorations), confluence, and equality iff equal full flat data. A §§5–6 proves the actual A3 quotient is strictly isomorphic to FlatCut, not just sound evaluation.

**Nullary original case:** n=0 iff G=∅ and f=id_A with both outer interfaces A; arbitrary m survives. No nullary at empty nonidentity loop or unequal endpoints. [T §2]

**Interval factorization:** for I=[i,j], let U=∪_(k∈I)U_k and h=f_j…f_i. Intermediate is forced to (G|U,h), inner blocks are i_U^−1 U_k and inner full arrows f_i,…,f_j. The full factorization fibre is

    {(a,b)∈M² : ab=m}.

Thus nontrivial M prevents unique cuts in general. Root normal form is not recovery of separate factor values. Fixed tree shape with q≥1 semantic vertices has fibre { (m_v)∈M^q : ∏m_v=m }; vertex-free case is only actual identity. [S §6]

**Refinement:** from source with k occurrences to target with l, retain an admissible run vector (l_1,…,l_k), sum l, and a local n_i per original slot with m∏n_i=m′. Each target run partitions U_i, has the exact source-slot endpoints and composes to f_i. Empty run requires U_i=∅ and f_i=id; its n_i survives. Equality of endpoints does not identify different vectors/entries. [S §§2.1–2.3]

Independent completion C has directed grafts and invertible seven-equation steps; relations Rcat, O (18 critical-peak families plus disjoint/variable squares), MOut and MIn derive the actual semantic refinement comparison. This is already proved; it is not the new restriction criterion. Omitting MIn leaves spurious loops measured by added raw vertices. [C; integration/FailureAndRevisionRegister.md item 4]

## 4. Which interface changes are actually present?

| Layer | Supported change | Not supplied |
|---|---|---|
| Original C5 | Arbitrary functor F:K→L applied to each interface/arrow; monoid hom h:M→M′; N inclusion; specified increasing carrier bijections | No cartesian restriction cell or arbitrary boundary reindexing inside this Calc |
| Original completed refinement category | Same parameter maps on raw generators, equation paths, and occurrence tuples; coherent normal section α_(θ,w):θN(w)→N(θw) | Nonfaithful F/h need not reflect equality/lift arrows; cannot call parameter map an invertible interface change |
| Free chosen V envelope | All finite maps of tagged-set base B; fresh H[f,g], fresh I_A; cartesian κ and all-arity factor L; contextual unit η,U | No equality of fresh horizontal expressions; no proved normal forms or full classification of new old-profile cells |
| Extended finite-span E | Every H(G,S), every finite span square u_f named; arbitrary pullback restriction derived from exact normal forms | These additional generators are not proved generated by C5 + fresh restrictions/units |

Original parameter claims and explicit limit: T §8 and S §§4–5. F may identify objects/arrows and h may kill scalars. Then θN(w) need not literally equal N(θw); equation-path comparison is required. Noninvertible parameter transport is real, but **not** arbitrary noninvertible interface descent.

## 5. Minimum supported extension to state the proposed target

Use the existing **free chosen virtual-equipment envelope V of the original local signature**, not E and not ordinary equipment O unless composites are genuinely needed. [V §§1–4]

The base B is a small full category of finite **tagged** sets containing the faithful realization

    F(A)={(C,u):u:C→A},       F(h)(C,u)=(C,hu).

Fresh horizontal grammar: old W; I_A; H[f,g]. Keep H[id,id] and H distinct as expressions, and old (∅,id_A) distinct from fresh I_(F A). Universal comparison cells may be isomorphisms; they are not type equalities.

Full cell sort:

    α:(P_1,…,P_n)⇒H ; (f:A_0→B_0, g:A_n→B_1).

Substitution retains the whole matched interface-map family u_0,…,u_m. At m=0, **u_0 remains**, giving α⟨u_0⟩. For a nullary cell f,g may differ but have the same specified domain A_0.

Added constructors κ_(H;f,g), η_A, cartesian factor L(α), contextual unit factor U_(r,A,s)(α). Equations, in every typed context:

    κ·L(α)=α;       L(κ·β)=β;
    U(α)[1_r,η_A,1_s]=α;  U(β[1_r,η_A,1_s])=β.

Retain original seven equations and all VDC laws. Congruence must close under **L,U as well as substitution**. Otherwise it is not the existing free chosen envelope.

This is a clarification/extension of the target's language, not a weakening: original C5 cannot express the proposed restriction problem. Any claimed explicit criterion must handle these new constructors or prove a bridge to another presentation. V proves conservativity of old equalities and actual old refinement tuples and reflection of old unary isomorphism existence; it explicitly does **not** prove fullness or classify all new old-profile cells. Do not infer the desired bridge from conservativity.

## 6. Extended presentation: usable calibration, not original syntax

E §§1–4 names all actual spans and maps. Its different seven schemes are (S),(D1),(D2),(N2),(N0),(A),(U). N2 requires the SAME actual middle boundary map; N0 is u_(I_h)c0_A=c0_B⟨h⟩; A uses actual tuple-flattening bijections; U deletes only designated diagonal unit. Normal form in each fixed full horizontal path/output/outside-boundary sort is

    NF(π,φ,m;f,g)=u_(f,φ,g) d_m c_flat(π;p),
    l_S φ=fπ_0,       r_S φ=gπ_n.

For empty p at A, P(p)=A, not a singleton or absent boundary. Nullary φ may encode differing outside maps and retains m. E §5 derives restrictions by φ↦(hπ_0,φ,kπ_n). E §8 recovers full old globular fibres (unique forced coefficient on graph spans), but explicitly denies equality with the C5-only free envelope or generation of all spans/squares from it.

## 7. Existing obstructions a new theorem must not erase

| Failure | Exact scope / repair constraint | Source |
|---|---|---|
| Scalars have several factorizations | Retain whole scalar factor fibre, not just root total or canonical placement | S §6 |
| Equipment quotient valid but coherent-cut witness lost | Graph-activated coefficient forgetting can preserve equipment and old fibres; retain actual inner bijections for repaired tree cuts | Q; G §§6–11 |
| Restriction equations return to old profiles | Terminal restrictions a↦a^A admit retraction r(α)=χ·α[β_i] using matched sections; a^A=b^A forces a=b. Marking existing cells cartesian can destroy prior conservativity | N |
| Nonempty restriction comparison not always invertible | c_f:P(reindexed spans)→reindex(P(spans)); fibre over a feasible tuple =∏_(0<i<n) f_i^−1(a_i) | G §10 |
| Nullary is not empty-product case | I_(A′)→(f,f)*I_A is diagonal A′→A′×_A A′, bijective iff f injective | G §10 |
| Primitive adjacent-pair checks miss longer failure | Three singleton-witness spans through internal value 1; restriction selects 0 at both middle boundaries. Pair tests empty→empty; whole triple empty→singleton | G §10 |
| Root quotient exactness misses intermediate failure | Active whole with cross-edge but inactive two-block induced graph: 2→1 comparison becomes invertible at root quotient but not inactive inner cut | G §10 |

G §10's criterion ranges over actual composite-child spans at every relevant interval and unit; it is a finite-span semantic criterion, not yet a derivation for the smaller original envelope. The repaired action covers all finite planar/laminar trees, not an automatic arbitrary crossing calculus theorem.

## Audit conclusion

The source-grounded hard target is: derive a quotient/cut/lifting criterion for the **original seven-rule presentation inside its explicit free chosen envelope**, keeping original-profile conservativity as a separate obligation and retaining every common boundary and factor witness. Establishing only the already-proved C5 normalizer, E span normal form, or G fibre test does not meet it. This inventory proves no new theorem and changes no acceptance status.
