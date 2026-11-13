# Active-input witness enrichment: model laws, relative presentation, old-language comparison

Author proof, 31 October 2026. Scope is the frozen `concrete_model_gate.md`, not unrestricted graph spans. Terminal old scalar is sufficient; the same proof works if original scalar data are retained exactly. This proof imports the specifically pinned original C5 presented-calculus theorem below at its actual scope and supplies the NEW enrichment/comparison argument. No old theorem is assumed to cover the new D relations automatically.

## 1. Construction and laws

Let P be the original ordered graph-C5 multicategory. Every operation α has an actual ordered partition `(U_i)` of its output graph, and input graph i is the corresponding induced graph. Thus a nonempty output has at least one nonempty input; an empty output has only empty inputs; a nullary output is empty. Let L be any monoid, not necessarily commutative.

Define P[L] with the SAME colors and full ordered profiles. Its operations are `(α,(l_i)_{U_i≠∅})`. When substituting `(β_i,(m_ij))` into `(α,(l_i))`, retain the original C5 composite and label each nonempty final block by `l_i m_ij`. All final nonempty blocks have nonempty ancestors, so both factors exist. Identity on a nonempty color has label e; identity on an empty color has the empty tuple.

**Theorem 1.** P[L] is a nonsymmetric multicategory; the projections to P and its all-e section are multicategory morphisms.

**Proof.** Graph/grade profiles are those of P. For three substitution levels, each nonempty final block (i,j,k) receives `(l_i m_ij)n_ijk` under one association and `l_i(m_ij n_ijk)` under the other. These are equal by associativity in L. No label from a different branch is reordered. Empty final blocks have no label on either side; their old occurrence data are retained, not deleted. Unit substitution multiplies each existing label by e on the appropriate side, with the empty case unchanged. Forgetting labels and assigning all labels e plainly preserve these formulas. ∎

The added labels are not arbitrary decoration ignored by operations: one parent factor acts simultaneously on all nonempty descendants. This is the exact source of the correlated cut equations below.

## 2. Relative generator/relation presentation

Assume a sound-and-complete old presentation `(Σ,R)` of P with full profiles retained. For every nonempty color H and l∈L, adjoin a unary generator `D_H(l):H→H`. Add relations

1. `D_H(e)=id_H`;
2. `D_H(l)∘D_H(m)=D_H(lm)`;
3. for every OLD generator `g:(H_1,...,H_n)→H` with nonempty H,

   `D_H(l)∘g = g∘(d_1,...,d_n)`,

   where `d_i=D_{H_i}(l)` for nonempty H_i and `d_i=id_{H_i}` otherwise.

No D is added on an empty color. Retain all R. These relations have the exact same full profiles on both sides. For fixed finite graph bound, finite K and finite L, this is a finite added generator/relation family whenever the original chosen Σ is finite; otherwise it is the same effective color/generator schema as Σ. It is not an enumeration of all true semantic equations.

**Lemma 2 (extended diagonal law).** Relation 3 holds with any old composite t in place of g.

**Proof.** Induct on an old presentation tree. For an identity use the identity law. At a generator with substituted old subtrees, push D across the generator by relation 3 and then across each nonempty child subtree by induction. Empty child subtrees have only empty descendants, so no D needs to be pushed there. The two sides consequently have D(l) at precisely the nonempty external inputs. Relations R have fixed profiles, so replacing an old tree by an R-equivalent one respects the resulting substitution equations. ∎

**Theorem 3 (relative soundness/completeness and conservativity).** The extended presentation presents exactly P[L]. Every extended term is equal to a normal form

`t∘(d_1,...,d_n)`,

where t is an old term and d_i is D_Hi(l_i) on nonempty external inputs and identity on empty ones. Two such normal forms are equal iff their underlying old operations agree in P and all corresponding l_i agree in L. The old inclusion is faithful on every full profile.

**Proof.** Interpret old generators with all-e labels and D_H(l) as the unary old identity with label l. Each relation is valid by Theorem 1's formula, including relation 3, so there is a sound interpretation.

Normalize by induction on an extended term. The old-generator case and D case have the displayed form. Suppose an outer normalized old term α with boundary labels l_i is substituted by normalized old terms β_i with labels m_ij. By Lemma 2, move each D(l_i) across the old term β_i; then combine successive unary D's using relation 2. The resulting normal form has old composite α[β_i] and label l_i m_ij at each nonempty final input. Empty ancestors contain no nonempty descendants and add no omitted factor. This proves normalization without a termination or confluence assumption on a chosen rewrite orientation.

If two normal forms have the same semantics, their old terms are equal by completeness of `(Σ,R)` and their labels agree literally. Apply the old equality and then substitute the same boundary D tuple to derive their equality in the extension. Conversely sound interpretation prevents equality between different old operations or different labels. Every operation of P[L] is represented by any old representative of α followed by its specified D tuple, so interpretation is surjective. Finally forgetting every D to identity defines a retraction onto P; equivalently the normal-form criterion gives faithfulness of the old all-e inclusion. ∎

This theorem is relative to the established old presentation, not a claim that all original C5 obligations were accepted. It supplies a reusable local enrichment rather than redefining the original global scalar to be noncommutative.

## 3. Joint cuts and original-language comparison

Fix an actual old planar cut tree T of α, including all intermediate old components, occurrence positions and old factor operations. An extended cut of `(α,l)` over T assigns a label to every nonempty input edge of every internal operation. Its composite label at external active leaf j is the ordered product of labels on the root-to-leaf spine. Equivalently every elementary contraction obeys `x_ij=a_i b_ij` with the SAME a_i for all active descendants within block i.

**Lemma 4 (forgetting and existence reflection).** Every extended cut forgets to the specified old cut. Conversely every old cut T of α lifts to an extended cut of `(α,l)` for every external label tuple l.

**Proof.** Forgetting follows from Theorem 1. To construct a lift, put label e on each nonempty internal edge and put the required l_j on the input edge at the actual external leaf j. Every root-to-leaf product is then l_j. If the tree has only one operation, this is its label tuple. Empty external occurrences and empty subtrees have no label and retain all old data. ∎

Thus any old label-blind existential joint-cut query with fixed old factor conditions has the same truth before and after adding labels. This does not preserve its witness count, chosen witness, gauge or isotropy. For example a unit l with inverse produces a nontrivial two-factor cut of an all-e unary operation. Added label-sensitive tests have strictly more expressive power and are not covered by the old-language comparison.

The actual joint constraint at one grouped block is

`exists a in A, b_j in B_j for all j: x_j=a b_j`.

It is not equivalent to `for each j exists a_j in A,b_j in B_j: x_j=a_j b_j`. A finite witness model must retain the common a. The general I5 repair calculus uses the former relation, with possibly relational (non-product) quotient blocks for entire factor operations.

## 4. Actual two-channel interface action

For the principal transformation monoid M≤End([k]), put L=M×M and B={0,1}×[k]. Represent `(x,y)` by the block-diagonal function

`F_(x,y)(0,z)=(0,x(z)); F_(x,y)(1,z)=(1,y(z))`.

Use the same composition convention as the chosen monoid presentation. The channel permutation `sigma(c,z)=(1-c,z)` satisfies

`sigma F_(x,y) sigma^{-1}=F_(y,x)`.

Hence swapping the actual interface frame conjugates every branch witness by the same concrete channel permutation. It preserves multiplication, so it defines a multicategory isomorphism between the two framed copies of P[L]. Applied twice it is identity; it does not permute planar input occurrences. It carries every actual cut record to the correspondingly swapped actual cut record, since `x=a b` implies `swap(x)=swap(a)swap(b)`.

The seed readout is first LOCAL channel membership in H in BOTH frames. It is not equivariant with the swap, by design and by the declared observation protocol. If H is proper and nonempty, choose u∈H,v∉H: witnesses `(u,u)` and `(u,v)` agree initially but their transports do not. T therefore adds genuine information. This is observational refinement, not enlargement of interface-change authority.

## 5. Single-vertex reduction for cut repair

Let Q be an equivalence on L. On every old operation whose output graph has exactly one vertex, put the uniform label equivalence Q while retaining all old data exactly. Such an operation has exactly one active external input, although its arity can be arbitrarily large. On empty-output operations there is no label to quotient.

For one-stage cuts of a one-vertex operation, graph vertex conservation gives exactly one active outer input and one active inner input; their labels a,b satisfy ab=x. Every other factor has an empty output graph and no added label. The complete old skeleton, including all empty positions and grade arrows, is independent of x.

Define the ordered monoid-factorization signature

`F_Q(x)={([a]_Q,[b]_Q):a b=x}`.

**Lemma 5.** The family Q on all one-vertex profiles is stable under all elementary joint cut tests iff Q is stable under F_Q. Stability then holds for all finite generated cut trees on these profiles.

**Proof.** Each old elementary cut signature is a fixed skeleton-indexed copy of F_Q(x), with unique empty labels appended. Thus monoid stability implies elementary-cut stability. Conversely the old unary insertion cut realizes every pair a,b with product x and distinguishes every pair of Q classes occurring in F_Q, so elementary-cut stability implies monoid stability. A cut tree on one vertex has exactly one nonempty spine; all off-spine subtrees are empty. Its additional witness records are finite ordered factorization chains. By induction on the chain, elementary stability transports the first factor's class and then the remaining product's class, preserving the full ordered tuple jointly. Equivalently split off one elementary cut at a time. This is class-wise existential realization, not lifting a preselected actual factor tuple. ∎

**Theorem 6 (no hidden higher-arity C backpressure).** Start from the gate's profilewise uniform E0. The full C-only repair restricted to any one-vertex old operation equals the ordinary monoid-factorization repair of its label seed.

**Proof.** First prove simultaneously over ALL singleton old records that any global C-stable refinement E determines every monoid cut-splitter stage q_t. At t=0 this is the uniform initial readout. If it holds at t, take an actual elementary cut of a source record. The outer and inner E classes each determine their q_t label class, even when these two records have different E partitions. Projecting the full joint E signature to those determined classes gives EXACTLY F_{q_t}(x), by realization of every binary factorization at that fixed old skeleton. C stability therefore forces equality of F_{q_t}, hence q_{t+1}, at every singleton record. Induction to the finite monoid fixed point proves that every such E refines Q on every singleton record. This does not presume the independently varying E partitions are identical. Conversely use Q on every one-vertex old operation, the unique label equivalence on empty-output operations, and the discrete label partition on every operation whose output has at least two vertices. This refines E0. At larger outputs source equivalence is equality, so cut stability is automatic. Cuts of one-vertex outputs cannot have factors with larger output graphs, and Lemma 5 proves their stability; cuts of empty outputs have no added labels. Thus this is a global C-stable extension of Q. Leastness of the global C repair forces its restriction to be no finer than Q. Both inequalities give equality. ∎

The theorem does not assert that S cannot send a singleton witness into a larger output graph. To obtain the specific noncommutation example, separately prove that the starting H-membership partition is globally substitution-stable; then S(E0)=E0, while C(E0)'s singleton restriction can fail an actual unary graft. This is enough to prove `S C(E0) != C S(E0)` without asserting a global multiarity formula for C at later stages.

## 6. Scope of the model comparison

Guarded label schemata, the selected all-profile optimum, structural commutation criteria, stabilization bounds, monoid calculations and the scoped modular I1 comparison are supplied in the separate supporting proofs. No general finite old-profile normalization theorem is claimed. No scalar-kernel or all-span theorem is replaced or silently strengthened.

## 7. Exact imported dependency pins and limits

1. **Old semantic calculus and presentation.** `prior_math/THEOREM.md`, “A convergent mixed presentation of decorated typed graph cuts,” SHA-256 `2c374fe15406197dfaf7d0bc4769f831477e1420d11df8934fa7bc606c07b2ad`. Section 2 independently defines flat witnesses and substitution for all N, finite K and finite COMMUTATIVE old scalar M, with full profiles and unbounded arity/depth. Section 3 gives the finite signature and seven rules. Sections 4–6 prove termination, explicit normal forms, confluence and `s E t iff eval(s)=eval(t)`; §8 states the fibrewise calculus isomorphism and the conditional B2 tuple-category transfer. We specialize old M to {1}. Its §8 expressly does NOT by itself establish B3 raw-refinement completion. Our new D generators, diagonal relations and normal forms are proved in §§1–2 above; they are not covered by the old seven-rule proof.

2. **Old presented refinement comparison, when retained common-spine certificates use it.** `prior_math/Completion_Comparison.md`, SHA-256 `27f4754cf81822034b0fd4f2268af75075e28de2110b66c6c53b0b6db37e6e1d`. Its §1 freezes the exact graph/finite-K/commutative-scalar signature with no profile/depth/history bound. Theorem 3.2 establishes ordinary path coherence for its specified equation subcategory; §§4–5 construct the mixed comparisons; Theorem 6.2 identifies equality of its mixed paths with equality of the complete normal occurrence-forest tuples. A normal entry retains its own frontier, partition, grade path and scalar; equal total composites are explicitly insufficient. We import this ONLY for the already-existing common graph-spine certificate, not for arbitrary new D or mixed-channel proof paths. New coefficient-forest normalization is proved here and in `modular_repair_theorem.md` §9.

3. **Old full refinement tuples and elementary parameter transport.** `prior_math/Semantics_Transport_Factorization.md`, SHA-256 `dbbf64f3c2cb49301d03df01ed5cddca2b8dcbad3efe8a701d2f5f852f462c84`. Section 2.2 identifies old homs as the disjoint union over actual admissible ordered runs of scalar tuples satisfying the composite equation; §2.3 gives entrywise composition; §4 proves strict parameter maps on full witness/Ref tuples; §5 supplies coherent normal-section comparisons. These are the retained old occurrence/parameter facts. They do not provide arbitrary descent, virtual equipment, or new correlated coefficient-cut claims.

These are mathematical dependency scopes, not retrospective changes to historical acceptance. The I5 result remains relative to these supplied old theorems. The new coefficient presentation and retained-forest comparison are independently checkable arguments above and in the modular artifact.
