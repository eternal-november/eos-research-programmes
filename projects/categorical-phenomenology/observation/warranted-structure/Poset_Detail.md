# Alternative: when does observation warrant a new universal operation?

## Recommendation and novelty verdict

Use **finite certification of an emergent universal operation under changes in admissibility** as a falsification benchmark. Do not promote it yet as a new theory. The cleanest test case has exact proofs, genuinely noninvertible comparisons, and no assumed factorization: an observed binary comparison relation may support a newly derived meet operation. The operation is not supplied to the learner and its existence is not promised.

The sharp result is that domain openness, not merely the number of observed comparisons, controls what can be certified. Under arbitrary order-embedded extensions, a meet of two named elements is stable exactly in the comparable case. For an incomparable pair, additional unseen elements can change the meet or supply one that did not exist. With an exhaustively known finite domain, the same primitive comparison experiments decide existence and recover the operation. A concrete finite family makes the certification cost almost quadratic.

This separates ideal determination, admissible definability, and finite certification. It does **not** by itself escape standard model theory, learning theory, or database theory. A publishable generalization needs a theorem about restricted experiments and categorical universal structure that is not just a preservation theorem or a query-complexity result with renamed objects.

## 1. Three levels that must stay separate

1. **Finite evidence:** a finite transcript of individual, exact yes/no comparison queries involving named tokens.
2. **Ideal observations:** the complete binary comparison relation on the actual domain. This determines whether a specified greatest lower bound exists, even if no finite procedure can certify that determination.
3. **Admissible experiments:** which tokens can be named, which comparisons can be queried, whether a finite domain is known to be exhaustive, and what form of experiment can reveal a new token.

There is no primitive query of the form “is this a meet?”, “have all possible lower bounds been found?”, or “are these systems equivalent?”. No total-law oracle or supplied factorization is used.

The model is noiseless. Moving to noisy experiments would require a separate statistical theorem and should not be concealed by the idealization.

## 2. Exact non-oracle probe models

### Open-domain model

The investigator has finitely many named tokens at every finite time. An admissible probe `compare(x,y)` returns whether x is below y. New tokens can be introduced over time. For a countable exposable domain, one could additionally assume that every actual token and every comparison are eventually exposed, but no result below needs that assumption. There is no finite termination signal asserting that all tokens have appeared.

A finite transcript permits every poset containing the observed induced order, including extensions with additional elements. Even giving the investigator **all** pairwise comparisons on the currently named tokens does not close the domain.

Sound certification means that the claim is true in every compatible world. It is deliberately stronger than a conjecture that may later be retracted, and stronger than eventual identification in the limit.

### Closed finite-domain model

The investigator is given an exhaustive list of N token IDs and the same individual comparison probe. Exhaustiveness is an explicit input assumption, not something inferred from a long stretch without new observations. The algorithm can query all N² ordered pairs, check that the relation is a partial order, and decide which binary meets exist.

If all binary meets exist, the algorithm derives the whole table m(x,y). Commutativity, associativity, and idempotence follow from the greatest-lower-bound characterization. Thus a semilattice algebra is recovered without access to an algebra-operation query and without a promise that the input has such an algebra. In the associated thin category these are binary products.

This is genuine derivation of an additional operation from a relation, but it is a **calibration example**, not a claim that arbitrary categorical structure has emerged from uninterpreted data. The interpretation of comparison as order and the choice to regard a poset as a thin category remain explicit semantic commitments. One can verify the order laws in the closed finite case; they cannot be justified for an open domain from finite samples alone.

## 3. A sharp extension-stability theorem

**Proposition.** Let P be a poset and let m be the meet of a and b in P. The equation m = a ∧ b is preserved by every order embedding of P into a larger poset if and only if a and b are comparable.

**Proof, comparable direction.** If a ≤ b, then the meet is a in every poset containing that comparison. Every common lower bound of a and b is below a by definition. The dual comparable case is identical. This is important: open-domain finite evidence can certify such meets. A blanket claim that it cannot certify even one meet would be false.

**Proof, incomparable direction.** Suppose a and b are incomparable. Add a new element w to P. Keep all old comparisons unchanged, set x ≤ w exactly when x ≤ m for old x, and set w ≤ y exactly when a ≤ y or b ≤ y for old y. Add reflexivity at w. These clauses give a partial order: any newly composable old-to-w-to-old path already existed in P, because x ≤ m ≤ a ≤ y or x ≤ m ≤ b ≤ y. No old-old comparison is created. There is no cycle through w because that would force a ≤ m or b ≤ m, contradicting incomparability.

The inclusion P → P ∪ {w} is therefore an order embedding, hence a fully faithful but noninvertible functor between thin categories. Every old common lower bound of a and b lies below m and hence below w. The new meet is w, not m. The old meet equation is not preserved. ∎

**Corollary for finite evidence.** If the admissible worlds remain closed under such extensions, no finite transcript soundly certifies a named meet for an incomparable pair. This remains true even when the complete order on all currently named elements has been observed, including all negative comparisons.

This is not a limit-inference impossibility: a learner may make revisable conjectures. Nor is it an impossibility when an application supplies an independently justified closure principle. It is a failure of finite **sound certification** under the stated extension policy.

## 4. Explicit indistinguishable worlds

Let A have three elements z,a,b and just z<a and z<b, with a and b incomparable. Its meet a∧b is z.

* B adds w with z<w<a and z<w<b. Then a∧b=w.
* C instead adds w below both a and b but incomparable with z. Then a and b have no meet.

All comparisons involving only z,a,b, positive or negative, have exactly the same answers in A, B, and C. The inclusions of A are order embeddings. The example therefore does not rely on invertible comparisons, measurement noise, or erasing previously observed facts.

Conversely, an arbitrary poset with incomparable a,b can be extended to give them a new meet: put a fresh w above every old common lower bound and below a,b and their upper bounds. The same transitivity check preserves the old induced order. Thus an open finite transcript cannot certify absence of a meet for such a pair either, unless restrictions on future extensions are supplied.

These examples show why “the structure emerging as we observe more” need not mean a simple refinement of an old operation. Additional objects can replace a previously reconstructed product or destroy its existence while preserving every old relation. The finite order relation itself has not been contradicted; the universal quantification domain has changed.

## 5. A nontrivial positive construction with exact probe costs

The exhaustive-domain assumption makes recovery possible, but not automatically cheap. Consider a domain consisting of a bottom element 0, n named lower elements L, and n named upper elements U. The only unknown strict comparisons are l<u for l in L and u in U. All other comparisons are fixed: 0 is below everything, elements within each level are incomparable, and there are no other strict comparisons.

Each possible unknown comparison is one independent yes/no probe. Let G be the resulting bipartite graph between L and U.

**Proposition.** This poset has all binary meets if and only if G has no four-cycle.

**Proof.** Two distinct upper elements have as nonzero common lower bounds exactly their common neighbors in L. Their meet exists exactly when they have at most one common neighbor: it is 0 if there is none and the unique neighbor if there is one. Two distinct common neighbors are incomparable and give no greatest one. Such a pair of common neighbors is exactly a four-cycle. Every other pair has an immediate meet: either 0, or the smaller comparable element. ∎

An algorithm queries the n² unknown comparisons, checks that no two upper vertices share two lower neighbors, and, if successful, constructs the entire meet operation. It never asks an operation or universal-property oracle.

Let z(n,n;2,2) be the maximum number of edges in a four-cycle-free bipartite graph with n vertices on each side. On the empty-graph input, the minimum size of a sound certificate that all binary meets exist is exactly

    n² − z(n,n;2,2)

negative comparison observations, if the certificate need only establish existence and not reconstruct the whole table. This is an exact combinatorial characterization of minimum certificate size, not a claim that extremal certificates can be constructed efficiently for every n.

**Proof.** After some negative answers, every unqueried edge remains free to be present. Certification succeeds exactly when the graph of unqueried edges is four-cycle-free. Otherwise the four edges of an unqueried cycle can be present in an indistinguishable completion without all binary meets. Conversely, if the unqueried graph is four-cycle-free, every compatible subgraph is too. Maximize the number of unqueried edges to minimize the certificate. ∎

The classical extremal bound z(n,n;2,2)=O(n^(3/2)) therefore gives a near-quadratic lower bound even on this input where every probed comparison is false. An elementary proof counts pairs of neighbors and applies convexity; no new extremal theorem is being claimed. The relevant literature is the Zarankiewicz problem; see [Damásdi, Héger, and Szőnyi, Section 3](https://real.mtak.hu/13977/1/DHSzFIN.pdf).

If the task is to recover the actual entire meet table whenever it exists, rather than merely certify existence, all n² comparisons are necessary on the empty graph. Any unqueried edge could alone be present; this alternative still has all binary meets but changes the meet of its endpoints from 0 to the lower endpoint.

This is a concrete separation between a structure being uniquely determined by complete finite evidence and its being cheaply certifiable from sparse evidence. It is also an explicit reminder that a structure-formation claim can reduce to ordinary graph-query complexity.

## 6. The research target worth testing

**Candidate target, not an established new theorem:** characterize finite certificates for universal constructions under a specified family of permitted domain extensions and primitive experiments, with a sharp cost bound in at least one non-thin categorical case.

The target should state in advance:

* what the raw data and individual experiments are;
* what permits new entities, arrows, or compositions to become admissible;
* which semantic commitments are assumed, rather than empirically derived;
* whether success means ideal determination, an executable definition, a finite sound certificate, or revisable convergence;
* which noninvertible comparison maps must preserve the recovered structure;
* an indistinguishable pair showing the necessity of every closure assumption used for finite certification.

A credible first extension would concern a universal construction with genuinely multiple arrows and a uniqueness-of-factorization condition. Do not begin by assuming factorization witnesses or a factorization functor. The experiment interface must expose individual compositional observations; the existence and uniqueness claims are the output to be tested. The old example supplies a failure mode the general result must explain, not an application to prioritize.

**Pass criterion:** a new theorem links operational restrictions on possible probes/extensions to which universal structure can be soundly recovered, and proves something not obtained by translating a standard definability, preservation, certain-answer, or graph-query result. It should produce an experimentally distinguishable success/failure boundary, not simply a category of all compatible hypotheses.

**Kill criterion:** if the claim amounts to learning a fixed-signature structure, testing a first-order sentence under ordinary membership queries, forming certain answers across completions, or applying Beth/preservation unchanged, stop presenting it as a new foundation. Those may be useful tools, but their categorical packaging is not the contribution.

## 7. Prior-art risks that must be confronted

1. **Learning algebraic structures.** Learning a category or algebra with unknown operation tables and unknown isomorphism type is not automatically outside established learning theory. Nikolay Bazhenov, Ekaterina Fokina, and Luca San Mauro study learning isomorphism types from finite pieces of structured data and give a model-theoretic characterization. The signature is fixed, but much of what might be called “structure discovery” already occurs there. [Learning families of algebraic structures from informant](https://doi.org/10.1016/j.ic.2020.104590); [author preprint](https://arxiv.org/abs/1905.01601).

2. **Beth definability.** In ordinary first-order logic, unique implicit determination of a new relation across models of a theory already implies an explicit formula in the observational language. A general claim that ideal observations uniquely determine extra operations risks being this theorem. This does not automatically provide a finite experimental protocol or a definition in a restricted admissible fragment. [Open Logic Project, definability theorem](https://builds.openlogicproject.org/content/model-theory/interpolation/definability.pdf).

3. **Preservation theory.** Relating the form of definable structure to its preservation under noninvertible maps is classical. Rossman proves the homomorphism preservation theorem over finite structures. Its hypotheses must not be silently transferred to arbitrary restricted classes of worlds: preservation theorems may fail on subclasses. [Homomorphism preservation theorems](https://doi.org/10.1145/1379759.1379763).

4. **Incomplete databases and certain answers.** “Warranted by every world compatible with finite observations” is already the central semantics of certain answers. Open- versus closed-domain effects and completeness assumptions are not new merely because the query concerns a product or meet. Libkin also warns that taking the raw intersection of answers can lose structural information, and studies representing answers as objects or knowledge. [Certain answers as objects and knowledge](https://doi.org/10.1016/j.artint.2015.11.004).

5. **Query and extremal complexity.** The finite positive example reduces directly to detecting four-cycles in a bipartite graph. Its categorical interpretation is useful for policing assumptions, but its lower bound is classical combinatorics rather than evidence of a new mathematical field.

## Assessment

The strongest immediate outcome is a precise, corrected impossibility boundary and an exact positive benchmark. This does not yet establish a research gap. It improves the program by forcing three distinct claims apart: the world has a structure, ideal observations determine it, and permitted finite experiments can warrant it. A candidate that conflates them should fail the next gate.
