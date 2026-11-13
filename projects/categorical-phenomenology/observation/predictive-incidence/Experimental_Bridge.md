# A comparative-generative test: additional experiments for predictive and incidence structures

## Result and status

The strongest concrete candidate here is an **acquisition separation from the same incomplete data**. An initial table distinguishes n exhaustive behavioral states by threshold readouts, but leaves an intervention completely unknown. With additional binary threshold queries, one can either certify that every future experiment stays inside the old incidence closure or generate a specific new test whose extent lies outside it, in O(n) queries. Reconstructing an arbitrary predictive transition table needs Ω(n log n) binary queries. The incidence decision has an Ω(n) lower bound, and a constant-map instance has an exact certificate size 2n−2. A separate positive transcript uses 3k−2 probes at n=2k to certify all-future incidence stability while leaving 2^k distinct predictors possible; exactly k additional bits identify which predictor is actual.

This is not a novelty claim. The mechanism reduces to preservation of upper sets by monotone maps, threshold-query search, and classical finite information bounds. The predictive-to-incidence bridge itself is elementary inverse-image duality, not a newly discovered comparison. The useful additional content over the previous note is a stated task, genuinely unknown transition, executable adaptive experiment policy, cost comparison, and independent ambiguity controls. Whether this packaged acquisition problem leaves a source-distinct theorem-sized residual remains unestablished.

## 1. A general exact law for adding one observational test

Let H be a finite set of observed preparation histories and E a finite set of tests. The actual data are the complete finite rectangle I:H×E→{0,1}. For e∈E write A_e={h:I(h,e)=1}. Two constructions use this same table:

1. The **finite-test predictive profiles** Q_E identify equal rows. These are not yet complete predictive states unless a separate adequacy argument is available.
2. The positive incidence closure C_E consists of all intersections of the A_e, including H as the empty intersection.

Suppose an additional test z has fully measured extent A⊆H. Let s(A) be the number of old row classes meeting both A and H\A.

**Proposition 1.**

- The number of row classes increases by exactly s(A).
- C_{E∪{z}} = C_E ∪ {C∩A:C∈C_E}.
- At least s(A) new closed extents are added, and at most |C_E|.
- The profile partition is unchanged iff A is a union of old row classes, equivalently Boolean-definable from the old finite test columns.
- The incidence closure is unchanged iff A∈C_E, equivalently definable as a conjunction of old positive test columns.

**Proof.** A new binary coordinate either leaves an old row class intact or splits it in two. Each intersection in the enlarged vocabulary either omits A or includes it, proving the update formula and the upper bound. For each split old class B, choose x∈B∩A. Its new singleton closure is cl_E({x})∩A. This is not old-closed, since it contains x but omits a member of the same old row class. Distinct split classes give distinct new singleton closures: equal closures would make their chosen points agree on all old attributes and hence belong to the same old class. Finite Boolean combinations generate exactly the unions of row classes, while intersections generate C_E. □

Thus incidence enrichment need not split predictive profiles. This is not evidence that a completely known predictor gained information: unchanged row partition is weaker than unchanged transition knowledge or unchanged future predictions. Nor is a newly defined column one binary experiment: obtaining its whole extent can require |H| separate reset-and-prepare runs.

### A consequence from a partially measured, genuinely unknown column

Let P and N be the histories so far measured positive and negative for z, respectively, with P∩N=∅. The remaining cells are unknown. Suppose for this local statement that all column completions A with P⊆A⊆H\N remain allowed.

**Proposition 2.** A conjunctively redundant completion exists iff cl_E(P)∩N=∅.

**Proof.** Every closed completion containing P contains its closure. Conversely, if the closure avoids N, that closure itself is an allowed closed completion. □

Consequently, when h∈cl_E(P) is unmeasured and its z-run is admissible, querying it tests a concrete consequence of the **redundancy hypothesis**. A negative result certifies incidence novelty before the whole new column is known. This is not an unconditional prediction that the result must be positive. An old row-class split is already witnessed exactly when one old class meets both P and N.

There is also an exact criterion for redundancy being certain, rather than merely possible. Put U=H\N. Every completion in [P,U] is closed iff U and every U\{u} for u∈U\P belong to C_E. Necessity is immediate. For sufficiency, every intermediate subset is an intersection of these sets. This may certify redundancy without filling every cell when the old closure is sufficiently rich.

These are elementary closure-system facts and the dual of familiar partial-description feasibility in attribute exploration. They do not by themselves supply a new active-learning theory. With no restrictions on unqueried columns, no policy can guarantee that an as-yet-unmeasured candidate will enrich incidence structure: it may be the constant-1 column H. Current evidence can make a query diagnostic, not determine the favorable outcome.

## 2. The predictive/incidence criterion behind the acquisition problem

Let Q be a certified finite behavioral state set, let δ_a:Q→Q be its deterministic intervention maps, and let retained tests have supports A_e. Write C for their intersection closure. For a word w followed by test e, its support is δ_w^{-1}(A_e).

**Proposition 3 (finite generator criterion).** Every ideal future test support lies in C iff δ_a^{-1}(A_e)∈C for every intervention letter a and retained test e.

**Proof.** Necessity uses the one-letter futures. For sufficiency, inverse images preserve intersections, so the criterion makes every δ_a^{-1} preserve C. Induction on word length gives all future supports. □

This is a directed comparison, not an invertible identification of carriers: the predictor has states and transitions; C has positive observable extents and inverse-image operations when the criterion holds. Its formal intersections need not be realizable states or physically executable joint preparations. “No incidence enlargement” throughout means no new closed extents (and hence no change to their inclusion lattice), not that the labelled formal context gains no new test names or that all old and new labels are identified.

If δ is already completely certified, this is model-derived experiment design. A failed criterion yields a missing literal incidence attribute, but its outcome is already predicted within that model class. Executing it adds direct evidence or validates the assumptions, not new model-relative behavioral information. Breadth-first subset search can find a shortest missing word when needed, but has up to 2^{|Q|} supports to visit; arbitrary access restrictions require constrained search. The next construction avoids assuming the unknown transition is already learned.

## 3. A genuinely incomplete threshold experiment

Fix n≥2. The interface has **independent preparation procedures** h_1,…,h_n and **independent terminal tests** z_1,…,z_{n+1}. They are not silently unary histories a^i or suffixes involving the unknown intervention a. Otherwise their syntactic relationships would already constrain that intervention.

The actual initial table is

I(h_i,z_j)=1 iff i≥j.

Assume deterministic stationary behavior, reliable preparations/readouts, and a valid bound of n on the full future-relevant observable state space across these preparations. The n distinct observed rows then exhaust the behavioral states; identify them with Q=[n]. This proves exhaustion relative to a capacity promise, rather than inferring it from a fitted table. The tests z_1 and z_{n+1} are respectively constant 1 and 0 on all states.

A single intervention a is wholly unknown. Its transition δ:[n]→[n] may be **any** function. Every one of the n^n functions has an n-state realization with exactly the recorded calibration table. Neither monotonicity nor any transition value is assumed.

- **Actual evidence:** the calibration rectangle and the specific additional queries already answered.
- **Currently admissible additional experiments:** every one-step run (h_i,a,z_j), for 2≤j≤n, giving the bit 1[δ(i)≥j]. Constants need not be queried.
- **Ideal experiments:** all (h_i,a^k,z_j), k≥0. Higher-k experiments need not currently be admissible.

The initial incidence closure is the chain C={U_j:1≤j≤n+1}, where U_j={j,…,n} and U_{n+1}=∅. The predictive carrier is already exhausted, but its dynamics and future answers are not yet known.

### The exact bridge law

**Theorem 4.** The following are equivalent:

1. Every ideal future support {i:δ^k(i)≥j} belongs to the old C.
2. Every one-step support {i:δ(i)≥j} belongs to C.
3. δ is nondecreasing.

If δ(i)>δ(i+1), the generated test a z_{δ(i)} has a support containing i but not i+1, so lies outside C. The two associated binary runs certify its incidence novelty without measuring the whole column.

**Proof.** (1) implies (2). If δ is nondecreasing, so is every iterate, and each threshold preimage is an upper tail, proving (3) implies (1). If δ is not nondecreasing, an adjacent descent exists. The stated threshold produces a set that is not an upper tail, contradicting (2). □

This theorem transfers an independently testable property of an unknown predictive transition into a generative statement about every future observable. It does not merely rename a complete incidence table.

## 4. An adaptive policy and its exact scope

**Theorem 5.** From the calibration data alone, there is an adaptive policy using at most 3n−2 additional primitive queries that returns either:

- a sound certificate, over all n^n initially compatible transitions, that no ideal future experiment enlarges C; or
- an explicit one-step test and two measured runs proving that its extent enlarges C.

**Policy and proof.** Process i=1,…,n and maintain v, initially 1. For i>1, v is the exact previously learned δ(i−1). If v>1, query whether δ(i)≥v. If the answer is 0, stop: the previous row has a measured or otherwise already known positive answer at threshold v, and the present row a negative answer. These give the witness in Theorem 4. If v=1, this guard is known true without a query.

After a successful guard, query δ(i)≥v+1, δ(i)≥v+2, and so on, increasing v on each positive response, until the first negative response or v=n. At that point δ(i)=v exactly. Continue.

If no guard fails, every value has been learned and the sequence is nondecreasing. The transcript itself certifies these facts for every compatible transition. Across the entire run there are at most n−1 positive threshold increases, n terminating negative answers, and n−1 guards. The total is at most 3n−2. Every selected query is one of the declared currently admissible runs. □

**Important accepting-run caveat.** This particular policy identifies the entire predictive transition on every accepting run. It does not prove that a good incidence answer always leaves a difficult predictor unknown. The cost separation below compares the worst-case property-or-witness task over arbitrary maps with worst-case identification of arbitrary maps. The property policy can abort on a negative instance without learning the rest of the transition.

The costs are **additional-query** costs after the shared calibration data. Obtaining a literal calibration rectangle from scratch can itself take Θ(n²) binary measurements; it is not hidden inside the O(n) claim.

### Positive certification with exponentially many predictors still possible

Let n=2k, k≥1. Obtain the following answers:

- For 1≤i≤k, certify 2i−1≤δ(i)≤2i. The lower bound at i=1 and the upper bound at i=k are automatic boundary facts; each of the other lower and upper bounds takes one threshold query.
- For k<i≤2k, query δ(i)≥n and obtain 1, fixing δ(i)=n.

This costs (k−1)+(k−1)+k=3k−2 primitive queries. For example, the actual transition δ(i)=2i−1 for i≤k and δ(i)=n afterward produces exactly these answers. The compatible transitions have independent two-point choices δ(i)∈{2i−1,2i} in the first k positions, followed by constant n. Every such transition is nondecreasing because the successive permitted intervals are ordered. Theorem 4 therefore warrants that **no ideal future test enlarges the existing incidence closure**, even though **2^k distinct predictive transitions remain compatible with the same actual evidence**.

The query δ(i)≥2i resolves the remaining bit at each i≤k. Exactly k further binary observations are required in the worst case to identify the predictor, by counting the 2^k candidates, and these k one-step queries attain that bound. Their answers genuinely vary across the compatible models. No equivalence oracle or already learned transition was used to obtain the structural certificate.

What has been certified is the collection of possible positive extents: every future test denotes some old upper tail. Which upper tail a named future experiment denotes is still unknown. Thus the result does not conflate incidence-carrier stability with equality of labelled predictive dynamics or with absence of useful future measurements. It supplies a concrete positive example beyond the scanning algorithm's accepting-run behavior, while still reducing to interval order and threshold querying.

### An exact partial-transcript certificate and lower bound

Any valid threshold transcript gives an interval [L_i,U_i] of possible values for each δ(i); the choices for different i remain independent.

**Proposition 6.** Every compatible transition is nondecreasing iff

U_i≤L_{i+1} for every i<n.

Some compatible transition is nondecreasing iff L_i≤U_j for every i<j (and the intervals themselves are nonempty).

**Proof.** The universal condition is sufficient by bounding arbitrary adjacent choices; if it fails, choose δ(i)=U_i and δ(i+1)=L_{i+1} to create a descent. For existence, the least nondecreasing candidate is δ(j)=max_{i≤j}L_i; it is feasible exactly when it does not exceed U_j. □

This allows meaningful decisions from incomplete transition information rather than only from a reconstructed model.

On the constant actual transition δ(i)=c, where n≥3 and 1<c<n, all intervals contain c. The universal criterion therefore forces U_i=c for every i<n and L_i=c for every i>1. Setting U_i=c requires the negative threshold answer at c+1; setting L_i=c requires the positive answer at c. Hence **at least 2n−2 queries** are necessary on this input. Those exact queries suffice, so this is its exact certificate size. They may leave δ(1) anywhere in [1,c] and δ(n) anywhere in [c,n], while still certifying monotonicity. Thus incidence stability can, in principle, be certified on a positive instance without reconstructing the complete transition. The certificate is not a free means of discovering the unknown value c.

The incidence decision therefore has Θ(n) worst-case additional query complexity. In contrast, identifying arbitrary δ requires at least ceil(log₂(n^n))=ceil(n log₂ n) binary queries, since the initial data admit all n^n different transition tables. Different tables really differ predictively: a threshold after one action distinguishes their differing entries. Binary search at each preparation gives a matching O(n log n) upper bound. This comparison does not assert a separation on the monotone subclass: promised-monotone maps can themselves be reconstructed with O(n) threshold queries.

## 5. Failures and informative examples

**Unknown-state failure.** Remove the state bound/exhaustion premise. A positive n-state identity transition and a finite hidden-copy system can agree on every calibration and one-step run. In the hidden system, a sends each h_i-state to an observationally identical copy; from that copy a sends it to h_{π(i)}, where π swaps 1 and 2. All one-step columns are old upper tails. But the two-step support for z_2 contains preparation 1 and not preparation 2, so is not an upper tail. The finite one-step criterion was illegitimately applied to an unexhausted state set. No amount of one-step measurement on these preparations repairs that missing premise.

**Access failure.** Even with two exhaustive states, suppose only one-step queries from preparation 1 are currently admissible. The transitions δ_+=(2,2) and δ_-=(2,1) agree on every such query and on calibration. The first preserves the old closure; the second generates a non-upper-tail support. The policy cannot promise its result when the required preparation is inaccessible.

**Profile versus incidence growth.** Let δ be the cycle 1→2→⋯→n→1. The original n distinct profiles already identify the whole carrier. Nevertheless the future supports of z_2 under powers of a are all co-singletons of [n]. Their intersections generate every subset, expanding the incidence closure from n+1 to 2^n extents without adding states. Before δ is learned these tests can teach dynamics; after δ is certified they are representational enrichment or validation, not additional model-relative information. This example does not confuse those stages.

**No guaranteed favorable new column.** In Proposition 2, a negative answer in cl(P) produces a useful counterexample, but all measured answers might instead remain compatible with a closed column. A method that recommends an informative query has not guaranteed the property it hopes to discover.

## 6. Known reductions and the remaining gap

- **Clark, syntactic concept lattice:** the predictive partition and Galois/incidence lattice derived from the same prefix–suffix pairing are already explicit. The previous report's residual-to-intersection bridge is therefore a baseline, not repeated here as a new result. [Paper](https://alexc17.github.io/static/pdfs/JLC2013.pdf).
- **Partial attribute exploration:** the least-closure feasibility test in Proposition 2 is a direct closure-theoretic reduction, dual to realizing partial object descriptions. Our primitive oracle returns one measured cell, whereas an exploration expert may answer an implication or provide a counterexample. That oracle distinction must be maintained but does not make the elementary criterion novel. [Borchmann, A General Form of Attribute Exploration](https://arxiv.org/abs/1202.4824).
- **Coalgebra learning via duality:** logical tests, states, dual adjunctions, and counterexample-driven test refinement already support abstract correct learning algorithms. The current contribution is not a new states/tests duality. Its narrow threshold experiment class replaces equivalence queries with an exhaustive-state capacity premise and one-cell membership measurements. [Barlocco, Kupke, Rot](https://arxiv.org/abs/1902.05762).
- **Residual-automaton learning:** NL* already learns residual nondeterministic automata from membership and equivalence queries, retaining prime residuals rather than every deterministic residual. Thus structure-sensitive observation-table learning is not new. Our threshold task is a much narrower incidence-preservation decision and supplies no generalization or improvement of NL*. [Authors’ publication page](https://fbim.hs-regensburg.de/~kec39902/publication.html). The abstract was inspected; the full paper was not retrieved.
- **Universal automaton learning:** Björklund, Fernau, and Kasprzik learn the canonical universal automaton with a polynomial number of membership and equivalence queries relative to that automaton's size. They already learn a canonical factorization/Galois structure through observation tables. Our task decides preservation of a fixed observed closure or exhibits one missing test; it does not learn the whole universal automaton and has no equivalence oracle. Consequently the O(n) bound is not a speedup over their different learning problem. [Author-hosted paper](https://www.uni-trier.de/fileadmin/fb4/INF/TechReports/ratom2longelsevier.pdf).
- **Threshold-query search:** Damaschke's *Searching for a monotone function by independent threshold queries* uses the same threshold-oracle form under a monotonicity promise. This is particularly close to the accepting branch, which reconstructs the monotone transition. The present unpromised decision/witness wrapper and the constant-map interval certificate should be treated as elementary extensions unless a careful source comparison establishes otherwise. [DOI](https://doi.org/10.1007/BFb0015433). The publisher abstract was inspected and verifies the same oracle and O(n) query claim; no full-text inspection is claimed. [Publisher abstract](https://link.springer.com/chapter/10.1007/BFb0015433).

The substantive positive outcome is a fully specified comparative experimental problem with proofs, a policy, and failure controls, rather than a generic diagram. The source-distinct novelty gap remains: the results currently reduce to classical closure, inverse-image preservation, threshold search, and decision-tree reasoning. No Gate A novelty or broader native-realization conclusion is certified.
