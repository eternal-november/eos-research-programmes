# Addendum: simultaneous linear interface sharing versus existing realization theory

28 October 2026. Target audited: finite shift-invariant subspaces `W_S` of observable source-history functionals, inferred from Hankel residual maps, are to be implemented by physical registers shared across crossing regions. Each interface has exactly its own registers; no hidden central decoder or free extra storage is permitted.

## Immediate verdict

1. **Common adapted basis iff generated subspace lattice is distributive is classical**, not a new crossing theorem.
2. **If every W_S is invariant, an adapted basis already gives sharing-compatible linear updates.** Invariant complements are unnecessary for ordinary local register sharing. Requiring them silently strengthens “local dynamics” to independent dynamics of ownership atoms.
3. The meaningful unproved step is learning a well-conditioned, correctly typed simultaneous realization from noisy predictive data, with genuine locality/initialization constraints and quantitative witness/error guarantees. Alternatively, permit coded/redundant registers and solve a materially different resource optimization problem, for which network coding is the stronger baseline.

## 1. Exact static theorem and primary comparator

Polishchuk–Positselski, *Quadratic Algebras* (2005), Chapter 1 §7 Proposition 7.1, states equivalence of distributivity of a finite subspace family, a direct-sum decomposition adapted to that family, and a common basis whose subsets span the family. [Author's book record](https://users.math.cas.cz/~positselski/), [publisher](https://bookstore.ams.org/ulect-37). The proposition's text is indexed online; independent [university notes](https://www.math.uni-bielefeld.de/birep/activities/topics/files/ws05-hille-koszul-algebras-and-distributive-lattices.pdf) state the same result and cite Grätzer, *Lattice Theory* (1971), §2.7 Theorem 19. These are references for priority, not a claim of new attribution to the 2005 book.

A primary modern generalization is Burgos Gil–Mallick, *Multifiltrations*, Theorem 3.40: for finite-dimensional E and their finitely generated ordered-group/strict-generating-cone setting, exhaustive separated regular multifiltrations are precisely those induced by a noncanonical multigrading. Their examples also show that induced subobjects/quotients need not preserve regularity automatically. [Primary paper](https://arxiv.org/pdf/1808.10162).

### Elementary proof outline specialized to this project

Let V be the sum of the finitely many W_S. If they are coordinate subspaces for one basis, every sum/intersection is coordinate, so the generated lattice is distributive. Conversely, a finitely generated distributive lattice is finite. For each nonzero join-irreducible subspace J choose a linear complement E_J of its unique lower cover J_- in J. Order the join-irreducibles compatibly with inclusion. Distributivity gives

`J ∩ (sum of earlier incomparable/lower join-irreducibles) = J_-`

when earlier join-irreducibles below J have already been included. Thus the E_J form a direct sum; each lattice element X is the sum of E_J for J≤X. Bases for the E_J give the adapted basis. This construction is purely linear algebra/lattice theory.

**Pairwise checks are insufficient.** Three distinct lines `<e1>`, `<e2>`, `<e1+e2>` in a two-dimensional space are pairwise disjoint and every pair can be simultaneously coordinated, yet all three cannot be subsets of a single basis. The distributivity defect is

`<e1+e2> ∩ (<e1>+<e2>) != (<e1+e2>∩<e1>)+(<e1+e2>∩<e2>)`.

A nonzero vector in the quotient of the left side by the right is a finite algebraic crossing certificate. Giving that certificate a physical/predictive meaning is an additional task.

## 2. Dynamics: when module extensions matter, and when they do not

Let D_a:V→V be every relevant linear shift, with D_a W_S⊆W_S. Let B be an adapted basis and `I(b)={S:b∈W_S}`. Define

`U_b = intersection over S∈I(b) of W_S`.

Because intersections of invariant subspaces are invariant, D_a b∈U_b. Since the basis is adapted, U_b is spanned by exactly the basis vectors available to every interface containing b. Consequently the update of the shared register `z_b(h)=b(h)` uses only registers jointly available to its users. There is no extra invariant-complement requirement. Equivalently, coefficients from b to c can be nonzero only if `I(b)⊆I(c)`.

**This is a direct corollary, not the ambitious missing theorem.** It covers abstract linear state evolution with common accessible update labels. It does not ensure that the physical site owning the shared register observes the required action/observation symbol, has permitted input access, or can initialize it from its local history. Those must be checked separately. Also distinguish unnormalized linear predictive updates from normalized PSR filtering, whose common likelihood denominator can itself create a forbidden global dependency.

### Actual nonsplit extension example

Let V have basis e1,e2, W=<e1>, and D e1=0, D e2=e1. The chain `0⊂W⊂V` is distributive and admits an adapted basis. There is no D-invariant one-dimensional complement to W: every complement is `<e2+c e1>`, whose image is e1, outside that line. Thus the exact sequence of modules over the algebra generated by D does not split.

Nevertheless the shared-register implementation is valid: `z1'=0`, `z2'=z1`. The smaller interface accesses z1; the larger accesses z1,z2. Its private register legitimately depends on shared memory. A module splitting obstruction becomes relevant only if private and shared atoms must evolve autonomously, if prescribed wiring forbids the shared-to-private edge, or if separate owners cannot access the required update symbols. State that extra requirement before invoking Ext/module machinery.

## 3. Physical typing is stronger than an abstract adapted basis

For fixed region labels with intersections, a register has an allowed physical support R. To demand literally that an interface sees exactly the registers supported inside it, require membership agreement, not just vector-space dimensions:

`b∈W_S iff R(b)⊆S`.

An adapted basis gives a membership pattern I(b); it does not automatically show that this pattern equals `{S:R⊆S}` for an allowed physical region R. If all intersections are present and each shared functional must be physically available at overlap, require at least `W_A∩W_B = W_(A∩B)` under the intended exact-access semantics. An arbitrary nonzero functional in an intersection is not automatically an overlap-local observable. Its computation may use remote measurements even if two predictors happen to use it.

If the family includes all unions as well and “no synergistic register at union” is intended, `W_(A∪B)=W_A+W_B` is another condition; it is not implied by intersection compatibility and should not be imposed inadvertently. Cross-region-only registers are a valid design choice in other semantics.

Local input availability, typed support and initialization can therefore add genuine constraints after distributivity. But proving them by enumerating all supports and solving matrix equations is still the generic baseline unless a structural or quantitative gain is obtained.

## 4. Structured state-space realization: closest systems comparators

**Lessard–Kristalny–Rantzer (2012/2013).** They distinguish a transfer matrix with a prescribed sparsity pattern from a stabilizable/detectable state-space realization carrying that structure, and exhibit failure of the implication. Their graph is supplied; this is not noisy architecture discovery. Their precise control theorems have graph and continuous-time hypotheses, so they cannot be transplanted to arbitrary action-dependent predictive shifts. [Primary paper](https://arxiv.org/pdf/1212.1839).

**Rantzer (2018/2019).** Network realizability explicitly attaches local states/inputs/outputs to graph nodes and imposes sparsity on realization matrices. Theorem 1 supplies closure properties with necessary stability qualifications; Theorem 2 relates network realizability of controllers and closed-loop maps. This already converts suitable global input/output specifications into locally implementable state dynamics; it is not simply “centralized prediction.” State-count optimization remains distinct. [Primary paper](https://arxiv.org/pdf/1812.07748).

**Du–Li (2026), important current comparator.** *Realizations of Linear Systems with Prescribed Sparsity Patterns*, v2 dated 17 September 2026, gives a polynomial-equation approach using similarity transformations, permutations and elementary additions. The paper explicitly restricts to minimal realizations and assumes a modal realization with nondegenerate eigenvalues; it treats a supplied support pattern. Its Theorem 1/Corollary 3 are therefore not an unrestricted solution to every network realization problem. Still, “learn global linear model, search a sparse realization algebraically” is directly occupied. [Primary paper](https://arxiv.org/pdf/2603.28754).

## 5. Network coding/minrank: essential if coded registers are allowed

Bar-Yossef–Birk–Jayram–Kol characterize optimal linear index-code length by minrank for a known side-information graph. Input is which receiver already knows which source symbols and what it demands, not unknown physical components. But this is precisely the relevant baseline when one wants to transmit linear mixtures rather than uncoded shared coordinates. [Primary paper](https://webee.technion.ac.il/people/zivby/papers/indexing/indexing.full.pdf).

Muralidharan–Rajan connect linear fractional network codes to representable discrete polymatroids, allowing different source-message and edge dimensions. This covers nontrivial simultaneous subspace dependency and communication-budget optimization on a given network. [Primary paper](https://arxiv.org/pdf/1304.0355).

**Consequences:** distributivity is necessary only for the strict global-basis/subset-storage semantics. With redundant storage, the three-line example can store e1, e2 and e1+e2 at separate sites; there are three physical scalar registers but linear span dimension two. With coded messages and receiver side information, further savings may arise. Such implementations are excluded by a nonredundant common-basis requirement, not ruled out by physics. Name which resource is counted: independent dimension, actual scalar registers, finite-field symbols, bits, or communication per step.

Shared randomness must also be charged or conditioned on for probabilistic rank lower bounds. A full-rank stochastic input/output channel can be simulated by mixtures of lower-message-cardinality channels indexed by a shared seed. Hence a marginal noisy-channel rank alone need not lower-bound message cardinality.

## 6. What substantive theorem remains?

### Exact fixed-W result: useful integration, modest novelty

A precise theorem can combine adapted-basis existence, allowed support-pattern realizability, local action access, local initialization, and register-count optimality under **nonredundant linear coordinate sharing**. A proof should compile a realization or return (a) a distributivity-defect vector, (b) an unrealizable incidence pattern, or (c) a local-input/initialization counterexample. This is a useful rigorously typed assembly of established ingredients; do not advertise its linear-algebra core as new.

### Stronger target: robust simultaneous discovery and certification

A defensible new target would start with estimated Hankel blocks and inferred interface candidates, not exact W_S. Under explicitly testable singular-value/angle margins and action coverage, prove an algorithm that jointly selects the components, reconstructs a nearby exactly realizable typed arrangement, and outputs either:

- persistent local registers with quantified memory, condition number, local update errors and finite-horizon (or stability-controlled infinite-horizon) prediction bounds; or
- a finite receiver-conditioned history/test certificate whose probability gap excludes **every** realization in the declared budget class, not just a supplied coordinate candidate.

The genuinely difficult step is simultaneous recovery of intersection/sum incidence and admissible shift dynamics under perturbation. Exact intersection dimensions are discontinuous: an arbitrarily small rotation can erase an intersection. A generic noisy matrix never lies exactly on the desired distributive incidence stratum. Rank recovery alone is therefore insufficient; one needs a margin/stratum-identifiability model and a joint projection/certification theorem rather than thresholding each pair independently.

A further substantive theorem could bound the minimum redundant or coded register overhead when distributivity fails and relate that overhead to persistent, receiver-conditioned observable witnesses. That goes beyond the adapted-basis theorem, but must be compared to subspace arrangements, index coding and structured realization—not merely to Hankel rank. No general overhead formula or robust theorem is established in this addendum.

**Recommended first claim:** exact typed nonredundant realization is a classical simultaneous-splitting corollary with operational qualifications. The ambitious research claim is robust discovery or an explicit persistent coding-overhead theorem. Do not manufacture a module-extension obstruction where triangular local coupling is allowed.
