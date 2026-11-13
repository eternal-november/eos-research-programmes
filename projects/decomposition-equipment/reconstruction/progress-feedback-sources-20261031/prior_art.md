# Infinite-state feedback: prior-art and framing audit

2026-10-31. Research audit, not a novelty claim. Read against the cross-doctrine comparison theorem, qualitative-divergence companion, and adequate-CFS span criterion. Scope: semantic/categorical transport and wiring; not acquisition or identification from experimental data.

## Decision

The new target is worthwhile only if it closes the **operational progress / cylinder-reconstruction bridge**. Almost-sure termination certificates, their abstraction, their compositional aggregation, and guarded categorical iteration each have substantial prior art. A theorem saying that a globally decreasing function implies termination is a baseline. So is defining the admitted arrows to be precisely those whose composites terminate.

The existing qualitative result gives a concrete, correctly targeted obstruction: on countably many states, identical open support and local deficit data can have different first-exit deficits. The biased nearest-neighbor walks already show this. Thus the extra interface must retain enough quantitative information about potentially unbounded trajectories. It need not retain an entire implementation or choose canonical physical representatives.

## Verified primary baselines

### 1. Almost-sure termination beyond finite expected runtime

McIver, Morgan, Kaminski and Katoen, *A New Proof Rule for Almost-Sure Termination*, Theorem 4.1, uses an invariant, a nonnegative potentially unbounded variant V positive under the guard, and positive antitone functions p,d of its current value. A completed body step decreases V by at least d(V) with probability at least p(V). The supermartingale condition is formulated using all bounded truncations H⊖V and weakest preexpectations. This formulation matters for partial bodies and demonic choice; do not silently replace it by an informal expectation inequality for an already total body. Their symmetric random walk example terminates almost surely but has infinite expected termination time. Section 6 and Appendix E connect this to Foster's denumerable-chain work.

Primary full text: https://arxiv.org/html/1711.03588 ; https://arxiv.org/abs/1711.03588 .

Consequence for this project: uniform expected decrease, geometric tails, and bounded expected runtime are useful initial certificate classes, but none is equivalent to the requested general a.s. feedback admission. State that restriction explicitly.

### 2. Compositional and lexicographic termination

Agrawal, Chatterjee and Novotný, *Lexicographic Ranking Supermartingales*, establishes sound a.s. termination and compositional reasoning for probabilistic programs with nondeterminism, with additional restrictions needed for expected-time bounds: https://arxiv.org/abs/1709.04037 . This audit checked the primary abstract rather than every theorem's full hypotheses.

Chatterjee et al., *On Lexicographic Proof Rules for Probabilistic Termination*, specifically identifies the earlier requirement that every component be nonnegative everywhere reachable and develops sound relaxations. Probabilistic lexicographic composition cannot simply copy deterministic ranking rules: https://arxiv.org/abs/2108.02188 .

Consequence: aggregation or lexicographic sequencing of progress certificates, by itself, is not the missing research result. A coupled module may increase another module's potential; one must account for those cross-effects or establish a suitable rule, not concatenate certificates.

### 3. Stochastic abstraction plus local small-gain composition

Lavaei, Soudjani and Zamani, *Compositional (In)Finite Abstractions for Large-Scale Interconnected Stochastic Systems*, already combines stochastic simulation functions with compositional abstraction. Verified Theorem 6.2: each subsystem has a finite abstraction and stochastic pseudo-simulation function; cyclic small-gain inequalities hold; the aggregate maximum of rescaled local functions satisfies a concavity condition. Then that aggregate is a stochastic simulation function for the interconnected models. The paper also treats reduced-order infinite abstractions. Its abstraction relation bounds output mismatch, not automatically first-exit termination.

Primary text: https://arxiv.org/html/1808.00893 , especially Assumption 3 and Theorem 6.2; predecessor https://arxiv.org/abs/1709.10312 .

Consequence: “local certificates survive abstraction and combine under wiring” is already an existing substantial theme. The present project's distinction must be a derived relationship to the two-sided cylinder construction and its actual comparison calculus, not merely use of a gain matrix. Remember expectation and maximum do not commute in the desired direction without additional justification; the concavity hypothesis in this baseline is not decorative.

### 4. Guarded trace and restricted uniformity

Goncharov and Schröder, *Guarded Traced Categories*, provides categorical guardedness, its graphical propagation, and guarded trace. Proposition 5.8 equates guarded trace on a co-Cartesian category with guarded Conway iteration. Definition 5.6 separately specifies uniformity relative to a chosen subcategory. Their metric example uses contraction to obtain unique fixed points. Thus a compositional guard discipline and its trace equations are existing machinery; guardedness must still be instantiated by the operational progress inequalities.

Primary text: https://arxiv.org/html/1802.08756 , Definition 5.6 and Proposition 5.8; https://arxiv.org/abs/1802.08756 .

Consequence: the subcategory of arrows along which iteration is uniform is a useful place to expose the operational comparison restriction, rather than silently quantifying over every formal Isbell arrow.

### 5. Reconstruction machinery already available

Garner's free Isbell/CFS construction and its lax/colax morphisms are the existing structural baseline: https://arxiv.org/abs/1410.7108 . The project's earlier native comparison-span and honest-wiring results must not be reintroduced as new termination theorems. They give formal arrows and coherence, not positivity, stochastic normalization, boundedness on a weighted space, or semantics of a progress observable on an arbitrary formal apex.

## Elementary baseline calculations (independent, not novelty claims)

Use column-kernel convention. For internal substochastic Q, backward expectation is Q*V(x)=Σ_y Q(y|x)V(y). Let survival time τ count internal transitions.

* If finite-valued V≥0 satisfies Q*V≤V−1, telescoping gives Σ_{k<n}Pr(τ>k)≤V(x), hence Eτ≤V(x). This is a standard drift/Poisson-inequality proof; no cylinder machinery is needed.
* If V≥1 and Q*V≤ρV for ρ<1, then Pr(τ>n)≤ρ^n V(x). This is weighted-norm contraction/geometric drift. An unbounded V is compatible with countably many states; finite V at admitted initial states is essential.
* If an operational stochastic comparison L:X→Y satisfies LQ_X=Q_YL, then Q_X*L*=L*Q_Y*. Positive pullback transports inequalities. To transfer a lower bound by 1, require L*1=1; if L is merely substochastic that implication fails. For an unbounded V, also require L*V finite on relevant inputs. This calculation explains the exact extra content absent from an arbitrary formal comparison arrow.
* Given vector local potentials and an actually proved nonnegative gain inequality, a positive weighting satisfying a strict aggregate contraction yields a global potential. Checking the gain inequality must include the wiring, not only isolated modules. Spectral-radius or positive-weight feasibility criteria are small-gain baselines, not themselves a realization theorem.

A stochastic comparison can preserve expected potential but fail to preserve nonlinear predicates of that potential, such as threshold events. Consequently transport of the stronger p,d rule needs more than just the affine expectation intertwiner: deterministic observation compatibility or a proved lifting/coupling condition sufficient for those events must be supplied.

## Exact missing ingredient and acceptance tests

A satisfactory theorem should define an operational certificate interpretation over the relevant cylinder data and then prove the following, without assuming their conjunction as a “compatible reconstruction” axiom:

1. **Meaning on reconstructed data.** Specify which preparation/test observables carry V, cost, thresholds or tail bounds. Explain what the positive cone and normalization mean there. A formal Isbell presheaf alone is not a Markov state space.
2. **Derived transport.** Calculate the signed canonical comparison and show its action is positive/normalization-preserving on the required observables, or show a concrete operational witness supplies such an action. State its direction. A two-legged formal span does not automatically give two-way simulation or termination reflection.
3. **Descent or witness invariance.** If the certificate lives on an honest realization rather than the canonical apex, prove the induced admission/estimate is independent of the admissible witness where claimed. Do not demand a global functorial section: the previous no-section theorem rules that out in an elementary subcase and it is stronger than necessary.
4. **Actual local assembly.** Derive the interconnection inequality from component interfaces and explicit wire compatibility. Local termination in isolation is not enough. Check changes of nesting, wire hiding and interventions against the same quantitative witness, with budgets updated rather than silently reset.
5. **Infinite limit.** Prove that finite-unfolding estimates control the limit. Support positivity commutes with nonnegative sums, but “zero deficit” does not commute with increasing approximations. A tail bound or valid a.s. rule is the substantive evidence.
6. **Scope separation.** Distinguish sufficient admission certificates from complete characterization; finite mean from a.s.; source operational arrows from arbitrary completion arrows; preservation from reflection.

## Recommended ambitious but honest deliverable

First build a certificate-enriched operational doctrine in which primitive comparison arrows and wiring have independently checkable positivity/normalization/progress conditions. Prove a comparison-lifting/descent theorem for the cylinder construction on that doctrine, with an explicit counterexample outside it. Demonstrate it on the biased infinite walk and on a genuinely coupled system where isolated certificates do not compose automatically.

If only the drift/gain calculation can currently be proved, label it a baseline lemma and keep the operational reconstruction bridge open. The full claim is not established by applying the free Isbell functor to a category already defined to contain exactly the terminating composites: that would package the answer rather than derive it.
