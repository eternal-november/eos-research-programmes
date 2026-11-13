# Related results and scope of the positive interface theorem

30 October 2026

The theorem combines established finite probability, experiment determinacy,
positive realization, concentration, policy transfer, and categorical comparison
techniques under explicit operational assumptions. This bibliography is a bounded
research map, not a determination of priority or a claim that no earlier theorem
covers the same combination.

## Safe learning and stochastic composition

Jiang, Zhao and Coogan, *Safe Learning for Uncertainty-Aware Planning via Interval
MDP Abstraction*, construct high-confidence interval MDPs, combine them with
temporal-logic specifications, prune failing actions and collect further data
along nonviolating cycles. This is an existing safe-learning-and-planning
architecture, not a derivation of arbitrary shared-source interface adequacy.
Its noise, regularity and high-confidence-bound premises remain significant.
[Primary source](https://arxiv.org/html/2202.01358)

Lavaei et al., *Compositional Reinforcement Learning for Discrete-Time Stochastic
Control Systems*, give finite-horizon probability transfer and network bounds.
The convergence result uses Robbins-Monro conditions and infinitely many visits
to state-action pairs. Those premises do not establish finite safe acquisition
inside a nonresettable mission budget.
[Primary source](https://arxiv.org/html/2208.03485)

Schön, van Huijgevoort, Haesaert and Soudjani, *Verifying the Unknown*, give local
sub-simulation relations with interface functions and a network composition
theorem. The network kernel is a product of local kernels. Shared noise cannot
be replaced by independent marginals under that premise; a correct joint
source or exposed shared state requires its own representation argument.
[Primary source](https://arxiv.org/html/2309.01276v1)

Schön, Haesaert and Soudjani, *Formal Control for Uncertain Systems via
Contract-Based Probabilistic Surrogates*, combine behavioral inclusion,
simulation, assume-guarantee contracts, ambiguity compensation and situation
probabilities. Their situation/awareness interface is supplied. A theorem that
likewise assumes an adequate operational interface has not thereby shown how
that interface is safely obtained from evidence.
[Primary source](https://arxiv.org/html/2506.16971v1)

Huang, Yang and Liang, *Safe Exploration Incurs Nearly No Additional Sample
Complexity for Reward-free RL*, study safe exploration followed by policies
for subsequent reward/constraint choices. The setting uses episodic MDPs with
a fixed initial state, a known safe baseline with slack, and feasibility
margins. Expected cumulative-cost safety is not automatically absence of every
adverse trajectory event. Persistent interaction additionally requires explicit
reset accessibility and remaining-state/resource accounting.
[Primary source](https://arxiv.org/html/2206.14057)

Nazeri, Badings, Schmuck, Soudjani and Abate, *Data-Driven Abstraction and
Synthesis for Stochastic Systems with Unknown Dynamics*, construct abstractions
from noisy state-input-state observations without separately observing the
noise, under valid Lipschitz bounds. The probability intervals use i.i.d. noise
samples. This does not remove the need for a conditional sampling argument
under adaptive or temporally dependent observations.
[Primary source](https://arxiv.org/html/2508.15543)

## Statistical and causal abstraction baselines

Howard, Ramdas, McAuliffe and Sekhon, *Time-uniform, nonparametric,
nonasymptotic confidence sequences*, supply simultaneous-in-time coverage
under specified martingale and tail conditions. Such tools support adaptive
stopping; they do not certify their own conditional model assumptions. Delayed
reports, reused samples, and the actual filtration must be accounted for.
[Primary source](https://doi.org/10.1214/20-AOS1991)

Lorenz and Tull, *Causal and Compositional Abstraction*, define component-level
abstraction through functors and an epic natural transformation and derive
query-level abstraction. Generator-level equations extending to composite
diagrams are therefore an established baseline. The construction does not
automatically provide finite safe acquisition or the particular CFS realization
comparisons used here.
[Primary source](https://arxiv.org/pdf/2602.16612)

Asiaee, *Certified Interventional Fidelity*, studies anytime inference for a
supplied abstraction/correspondence using a declared interventional score and
target distribution, including predictable proposals with bounded importance
weights. Distribution-averaged fidelity is not worst-case adequacy over every
mission context, construction of the candidate interface, or safety of the
experiments themselves.
[Primary source](https://arxiv.org/html/2607.08349)

Uniform model coverage plus a robust conditional safety certificate is standard
probability/control composition. It does not show that a useful certificate
is reachable before resources run out. Conditioning on the future event that
all intervals cover can also alter conditional noise laws; a stopping-at-first-
coverage-failure or direct good-history argument avoids treating that event
as a fresh independence assumption. Refusal and missed completion must be
counted separately from the event of acceptance followed by failure.

## Finite experiment determinacy and comparison

For a finite probability vector p, let A encode the complete admissible
experiment transcripts and include normalization. A linear mission quantity
f^T p is determined by Ap for every p exactly when

    ker A is contained in ker f^T,
    equivalently f belongs to rowspan(A).

Sufficiency expresses f as A^T c. For necessity, a vector h in ker A with
f^T h nonzero has zero total mass; small opposite perturbations of an interior
probability vector give indistinguishable evidence and different mission values.
This is finite-dimensional estimability, not a new result caused by changing
terminology.

For Boolean marginal experiments, the row space is spanned by Walsh characters
whose supports lie in an allowed joint query set. An uncovered character gives
the usual parity perturbation. O'Donnell's *Analysis of Boolean Functions*,
Chapter 6, provides the Fourier and k-wise-independence background.
[Primary source](https://www.cs.cmu.edu/~odonnell/papers/Analysis-of-Boolean-Functions-by-Ryan-ODonnell.pdf)

The rows of A must represent complete experimental transcripts. Two singleton
reads of the same persistent source reveal a joint pair, unlike two singleton
reads on independent fresh sources. Adaptive same-source querying can enlarge
the observable algebra. A criterion established for fresh vectors per joint
probe cannot be transferred unchanged to a different polling regime.

Hailperin, *Best Possible Inequalities for the Probability of a Logical Function
of Events* (1965), is an early probability-bounds and linear-programming
baseline. Robust probability bounds from partial event probabilities are not
new. [Publisher record](https://doi.org/10.1080/00029890.1965.11970533)

Elfving, *Optimum Allocation in Linear Regression Theory* (1952), optimizes
experimental allocation for linear functionals and discusses differing costs.
This is an experiment-design baseline for resource-constrained estimability,
not an assertion that arbitrary adaptive mission-safe variants reduce directly
to linear regression. [Primary source](https://doi.org/10.1214/aoms/1177729442)

Blackwell comparison asks for one stochastic post-processing kernel uniformly
realizing one experiment from another, equivalently decision-problem dominance.
A signed linear estimator for one quantity is weaker than positive simulation.
Recovering one expectation from marginal laws does not produce a normalized
generative interface. [Primary source](https://doi.org/10.1214/aoms/1177729032)

Brooks, Frankel and Kamenica, *Comparisons of Signals*, study comparison robust
to correlated side information and restricted decision classes. Marginal
experiments need not determine joint information content. Their universal
side-information condition should not be imposed when only a specified
restricted mission-context family is required.
[Primary source](https://benjaminbrooks.net/downloads/bfk_comparisons.pdf)

## Positive realizations and categorical structure

The invariant-polyhedral-cone construction in the instrument lemma has a
classical finite Markov realization baseline. Boyle and Petersen, *Hidden
Markov processes in the context of symbolic dynamics*, Section 4.4,
Theorem 4.40, attribute the criterion to Heller (1965), with a correction in
Heller (1967). The action/output-instrument construction here is a controlled
variant, not a novelty claim for positive cone realization.
[Research source](https://math.umd.edu/~mboyle/papers/BoylePetersen07-10-2009.pdf)

Garner's *The Isbell monad* supplies the free cylinder factorization system
infrastructure. The accompanying structural notes derive the particular
comparison and coherence statements used by the positive-interface theorem.
[Primary source](https://arxiv.org/abs/1410.7108)

Joyal, Street and Verity's *Traced monoidal categories* supplies standard
algebraic trace and compact string-diagram machinery. Algebraic cups, caps,
and traces do not, by themselves, license new physical interventions or
instantaneous operational feedback.
[Primary source](https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/abs/traced-monoidal-categories/2BE85628D269D9FABAB41B6364E117C8)

## What this theorem establishes and leaves open

Within its supplied source/context doctrine, the theorem derives a positive
interface from permitted marginal evidence, transfers the admitted mission
law, gives finite strict-margin completion conditions with charged resources,
and supplies a sufficient capability/compiler witness. Its partial-pair family
leaves real hidden distinctions unresolved while proving they cannot affect
the admitted one-route mission.

Source grouping, joint coordinate interpretation, noninvasiveness, freshness,
calibration safety, causal gate/drain laws, transport, and context admission
remain assumptions. Deriving or validating sufficiently useful boundaries
and transport from permitted safe evidence is a stronger unresolved target.
This package is a scoped constructive synthesis and test case, not evidence
that those general discovery obligations have been completed.
