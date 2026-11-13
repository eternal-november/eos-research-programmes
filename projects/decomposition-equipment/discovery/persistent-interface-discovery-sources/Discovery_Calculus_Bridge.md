# Discovery-to-calculus certificates for the delayed mixed-readout family

28 October 2026. Written finite-model theorem using the actual API described in `../learner_decomposition_bridge_20261028/Calculus_Bridge.md`. Not a new Lean formalization, not an interpretation of arbitrary equipment restrictions, and not a novelty claim for linear-circuit verification.

## 1. The newly available inputs

`Coupled_Family.md` supplies, from noisy action/readout histories, a common latent representative (up to permutation), sparse delayed matrices A_l, action matrix B, calibrated sensor matrix M, biased independent innovation parameters, and two inferred lag-class partitions P,Q. The partitions are not passed to the learner. It also supplies each proposed region's outgoing filter D_l and its deterministic history quotient.

The discovery theorem recovers discrete structure exactly on its confidence event and real noise probabilities approximately. All **exact** semantic statements here are between presentations of the same fitted model, with the same fitted p_i. They hold for the true population model when its exact parameters are used. The statistical confidence statement relates the fitted and true transcript laws by the separate nH epsilon_p bound; these two kinds of equality must not be conflated.

Use the A_L-invertible stationary subclass. Its lag-register initialization is uniform on F2^(nL), a known product law on register bits, although no realized latent state is observed or reset. Each bit is sampled once, and all presentations reuse that same sample. Derived port registers are generally correlated; they are initialized by deterministic projections of this common initial history, never independently.

## 2. Canonical finite graph and deterministic augmentation

Let z_t=(X_{t-1},...,X_{t-L}) be the source lag-register vector. The canonical finite graph W has state z. Its canonical event is

    (z,u,e,nu),

where u is the externally supplied action, e contains one innovation bit per latent coordinate, and nu contains one measurement-noise bit per raw sensor. The target register and readout are deterministic:

    x = A z + B u + e,
    z_next = T z + J(Bu+e),
    y = M x + nu.

Here A=[A_1 ... A_L], T is the companion matrix, and J inserts the new first lag. Action is an event label, not a state-controlled random draw unless a controller law is additionally supplied. Conditional on z,u, event weight is the product of the n innovation Bernoulli masses and n measurement-noise masses, each appearing exactly once. Distinct events retain distinct named e,nu records even if they have equal probability. No extra hidden random token is introduced by refinement.

Augment W with finitely many interface/register values r=Kz and event fields v=Dz, together with any poststep values prescribed by the same deterministic formulas. The augmented state carrier is the **consistent** set

    {(z,r): r=Kz},

not the full product of arbitrary z and r. Events likewise carry only the uniquely determined augmentation. Projection to z and to (z,u,e,nu) is an actual bijection, with explicit inverse that computes the derived fields. It commutes with source and target, hence is a `Graph.IsIso`, using `Graph.isIso_iff_bijective` from the original API. This statement holds on all consistent states/events; therefore it also holds on every reachable restriction.

Importantly, projecting z to a minimal interface quotient alone is usually many-to-one and is **not** an exact graph isomorphism. Exact refinement retains the owned source history or another certified reversible sufficient joint register realization. The interface Hankel theorem minimizes a standalone influence stream transducer, not that whole source-plus-interface state. A source already holding old values may compute its outgoing delayed parity with no extra interface registers.

## 3. The original Assignment and a genuine common refinement

Use the original `Dynamic.Graph`, `Dynamic.Assignment`, `Assignment.Op`, `Op.witness`, `Op.Exact`, `Assignment.calculus`, and `operationEquiv`. An operation remains a boundary-preserving map from a whole graph to its compatible tuple graph, with both state and event maps. We do not replace this by a relation between output distributions.

First take the bounded-region shifted-matching chain from `Coupled_Family.md`. Order the site-owned factors along the chain; include the sensor factors and deterministic register factors at explicitly declared positions, carrying any required same-name records through intervening positions. A record mentioned in nonadjacent factors occupies an uninterrupted interval of bags. At cut k, boundary graph B_k retains exactly these through-records (including source/target histories required by graph maps). Assign them to quiver vertices v_k. Introduce interval colors c_ij:v_i -> v_j, with component graph W_ij containing the records and local equations in that interval and projecting to its two endpoint boundaries.

Every split i<k<j gives an original generator

    c_ij -> (c_ik,c_kj).

Its witness restricts a single consistent assignment to the two intervals. The scopes intersect precisely in B_k, including every shared equation variable; matching pieces have a unique union. Hence its state and event maps are bijections. The inverse is literal union of equal-name fields, not stochastic conditioning on equality of independent samples. This is `Op.Exact` through `operationEquiv`.

Local equations must be assigned to an owning bag containing every variable they mention. A bag carrier retains those equations and boundary variables; running intersection then guarantees that a compatible union satisfies every global equation. Projecting arbitrary local images without this equation ownership condition is not a valid join theorem.

Both matching partitions have interval blocks in the same site order: P groups (1,2),(3,4),..., while Q groups the endpoint singleton and (2,3),(4,5),.... Their two coarse profiles therefore refine, by actual interval split generators, to the same fine occurrence profile. Their coarse components own different groups of local transition factors but borrow the same through-records at boundaries. The common fine profile includes the fixed sensor/driver occurrences, not merely the latent transition factors. This is a common refinement in the **original** syntax, despite P and Q crossing as sets of owned modes.

The diagram from W to either coarse compatible tuple graph and then to the fine tuple graph commutes on states and on events: each composite returns precisely the same record at precisely the same fine occurrence address. The ordinary grouping equations consequently meet `EquationMaps`; `freeExtend`, `descends_iff`, and `presentedRefinementFunctor` apply on this explicitly declared signature. `Path.Slot`, `Path.expand`, and `SemanticRefinement.Arrow` retain distinct occurrences. Repeated parameter values do not identify noise draws.

### Scope of the larger torus example

A single site order cannot in general make every row and every column an interval. For the torus, build two separator Assignments with their declared factor orders and compare their whole consistent-record graphs through W. The resulting maps are still explicit state/event bijections and probability-preserving comparisons. A permutation of ordered leaves is **not** silently an equation of the original planar syntax. To call it an original same-signature refinement, an explicitly justified profile-comparison generator and its maps must be added and checked, or one must use a larger suitable signature. The bounded-region chain already establishes the genuine original common-refinement claim without adding a crossing/interchange rule.

## 4. Probability, timing, and execution theorem

Every innovation e_i has one owning transition occurrence. Every measurement noise nu_j has one owning sensor occurrence. All other copies are aliases with equality maps. Initial lag bits have one initial owner. At each tick the causal program reads old registers and action, samples the new innovations, computes next modes, then samples sensor noise and computes readouts. Borrowed successor values appearing in a completed graph record are matching fields, not available early to choose an action or sample a preceding kernel.

For either decomposition, local recurrence summands plus incoming port influences equal the original matrix row. The owned innovation and sensor-noise laws are unchanged. Consequently each event's complete weight, not just its support or separate marginals, is unchanged by restriction/union. The initial law is transported once through the same bijections. This meets the causal owned-kernel and initialization hypotheses of the prior `Calculus_Bridge.md` assembly theorem.

**Execution theorem.** The two chain decompositions and their common fine refinement have bijective corresponding state/event paths at every finite length, preserving truncation and concatenation and the full noisy joint law. The identities hold at every source register and action, not just fitted stationary averages. Therefore they continue to hold for every controller policy using only its permitted noisy observation/action history: couple controller randomness and identical visible histories, then induct on time. No controller receives latent port parities merely because the internal modeled implementation uses them.

The statement is exact for every finite horizon simultaneously because a finite set of one-step algebraic identities and fixed persistent updates establishes induction. It is not extrapolation from matching a finite training horizon. Nullary units remain the actual boundary graph B_k with identity witness; an unobserved stochastic factor cannot be deleted as a nullary unit.

## 5. A finite supplied certificate and local checker

A certificate contains:

1. **Discovery/model record:** n,L; sparse A_l,B,M; the chosen coordinate permutation; innovation parameters/confidence intervals and known sensor-noise parameter; the A_L invertibility and uniform initializer assertion. Numeric confidence is checked separately from semantic equality.
2. **Ownership ledger:** one owner for every current e_i, nu_j, and initial lag bit; unique global addresses; source-time and read-time of every alias; one entry for each actual sensor wire and modeled dynamic message. It explicitly distinguishes sensor channels from internal influence channels.
3. **Region data:** P,Q membership lists, recovered-support connectedness certificates and absence of lag-class cross edges; group membership is the output certificate, not supplied discovery access.
4. **Local port realization:** for each outgoing stack D, quotient projection K and finite linear update/readout matrices F,G,C satisfying the appropriate stream-filter identities. For example with source shift register z_S, z'_S=T_S z_S+J_S x_S, require

       K T_S = F K,       K J_S = G,       D = C K.

   Here D is the one-tick stacked influence map on source history. These equations imply all-time influence equality. Include rank certificates that K spans the finite Hankel image when minimum standalone state is claimed. Stack all recipients before minimizing; do not add individual recipient minima and call the result globally minimal.
5. **Augmentation/retyping data:** each derived register is an explicit linear function of owned history; projection and augmentation compose to identity on their consistency constraints. Any shared-register certificate must state the joint retained variable set and inverse, rather than treating a quotient as a bijection.
6. **Scope and calculus data:** ordered factor occurrences, interval scope endpoints, B_k records, equation owners, split-generator maps and their inverse-union rule, and the selected grouping equations. Any changed factor order is a separately supplied comparison, not assumed free.
7. **Assembly identities:** sparse equality of each local-plus-incoming recurrence to its A row, and each sensor parity to its M row; initialization of every derived register from the same initial lag register; event ownership and parameter-reference equality.

The checker verifies these as finite F2 linear identities, sparse support checks, permutation/rank checks, and occurrence/address checks. Universal equality over 2^(nL) states follows from coefficient equality; the checker never enumerates that global state space. Checking numerical parameter-reference equality is symbolic equality of the same named fitted parameter, so irrational probabilities do not require an exact numerical oracle. Approximate equality between two independently estimated parameter sets instead uses the separate error theorem.

If a local certificate has width w and R records/equations, straightforward elimination costs O(R w^3) field operations, plus sparse wiring/address checks and the cost of explicitly retained interface matrices. This is a conservative bounded-width bound, not a claim that every torus separator has fixed width. More generally charge the sum of each certificate's actual matrix-elimination cost and the actual number of scope incidences. Wide structural separators may carry O(n) symbolic records while representing exponentially many states; those records are real certificate size and cannot be hidden. They are not automatically extra runtime sensors or stored copies: physical ownership and wire ledgers determine those costs.

### Shared persistent-register certificates

For the companion register-sharing result, represent each token j as a named linear functional v_j of the same residual history and record its consumer-visibility set I_j. A consumer's declared basis must span its required subspace W_i within its admitted read budget. Check v_j lies in every W_i for i in I_j. A persistent update must satisfy the universal identity

    T v_j = sum_l a_jl v_l,

with every used token l visible to all consumers of j (I_l contains I_j), and its current-input contribution must lie in the admitted common input space for I_j. Use the dual/operator convention stated by that certificate; do not silently transpose a state update. All tokens are initialized from one common history. Any redundant linear relations, such as z=x+y, are part of the consistent state carrier and must be preserved by updates. These conditions let the same deterministic-augmentation graph proof apply to shared registers. A minimum-number-of-registers theorem needs the additional lattice hypotheses in the separate register-sharing result; it does not follow merely from the existence of this checker.

## 6. What can genuinely be reused

`Proposal_Validation.md` adds an observable certificate stage: a supplied bounded-width architecture is validated by one residual moment per proposed recurrence row and O(n^2) transformed-innovation pair moments, instead of repeating the discovery algorithm's support enumeration. This is class-relative and confidence-controlled, not an unrestricted model-correctness test. The shared-register lattice/visibility conditions are specified in `Shared_Interface_Realization.md`.

For fixed fitted model, ownership ledger, and named interfaces, the original occurrence-refinement APIs let checked local identities be substituted at every authorized occurrence without rechecking all complete global trajectories. Both crossing chain decompositions reuse the same atomic transition, sensor, noise-ownership and initialization certificates. A proposed replacement that preserves its typed boundary, owned-event bijection, probability references, and source-time availability requires rechecking its local certificate and incident ledger entries; unaffected certificate entries remain valid. Grouping equations are restrictions of the same records, so they need not be verified by global-state enumeration after each grouping change.

This is a matched **local-check/reuse guarantee**, not a lower bound on what other software can do. A baseline equipped with the same sparse equations, ownership tracking and compositional memoization can obtain the same savings. Standard circuit identity checking and linear-system minimization deserve full credit. The specific contribution here is that the checked objects are generated from an actually hidden noisy discovery theorem, infer both crossing region systems, retain persistent-interface constraints and exact occurrence-sensitive event laws, and connect to the existing original API rather than a replacement syntax.

Changes that alter a boundary alphabet, remove a required source history, change a noise owner, change sensor timing, or introduce fresh independent randomness are not automatically authorized exact refinements. Their comparison must be supplied and checked afresh; equality after marginalization alone does not imply `Op.Exact`.

## Verification status

The prior bridge's public API names and proof obligations were read directly. This note is a written constructive specialization and certificate specification. No new Lean theorem, tool execution against Lean, physical validation, or strict novelty claim is made. Algebra tests for the family are in `check_coupled_family.py`; those do not by themselves implement this whole certificate checker.
