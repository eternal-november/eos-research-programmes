# Fair baseline comparison: learned parity mission and crossing certificate transport

31 October 2026. Bounded acceptance comparison under RC0.2 §RC7. This reviews the same parity family, not a new theorem, a novelty claim, or whole-contract acceptance.

## Verdict

**Standard methods can establish the positive parity mission from the same evidence, without identifying the physical source.** Binary elimination proves the global residual; a normalized linear constraint graph supplies the positive representative; finite common-response tables supply the crossing ownership implementations. Standard verification, refinement and assume–guarantee reasoning can carry the execution and reuse obligations when their actual hypotheses are checked. They are allowed to satisfy every requested output.

The useful contribution under review is an explicit, costed integration: keep the unresolved physical worlds, finite-data confidence, source/capture identities, restricted observable cylinder, local information permissions, physical execution and evidence dependencies aligned through a crossing change. The comparison establishes no exclusive expressivity, efficiency advantage, new graphical realization theorem, or new controller-synthesis principle. No baseline is penalized for not receiving a physical model that the proposed method also lacks.

## 1. Frozen hypothesis and output ledger

Notation distinguishes the full physical block from selected captures. Let `S_full` be the true block support, `P_cap` the known capture projection, and

    V_chain = {w : r_i = r_(i-1)+z_i (1≤i≤n), d=r_n},  n=2m≥2.

`K_phys` retains every stationary physical filter consistent with all retained evidence and physical premises. For the comparison use the sound relaxation

    C_chain = {T≤V_chain : A_i T=L_i, A_end T=L_end},
    L_i={(a,u,b):b=a+u},  L_end={(b,d):d=b}.

Every captured support from `K_phys` lies in `C_chain` on the correct-support event. Extra candidate-delay evidence stays in `K_phys`; `V_chain` need not be the projection of the all-evidence full-window maximum, nor itself realize every extra readout. This is the final theorem's narrower construction, superseding the preliminary framing audit's proposed equality with that projection.

| Item | Identical input/permission for proposed method and strongest applicable baseline | Required output or restriction |
|---|---|---|
| Physical universe | Fixed stationary F2 linear filter, fresh fair independent innovations, supplied memory ceiling D; unknown innovation count/grouping, coefficients and useful delay | No recovered actual wiring or complete world law is assumed |
| Probes | One local triple per fresh isolated block; endpoint pair; optional declared candidate endpoint probes. Choice precedes block, complete H+D separation including last acquisition-to-service gap | No full joint parity probe, revealing reset, block cloning, or favorable-block selection |
| Data | The same finite retained records and provenance; `m_e≥k_e+ceil(log2(K/δ))`, `k_e≤3` | The single simultaneous event E has probability at least 1−δ; full plane/diagonal spans must be checked, not supplied as facts |
| Physical premises | Reliable noninvasive readout, unchanged calibration/service law, isolation, clock/gate/interlock, complete drain/tail and certified latencies/capacities | Neither graph factors nor samples prove these physical assumptions |
| Uncertainty | `K_phys` and the sound captured relaxation above | Do not replace the family by the uniform representative; independent-z and shared-z alternatives remain |
| Service | Capture r0 and all zi, compute `p=r0+Σzi`, enable only selected load slot; actual bad event is `p+d=1` | Same causal controller, no early access to d or environmental r_i during production; refusal/missed completion is failure |
| Observable output | `Q(w)=(p,d)` and its coordinate-indicator tests; fixed public capture/schedule labels when guarded | Uniform diagonal Q-law for every T in C_chain; no equality of unrestricted early-input transcripts |
| Representative | Optional positive sampler of V_chain with n+1 independent representative events | Its event IDs are not learned physical innovation IDs; no replacement environmental hardware is implied |
| Crossing request | `{1,2}|{3,4}` versus `{1,3}|{2,4}` on `(u,b,v,c)`; actual declared deliveries and owners | Pointwise common output, source-preserving witness, local finite states, event-index grouping maps; not common ordered-planar refinement |
| Controller substitution | Real sensor bits replace representative coins; accumulator registers are controller state | Same actuator value for every deterministic input stream; each implementation's messages and timing checked separately |
| Initial opportunity | Same acquisition costs, certified computation model, storage, execution and tail budget B | `D+Σm_e c_e+C_check+C_service≤B`; charge all additional representation/checking work |
| Failure/repair | Same deleted channel or retracted evidence, same remaining budget and allowed repairs | Scoped loss, explicit repair and fresh confidence accounting; not universal controller impossibility |

The positive guarantee is conditional on the true full-plane/diagonal subclass and all capability/budget guards: on E the method accepts and completes safely; unconditional missed-or-unsafe probability is at most δ plus independently justified physical/acquisition allowances. No assertion is conditional merely on having accepted.

## 2. Binary elimination and linear constraint graphs: exact matched construction

Give the baseline the raw samples, not the true equations. It computes each empirical span by binary row elimination, checks the full masks and derives annihilating equations. The same union-bound proof gives E: for rank `r_e`, failure is at most `(2^r_e−1)2^(−m_e)`. Thus the baseline learns exactly the same local facts with exactly the same uncertainty and confidence.

Write `h_i=r_(i−1)+z_i+r_i`, and `h_end=r_n+d`. XORing the n+1 learned relations yields

    Σ_i h_i + h_end = r0+Σ_i z_i+d = p+d = 0.

This is an explicit binary row-span certificate. It proves zero hazard for the actual policy in every compatible physical world on E. It needs neither independent early bits nor the full law of those bits. Full endpoint diagonal support additionally makes Q surjective onto `{(0,0),(1,1)}` for each T; equal-size linear fibers prove its uniform law. The generic dual-union criterion from the predecessor is also available to the baseline, but this chain certificate already proves the named task.

For a positive representative, draw r0 fairly, then each zi fairly and independently, set `r_i=r_(i−1)+zi`, and copy `d=r_n`. The map from `(r0,z1,…,zn)` to V_chain is bijective. Therefore the representative is normalized, positive and uniform. This is a sequential constant-width graph, not an exponentially stored global table. A generic basis sampler is also legitimate but is not required to establish the stronger local implementation output.

Linear constraints, state boundaries and composition of graph fragments are established normal-realization tools. The parity construction above is our explicit application, not an attributed finite-data physical theorem. [Forney, *Codes on Graphs: Fundamentals*, §§2, 6–7](https://arxiv.org/html/1306.6264v2).

Factor graphs represent products of local functions; exact inference on suitable cycle-free structures and graph transformations are standard background. No loopy-belief-propagation claim is needed here. The normalized directed chain and eight-case tile calculation establish the desired law directly. [Kschischang, Frey and Loeliger, *Factor Graphs and the Sum-Product Algorithm*](https://www.isiweb.ee.ethz.ch/papers/arch/aloe-2001-1.pdf).

**Output achieved:** learned support relations, positive local representative, global mission implication, exact restricted Q-law and an implementable parity controller, subject to the shared physical/cost guards. None is exclusive to the witnessed calculus.

## 3. Common-response baseline: actual crossing, not separate marginal fits

For incoming a and representative bits u,v, use four equally weighted deterministic response strategies, indexed by `(u,v)`. For each a they output

    (u,b,v,c)=(u,a+u,v,a+u+v).

The column owners produce `(u,b)` then `(v,c)` with b delivered between them. The row source owner produces u,v at the declared times and delivers them to the parity owner, which produces b,c. The response table for each strategy is coherent across both charts for BOTH values of a. The resulting kernel is

    K(u,b,v,c|a)=¼·1[b=a+u and c=b+v].

This is a concrete feasible certificate for the existing common-response formulation in *Discovery and Reuse* §13; no LP search is required for this family. Four strategy values are not a grant of free shared-source access: the sequential realization draws each coin once and charges every delivery under the same permission table. Applying the response formulation to the scheduled local machines preserves the order of views and outputs rather than treating row owners as atomic tuple-return functions. Its generic unrestricted-source LP is not itself a fixed-source-budget theorem.

The same tagged elementary network supplies the common operational refinement. Owners are regrouped; stable merge by immutable elementary event index recovers the original event order. Direct and iterated regrouping are identical because they retain exactly those indexed events. The blocks genuinely cross, but this does not make them cuts of one laminar tree or supply a common original ordered-C5 refinement. The prior *Witnessed Feedback Composition* §7 already identifies that obstruction.

The local response method and intersection refinement are prior results in *Discovery and Reuse* §§13–14. Their original acquisition or product-block assumptions are not imported into the physical filter. Here they apply to the explicitly chosen representative tile; dependence across physical early inputs remains unresolved.

**Output achieved:** both crossing charts, common source-preserving operational witness, bounded local tables/state and compatible tagged grouping maps. A standard implementation carrying those fields can meet the entire chart obligation. A citation alone cannot certify its timing, ownership or physical provenance.

## 4. Synthesis, abstraction and refinement: precise applicability

### Direct verification and finite synthesis

The frozen task already specifies the parity controller. Verifying the learned invariant and schedule is sufficient; requiring a baseline to solve a much larger partially observed game would be unfair. If finite route selection from the predecessor is requested, the baseline can use the same simultaneous coverage tests and finite route checks, charging its actual search. A Bellman recursion or enumeration must preserve the same observations, retained block state, action timing and remaining budget. No full hidden-state observation is granted.

### Abstract interpretation

The learned linear relations provide a relational invariant domain. Propagating the XOR accumulator and projecting away internal r_i proves the residual exactly in this instance. A coarse nonrelational bit domain would lose parity, but the fair baseline may use the relational domain. Abstract interpretation is established semantics-based approximation infrastructure, not limited to such a coarse domain. [Cousot and Cousot, *Abstract Interpretation*](https://www.di.ens.fr/~cousot/COUSOTpapers/POPL77.shtml).

The RC0.2 anchor *Making Abstract Interpretations Complete* is not needed as an imported theorem here: this document neither invokes a universal complete-shell construction nor claims arbitrary domain completion terminates within the budget. The concrete parity propagation above establishes the exact result required.

### Feedback refinement

Reissig–Weber–Rungger Definition V.2 requires a strict relation between the relevant systems, inclusion of abstract enabled inputs in concrete enabled inputs, and inclusion of related concrete successors in abstract successors. Theorem VI.3 transfers a solved abstract specification through a valid feedback refinement relation. [*Feedback Refinement Relations for the Synthesis of Symbolic Controllers*, §§V–VI](https://arxiv.org/html/1503.03715v3).

These are legitimate baseline obligations, not unavailable expressive powers. To invoke that theorem on this task one must construct the appropriate scheduled systems and a relation from admissible observations/state summaries, checking successor and input conditions and the physical specification. The map `Q(w)=(p,d)` alone is NOT a causal feedback refinement relation: d is unavailable before the prediction, and its two-output law omits internal timing/control behavior. This comparison does not claim to have supplied a full FRR instantiation. It instead verifies the actual controller substitution pointwise: both chart implementations satisfy `p_i=p_(i−1)+z_i` for every input stream, followed by separate timing/permission checks. The same argument is available to a conventional verified-circuit baseline.

### Assume–guarantee contracts

The statistical premise, logical invariant, physical interlock and timing envelope can be packaged as explicit assumptions/promises with shared resource identities. Contract composition and refinement already support functional and nonfunctional viewpoints. [Benveniste, Caillaud and Passerone, *A Generic Model of Contracts for Embedded Systems*, §§2–4](https://arxiv.org/html/0706.1456v2).

Such a package can meet the complete integration output when instantiated and checked. Merely naming the contract framework does not establish empirical support correctness, safe acquisition, permission compatibility, or a physical deadline. This limitation applies equally to merely naming the witnessed calculus.

## 5. Equal resource accounting

The same samples suffice for every method. Local span work is bounded by `Σm_e k_e` row tests/updates on at most three-bit rows, plus charged reading/provenance; sparse telescoping and local template instantiation use linear-size records. Dense global elimination is optional, not a handicap imposed on the baseline. No runtime ranking follows without matched certified implementations.

The crossing artifact's normalized core bound is `445n+597` abstract word-RAM operations, with admitted workspace `32(n+16)` words. It excludes normalization/provenance/physical payload costs, raw-sample work not already verified, and actual service. It is an implementation-specific certificate, not a lower bound on standard methods. A standard baseline may reuse exactly that compiler and its checked evidence, not redo work merely to count as a baseline. Generic identifier validation or other representations retain their actual larger costs.

The representative sampler's `7m+3` ticks are not physical capture time. If it is not executed, do not charge its runtime as service; if it is executed, charge it separately. Both baselines and the proposed method retain this distinction.

Under the named physical unit-latency fixture, both controller charts are ready at `2n+1` with n XORs, an n+1-bit capture bank and the supplied channel capacities. Column internal/intertile transmission totals n−1 bits; row totals 3m−1 bits, excluding the common actuator command. Row needs a two-bit one-tick channel for that ready time; serializing it on a one-bit channel gives `2n+1+m`. Equal functions do not imply equal affordable deadlines. Arbitrary hardware uses its actual latency sums, memory and full drain/tail, in both comparisons.

## 6. Same-family ablations and repairs

1. **Delete row delivery of u.** Freeze the parity owner's information to `(a,v)` and independent private randomness, excluding every substitute carrying u before b is due. Conditional u remains fair, so any output matches `a+u` with probability exactly 1/2. All baseline methods recognize the same local implementation impossibility. One authorized bit restores the recurrence; charge channel, buffer, permissions and latency. This is not a physical-mission impossibility for every controller.
2. **Retract triple k.** The good filter and the filter injecting an independent fair E into all r_i for i≥k and into d agree on the remaining triple/endpoint evidence, while the old controller's residual in the latter is E. Its hazard is 1/2. This invalidates the old zero-risk certificate for all methods, without proving no alternative policy exists. With extra delay evidence, use only witnesses also agreeing on those records, or the fixed-delay subfamily.
3. **Repair evidence, unchanged good regime.** Reacquire the permitted triple with `m_r=3+ceil(log2(1/δ_r))` fresh blocks, recheck its full span and downstream dependencies. Charge boundary/drain, acquisition, checking and service. Confidence is at least `1−δ_old−δ_r`; repeated repairs need separately justified allocations. The bad injected-E source is correctly refused on the new correct-span event. If physics drifted, untouched evidence needs revalidation too.
4. **Insufficient remaining repair budget.** The conclusion is unresolved for this repair method, not universal infeasibility. A failed compiler or exhausted synthesis search is likewise not a universal NO.

These losses follow from information and physical counterexamples, not a special representation's failure. They supply a fair structural-information ablation for the same family.

## 7. Residual integration and acceptance disposition

| Required connection | Explicit evidence in the reviewed construction | What remains for acceptance |
|---|---|---|
| Samples → local facts → uncertainty | Predecessor §§1–3,6; crossing §1 | Check acquisition provenance and supplied physical premises; do not treat E as observed certainty |
| Local facts → positive representative → crossing | Crossing §§2–4; prior common-response methods | Check event identities, local views and grouping implementations; distinguish representative from real source |
| All compatible physical worlds → same mission cylinder | Crossing §5; equal-fiber maps `q_T` | Only declared Q tests; no unauthorized full-transcript transfer |
| Abstract comparison → actual calculus application | Crossing §5 invokes existing fixed-cylinder comparison using actual preparation/test maps | Verify the imported comparison's hypotheses and exact source-changing cells; no finite/executable canonical-middle inference |
| Logical success + real execution | Crossing §5A and §§6–7A | Verify physical capability, timing, provenance and total budget, not just algebraic masks |
| Same evidence through changes and retraction | Crossing §§8–9 | Check dependency versions, separate repair permissions/confidence and refusal semantics |

**Disposition:** the bounded RC7 baseline-comparison obligation is met by an exact matched-information comparison and same-family ablations. Standard methods are credited with every demonstrated output. The residual integration is substantive because the theorem connects data acquisition to useful uniform execution before full identification and preserves that result through a costed crossing change; it is not claimed mathematically unavailable to prior methods. Whether all RC1–RC9 duties, the two-assurance execution bridge, intrinsic calculus obligations and independent reproduction pass is a separate end-to-end acceptance decision. This comparison cannot close those by itself.

## Reviewed source identities

Titles and section references above identify the research artifacts without relying on machine-specific locations. SHA-256 pins the versions read for this comparison:

- *Evidence-relative crossing certificate transport on a learned parity mission*: `873ab22fa0b2d85a386af9c87b694c3a04674065458baa0d9c6ef1cc49bfb519`.
- *Safe finite acquisition and mission certificates with unknown linear noise coupling*: `60071e2c101926b94712fb6ce1237b7a55dd3cf39073c760e2c0b30d1372f731`.
- RC0.2 original read-only source: `be871717ec6f268fde9cd7106d7321c9f6b604a90c936a74335dce381cb1809f`.
- *Discovery and Reuse*: `6c5a77af7069936d2c9a653bb34858ef18bd636d1692fe258ed55e3fb29773dc`.

The preliminary *Audit of the first crossing interface contract target* supplies prior-method anchors, not a substitute for the later theorem's exact captured-support definition. External source links were checked against primary author/paper sources on 31 October 2026. No priority or literature-exhaustiveness conclusion is drawn.
