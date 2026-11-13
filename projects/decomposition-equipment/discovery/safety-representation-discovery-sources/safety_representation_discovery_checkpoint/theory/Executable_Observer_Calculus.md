# Executable observer witnesses for quantitative decomposition discovery

Proof candidate, 29 October 2026. The finite-state, communication and linear-programming mechanisms below are standard. The contribution to the current construction is an exact common interface between executable information acquisition, partial-evidence laws and quantitative task certificates. This does not identify physical mechanisms or prove an interpretation in the original graph-cut C5 presentation.

## Plain-language abstract

A mathematical statistic is not automatically a sensor or a message that a robot can obtain. This note makes that distinction explicit. A candidate observer is a small program with named sensor inputs, private memory, actual messages and a declared communication schedule. Its program determines exactly which statistic of a complete execution it can report. Only such certified reports can be used as executable evidence patches. Their probability laws must still come from data or other justified assumptions; discovering the program does not manufacture the missing measurements.

The same program semantics translates an evidence bound into a linear constraint on the possible whole-execution laws. Quantitative risk certificates can then be decomposed into weighted local report statistics. The construction preserves one underlying execution and its shared uncertainty when reports are combined. It also distinguishes three failures: current evidence cannot certify the requested risk bound; a chosen representation discards evidence needed for assurance; or the relevant statistic cannot be delivered through the permitted interface. An exact finite search can discover a least-cost observer family within declared implementation budgets. Its search can be enormous, and a practical environment may lie outside the evidence assumptions.

## 1. Finite trace domain and three different objects

Fix a horizon H and a finite complete execution alphabet. Let Omega be the finite set of complete action/readout traces, including any actually recorded hazard proxies, admitted by the behavioral universe. It need not consist of states of a supplied latent Markov model. The main quantitative theorem determines which probability laws mu on Omega are compatible with the exploration policy, available observations and physical hazard decoder.

Keep these objects separate:

1. A raw physical readout stream, named by a sensor or communication port.
2. An executable observer D, whose output is a deterministic statistic Psi_D:Omega -> Y_D of those readouts.
3. Evidence about the law of Psi_D, such as a simultaneous confidence interval for E_mu[f(Psi_D)].

An executable observer does not by itself establish item 3. An unrecorded new observer is a proposed measurement, not an extra constraint on the current law. If an archive contains the required aligned raw readings, the observer can be replayed to compute its outputs. If it does not, a claimed replay must be rejected. An observation interval may instead come from a separate experiment or calibration, but its relationship to the same underlying law must be justified.

Adding a new report to a fixed controller's action inputs changes the controller unless that input was already part of its specified behavior. The observers here may be used for acquisition, auditing or declared monitoring. Any altered control policy needs its own risk calculation.

## 2. A typed executable syntax

An input or output port has a finite value alphabet, a named physical owner and a time/phase index. A declared directed schedule says which messages can reach which receiver before each update. An observer has finite named memory carriers, an initial-memory specification independent of unobserved inputs, sensor-read permissions, and message alphabets.

Primitive program nodes are:

- a permitted local read at its actual time and owner;
- a deterministic finite table using values available at that node;
- a named memory update, with old memory read before the next memory value is written;
- an allowed message encoder, channel and receiver stage with its declared delay and alphabet;
- a local copy or discard operation when the hardware signature permits it;
- a constant independent of the physical trace, with its resource cost if any.

Unroll a finite-state observer for H steps. Every internal edge must go forward in the declared phase order, except that a memory edge goes from one time slice to the next. Thus no node can read a future observation, an undelivered message or another owner's private state. The complete unrolling is a typed acyclic circuit. Local update feedback is permitted through the delay edges.

The circuit stores a registry of physical sensor, memory and source identifiers. If two branches refer to the same sensor reading, they use the same trace coordinate. A syntactic copy does not create an independent random sample. Private randomization, if admitted, must be represented by a declared coin input with its specified law; this note otherwise treats deterministic observers.

The resource grade records memory-carrier sizes, channel alphabets, transmitted values, phases and latency. It is computed from the actual program, including shared nodes. A proposed budget is a predicate on this grade. An arbitrary budget-filtered family need not be closed under composition.

The primitive library must be backed by an explicit capability contract: which installed sensor exposes which record, which processor can read it, and which messages can arrive by which deadline. The mathematical checker verifies compliance with that contract, not the truth of a hardware attestation. The accompanying reference programs establish computational causality and finite-state implementability; they are not hardware-in-the-loop verification.

The law comparison assumes passive acquisition: the observer's sensing, storage and communication do not change the environment or the specified controller's behavior. If logging consumes safety-relevant CPU time, network bandwidth, energy or mechanical resources, those effects must enter the protocol and risk model. Installing such an observer is then a different experiment or implementation, not a harmless postprocessing map on the old data law. Timing/memory grades reveal some such costs but do not prove noninterference.

### Source semantics and composition theorem

For a typed circuit D:X->Y, evaluation in phase order determines a unique function F_D:Val(X)->Val(Y). The type X is the complete named input-port bundle, including any retained side inputs. An actual acquisition contract supplies a read map rho_X:Omega->Val(X), and the observer statistic is Psi_D=F_D composed rho_X. Well-typed sequential plugging E:Y->Z obeys

    F_(E after D) = F_E composed F_D,
    Psi_(E after D) = F_E composed Psi_D.

If E also reads side inputs, those inputs must be retained explicitly through D by extra named wires; they cannot be silently read from Omega. Parallel execution on the common underlying trace obeys

    Psi_(D parallel E)(omega) = (Psi_D(omega), Psi_E(omega)).

Both sides use the SAME omega and common source registry. Sequential plugging and parallel wiring are associative up to the canonical tuple reassociations; identity wires evaluate to identity maps. Nullary constant programs evaluate to their declared constant, not to an unspecified physical source. The resource grade is recomputed after plugging, and an over-budget composite is not admitted merely because its parts were.

Proof. Induct through the topological node order. Every table receives exactly the values of its incoming nodes, and every memory value comes from the previous declared update. For plugging, the induction first evaluates D and then substitutes those values into E. For parallel programs it evaluates both on the same input assignment. The identity and associativity equations follow from finite function composition. The registry prevents distinct evaluation variables from replacing one shared physical reading. QED.

This supplies a concrete categorical layer: typed scheduled circuits compose, and evaluation is a semantics-preserving map into causal finite trace maps. The observer program and its denotation are not disconnected descriptions. It does not supply virtual-equipment structure or an embedding into original C5, and a resource-restricted subcollection is not automatically a category.

## 3. Exact compilation of unknown observers

A finite implementation budget declares a bound on memory sizes, gates/messages and allowed time/phase slots, together with finite port alphabets and allowed wiring choices. This bounds engineering implementations; it does not enumerate latent environmental mechanisms.

Unknown wiring, memory-update tables and encoder tables are finite variables. For every admitted local input assignment introduce the literal table-evaluation constraint. Each node is checked for owner, time and read permissions. Repeated uses of a table or memory identifier use the same variable. Unrolling the constraints on each trace evaluates Psi_D without an oracle deciding whether a statistic is executable.

A statistic target f:Omega -> Z is implementable by such a program precisely when these constraints and the terminal equalities output_D(omega)=f(omega) are jointly satisfiable for every omega in the declared support. This is a finite synthesis problem. It is complete for the declared implementation language, not for arbitrary physical devices. Checking only observed traces proves agreement on those traces, not implementation of f on every possible execution.

A full trace expansion may be exponential. The node constraints can be represented by local circuit factors; their actual induced width controls elimination costs. It is not enough that the physical communication network has small width. Persistent memory, repeated table entries, common sensors and the risk decoder can create additional coupling. No general compactness or polynomial synthesis claim is made.

## 4. Executable reports become evidence rows

For a program D define its pushforward matrix P_D by

    P_D[y,omega] = 1 if Psi_D(omega)=y, and 0 otherwise.

The law of its report is P_D mu. If f is a numerical test on Y_D, its evidence row is a_(D,f)(omega)=f(Psi_D(omega)). Consequently

    E_mu[a_(D,f)] = E_(P_D mu)[f].

This equation is an exact semantic bridge. The statistical procedure must justify any claimed interval l <= a_(D,f) mu <= u, including adaptation or selection over candidate observers. For example, simultaneous intervals over a finite evaluated observer family can support later observer selection; intervals valid only for one preselected observer cannot silently be reused after searching many observers.

For typed postprocessing E:Y_D->Z, let Q_E be the deterministic pushforward matrix of F_E. Then P_(E after D)=Q_E P_D. Thus certified postprocessing transports evidence by an actual linear map. The root-trace pushforward P_D and the intermediate report pushforward Q_E have different domains; they are not interchangeable. Parallel reports produce the joint pushforward P_(D parallel E) mu. Their joint law is NOT determined by P_D mu and P_E mu separately, and is not their product unless justified by the behavioral model. This is exactly where an omitted interaction can matter for safety.

For a noninvertible postprocessor h, a report class has its actual preimage set. Forgetting a distinction enlarges the set of possible fine report laws unless the discarded information was already irrelevant to the task. It does not supply a chosen fine report or an inverse interface. The compilation and law constraints retain any shared fine variable that a later request still inspects.

## 5. Quantitative certificate interface

Let A mu=b include normalization and the justified behavioral equalities, and let mu>=0. For selected evidence rows a_i with simultaneous bounds l_i<=a_i mu<=u_i, define the feasible law set C_D. Assume it is nonempty. Let c(omega) be the main theorem's fixed-controller risk score, including its justified policy-change weight and sound hazard decoder. Write

    U_D = max { c mu : mu in C_D }.

The finite primal is bounded whenever c is finite. Linear-programming duality gives

    U_D = min b beta + sum_i (u_i lambda_i^+ - l_i lambda_i^-)

subject to lambda_i^+,lambda_i^- >=0 and the pointwise certificate

    A^T beta + sum_i (lambda_i^+ - lambda_i^-) a_i >= c.

Therefore a feasible dual with value at most epsilon proves a score bound E_mu[c]<=epsilon for every law in C_D. If the main physical transfer theorem gives P_pi(bad)<=E_mu[c]+eta_plus, a physical risk budget tau requires epsilon+eta_plus<=tau. A score bound is not silently equated with physical hazard probability. Each a_i is the pullback of a test on an actual executable observer. The beta terms are justified behavioral equalities, not fictitious measurements. Dual weights may be signed after combining the two nonnegative multipliers; they are proof potentials, not transition probabilities or physical mechanisms.

This is a decomposition of the risk proof across executable report interfaces. It is not by itself a factorization of the environment into independent mechanisms. Shared uncertainty remains in the one law mu. A claim of physical component reconstruction needs an additional operational realization theorem.

### Exact use-relative adequacy criterion

For a fixed threshold epsilon, an admitted observer family is sufficient for the current evidence-and-controller query iff U_D<=epsilon, equivalently iff the displayed dual has a feasible solution with value <=epsilon. This is a test of the chosen representation, not a premise that all representations are adequate.

The criterion is useful only with its quantitative and implementation qualifications: every evidence row must have a valid bound, its report must be executable or replayable under the actual acquisition contract, and c must be a justified risk score. Declaring all laws impossible would make a false certificate; emptiness of C_D is an evidence/model inconsistency requiring its own diagnosis.

### Certificate transport through a coarser interface

Fix a validated dual certificate and group all its weighted tests belonging to one observer D into the numerical potential

    phi_D(y) = sum_(i belonging to D) (lambda_i^+ - lambda_i^-) f_i(y).

Let q_D:Y_D -> Z_D be an admitted postprocessor. As an identity on the full declared report alphabet Y_D, the SAME potential can be expressed through the coarser report iff it is constant on every fibre of q_D. If only a separately justified reachable report image is required, fibre constancy is needed only on that image; the full-alphabet test is sufficient but need not then be necessary. Necessity follows because equal q_D values must give equal decoded potential values. Sufficiency defines bar_phi_D(z) by the common value on that fibre. The factorization is checked by finite table comparison and has an executable decoder.

When this holds for every D, replace phi_D composed Psi_D in the pointwise risk majorant by bar_phi_D composed q_D composed Psi_D. The two functions on Omega are literally equal, so the majorant is preserved. The original calibrated upper bound on the sum of expectations must also be retained, or a new valid bound on the coarse statistics supplied. Changing an observer does not preserve a confidence interval by convention. If each original test itself factors through q_D, its same numerical interval transports directly; aggregate-potential factorization can be sufficient even when the separate tests do not factor.

This is an exact criterion for transporting a FIXED potential representation through that adapter. It does not characterize whether some different dual certificate could succeed on the coarser information; that is the new coarse risk LP. A failed factorization is therefore an implementation obstruction for this certificate, not proof that every possible assurance argument fails.

For uncertainty sets, forgetting evidence gives a monotone relaxation: the old law set is contained in the set defined by only the retained justified rows. Its robust upper risk cannot decrease. If a fine report-law uncertainty set Q is available, its exact coarse uncertainty is the linear image P_q Q. Replacing that image by separately bounded coordinates can enlarge it further; this extra relaxation must be charged rather than called exact transport.

A newly measured joint report is represented by P_(D parallel E), on the same underlying trace. Its confidence constraints can remove laws allowed by the two marginals separately. There is no licence to replace them by a product or to discard them when a noninvertible adapter drops the relevant interaction. A selected representation retains the full assurance value precisely when its own valid risk LP has that value; duality supplies a corresponding certificate and a larger value supplies a concrete primal law exposing the loss.

## 6. Discovery and informative failure

Let C_full use every currently available justified evidence row. A selected family D uses a subset, so C_full subset C_D and U_full<=U_D. Distinguish:

**Representation loss.** If U_full<=epsilon<U_D, an optimal high-score law mu_bad in C_D violates at least one unused available row. Otherwise it would belong to C_full, contradicting U_full<=epsilon. That violated row gives an explicit missing distinction or interaction to add, subject to its executable observer cost. Iterating adds a new row each time, so a finite row family reaches an adequate representation whenever C_full is adequate and all required programs are admitted. This is a finite completeness statement, not an efficiency claim or a new generic CEGAR mechanism.

**Evidence insufficiency.** If U_full>epsilon, no rearrangement or compression of exactly the same constraints can establish the bound. If also L_full=min_(C_full)c mu<=epsilon, primal extremizers give a low-score-compatible and a high-score-compatible law. They may motivate a further observer that separates their pushforward laws, but no new bound is obtained until its measurements or other evidence are justified. If L_full>epsilon, all laws in the declared confidence set exceed the SCORE threshold; this is not merely loss from the selected representation. When c is only an upper hazard surrogate, a high score does not establish physical unsafety. A physical rejection needs an exact hazard score or the main theorem's separate lower-hazard transfer condition.

**Implementation insufficiency.** If the distinguishing statistic requires unavailable sensing, memory, communication or latency, it cannot be admitted as a current interface. A source-level synthesis obstruction or communication lower bound explains that failure. Existential construction of the mathematical statistic is not an executable certificate.

Because candidate programs under a finite budget are finite, one can enumerate them, compute their certified rows, and optimize the cost of a family admitting a dual risk certificate. The cost is that of the actual assembled program family, including shared nodes and communication; it is not automatically the sum of separately optimized local costs. Exhaustive optimization returns a least-cost solution relative to the declared program budget, cost rule and evidence rows. It may be prohibitively expensive. No universal least physical decomposition, unique optimum or polynomial approximation guarantee is claimed.

Existing-data eligibility must be checked before adding a row. A program whose required readings are absent from the archive enters a proposed-measurement list rather than C_full. A prospective observer can distinguish a particular primal pair without guaranteeing that every subsequent outcome will resolve safety.

## 7. Exact one-message information obstruction

A useful physically interpretable special case has a sender record s in S and receiver-local record r in R. In one simultaneous one-way phase, the sender transmits m(s); the receiver must recover a required statistic f(s,r). The sender cannot inspect r before sending.

Define s~s' iff f(s,r)=f(s',r) for every admissible receiver record r. On a full product S times R, the smallest possible message alphabet has exactly the number of equivalence classes of ~.

Necessity: if m(s)=m(s'), the decoder receives the same message at each fixed r, so the required outputs must agree. Sufficiency: send the equivalence class and use its well-defined response row as decoder. The result permits arbitrary encoder preprocessing; it therefore does not rely on forbidding clever coding. For a non-Cartesian joint support, a different confusability graph or support-relative problem is needed; the product criterion must not be applied silently.

For example, let s,r be integers in {0,...,K} and f(s,r)=1[s+r>K]. Every sender value has a different response row. Thus a receiver-independent message needs K+1 symbols, or ceil(log2(K+1)) bits. Sending only a sender's own dangerous/not-dangerous flag generally fails. If the receiver may first send r, a later one-bit reply f(s,r) suffices; that is a different two-phase interface with added communication and latency.

This threshold example can represent a declared quantized stopping-margin score. A physical stopping-distance formula must independently justify that score and its approximation error; the communication argument alone does not establish vehicle safety.

The result is classical deterministic communication complexity. Its role here is to turn a risk-relevant interaction requested by the primal/dual analysis into an explicit executable-interface obligation and, when the budget is too small, an informative obstruction.

## 8. Remaining limits

The exact source/semantics bridge is between scheduled observer programs and their report laws. It does not finish the original operational/C5 integration. Quantitative law constraints require simultaneous coverage justified by the sampling design; causal policy change and physical hazard decoding belong to the main theorem. The method identifies behavior distinctions needed by a specified assurance query, not the unique physical architecture. A least-cost program found within budgets may still be too expensive or too slow for deployment. These limits remain visible rather than being absorbed into an existential witness claim.
