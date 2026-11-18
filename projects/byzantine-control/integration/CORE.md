# One execution account for protocol, evidence, and independent effects

Status: general adapter and compatibility results with Lean and independent semantic checking; the first concrete adapter has been exercised over the retained peer-brake kernel. Whole-program checking remains open. This supplies a missing R1/R3/R4/R8 connection, not another stopping contract.

## The common object

The existing Execution.Model has arbitrary world and local-view types, one fixed fault index, local policies, and an action-indexed successor relation. Nothing in that signature requires an execution gate. The old common construction used a gate, and its clocked prescription compiler imposed an additional observation condition. These are specializations, not restrictions on every represented model.

CausalKernel in [CoreBridge.lean](CoreBridge.lean) exposes a joint fault index f; compliant policy executors C(f); initial worlds and local memory; jointly admissible observations; and actual effects. World retains physical, protocol, normative, queue, resource, event and mission-monitor state as consumed. A planner can remain compliant while a source, key, installer or actuator path fails. Those failures enter observations or effects under the same f, without deleting the planner's duties.

The effect relation receives actually issued compliant commands. It generates admitted faulty commands and independent effects internally. A faulty actuator can act despite a lawful OFF command, and a stolen signing key can produce an artifact without an intact executor issuing it. Those events remain in the relation. Normative prohibition does not remove them before mission evaluation.

The source's move order is preserved: current observations precede local commands; the adversary may react to current commands in choosing effects. No future command or private input is supplied. Exactness concerns this strongly informed causal adversary. A restricted adversary would require its own information-state implementation or an explicitly one-way overapproximation.

## Decision-boundary normalization

A boundary state retains world, local program memories and the current joint observation tuple. Actor i observes only its own memory and current optional observation. Fault identity, other actors' information, service age, physical state and analyst event records are not added.

Initialization includes every actual initial physical/local-input scenario and every permitted initial joint observation. One normal core edge consumes the current invocation, admits the actual effect, updates physical/mission state and chooses the next joint observation. That last choice prepares the next decision boundary; it is not another physical interval. Successful core edges correspond one-to-one with source physical intervals. Initial output obligations are checked initially, and the transition records next-epoch actual delivery.

This avoids turning observation, signing and computation subphases into extra physical service ticks or exposing an analyst phase counter. A communication or installation delay that actually consumes physical time must still appear; normalization cannot compress it away. The entire joint observation relation is retained: taking a product of its projections would change correlations, knowledge and potentially control.

The mathematical policy type is total, including at absent invocations. Such values are ghosts. They are erased before every source consumer: effect input, queue insertion, memory update, own-action history, conduct checking and adversarial observation of issued commands. Excluding a ghost only from the motion equation is insufficient. The absent_is_not_a_command lemma proves command/memory masking; the concrete source receives only the masked tuple.

The concrete profile(kernel,tables,boundary) constructs a following joint profile for checking, not a runtime oracle: only compliant invoked slots evaluate their local table. Other slots receive arbitrary erased fallback pairs. Thus a faulty-only observation outside the compliant alphabet cannot crash a callback the source never invoked. Correct entries depend only on their actual local memory and observation; follows_masks makes the analyst's choice for unused entries irrelevant.

A faulty executor's unused prescribed value is erased for the same reason. Its actual command remains an adverse choice inside the effect generator. The executable exercises a faulty actuator engaging during a lawful OFF invocation.

## Local initialization and memory

Finite tables include mu_i:J_i->M_i. The source initialization supplies actual local j_i; the same mu_i is applied in every fault scenario. initializedBy and local_initialization_covers formalize that mapping. The required source binding is K.initial f w m iff initializedBy Init mu f w m. Arbitrary CausalKernel.initial need not satisfy it. Under that binding, initialized_run_memory proves that every admitted run uses one actual local initializer input followed only by the actor's invocation observations; same_initial_input_same_memory rules out a hidden world/fault-dependent initial memory at equal inputs. The concrete Python adapter constructs exactly this initialization relation.

The concrete bridge fixes this local initializer. Changing mu during synthesis is a controller choice outside the fault quantifier, not permission to choose memory after learning f. Quantification over initializers must preserve the outer existential and cover every original physical/input scenario for each candidate. A candidate-dependent initialization encoding does not automatically give a same-arena strategy-reflection theorem.

A LocalProgram chooses command and next memory from its own current memory and received observation. source_memory_generated proves that each compliant memory is generated from its initial memory and received inputs. fold_erases_missing_calls and source_memory_is_invocation_local show that deleting absent invocations leaves the same memory. Silent physical intervals cannot become a hidden local clock.

Own issued commands are determined by that local execution and retained in effect records. Actuator feedback enters through the declared observation interface, not by equating intended and realized actions. Compromised process/key/actuator state that affects future behavior belongs in World or the adversary state. Held bookkeeping memory of an unfollowed prescribed program is not a model of all compromised hardware.

## Exact correspondence and legacy recovery

follows_masks proves that profiles following the local program have identical source-visible compliant commands and memory updates. core_step_iff_source_round and core_run_iff_source_rounds establish exact step/run correspondence. source_mission_transport carries any mission represented on those boundary traces. Since SourceRound is defined from the kernel, this proves an encoding transformation; it does not by itself establish that a Python or physical source implements that kernel.

Totality and safety remain separate. boundary_nonblocking derives successors from total primitive effects and observations. Its premise is stronger than totality only on retained valid boundaries; one may explicitly totalize irrelevant malformed interfaces or prove a restricted version. Failing choices cannot simply disappear.

The concrete completion sends missing observations/effects to losing terminal behavior. It does not drop initial worlds or adverse branches. A failed effect attempt still commits the already selected local invocation-memory update, then enters a terminal boundary with every invocation absent. Terminal stutters hold those memories and produce no service. Effect records distinguish performed physical transitions from diagnostic failure, so exactness is with the source's declared finite-failure completion, not a claim that an undefined physical plant literally stops.

Every earlier action-indexed Model has an explicit legacyKernel specialization: unit auxiliary memory, its old actual local observations, and an effect relation retaining the old Byzantine action profile. legacy_step_iff and legacy_run_iff establish exact recovery. legacy_run_exhaustive proves every admitted normalized legacy run is an embedding; the additional fields neither invent observations nor remove adverse choices.

This applies to the existing actual digital, witnessed-physical and institutional adapters. Their agreement, validity, service and certificate results retain their original contexts. Historical/epistemic atoms pull back along the exact embedding, and local-view equality is preserved on canonical states. The signed three-participant baseline does not thereby become HotStuff. Old protected suppliers do not become fault-tolerant merely because their model shares a carrier with another realization.

The common judgment therefore supports a real atlas: protected and independent-effect models have the same execution interface but different effect/fault relations. They are not equivalent plants. Property-specific assumption exchange must separately retain the mission and identify changed mechanisms.

## Clock-free prescription compatibility

A per-depth prescription sequence can use the analyst's global depth even where actors cannot read it. The relevant condition is compatibility.

For retained families K_t, CrossCompatible requires equal prescriptions at every pair of compliant occurrences with equal actor-local views, including different depths and fault scenarios. [Unclocked.lean](Unclocked.lean) proves equivalence with existence of one representing local policy, given nonempty action defaults. The construction adds no depth or fault information beyond the supplied interface; it does not repair an interface that already leaks them.

The proof applies the existing factorization theorem to an occurrence carrier containing depth as analyst data, which every local observation forgets. This auxiliary carrier is used only for factorization, never as a vacuously winning physical model.

For complete Reach families, represented_reach proves equality of all reachable states under the representing policy. No extra compiled-policy branches are introduced. Safety and nonblocking transport follow. General extraction uses classical choice; explicit finite tables support lookup construction.

This criterion matches all correct occurrences, including ghosts. It characterizes representation of the supplied sequence, not weakest effect-equivalence after irrelevant actions are erased. The concrete finite-program adapter supplies one policy directly and does not invoke the old clocked compiler.

### A recursive organizing object without a clock

Retain both a whole continuation family K and a partial table Gamma. Keys are actor/permitted local invocation histories with current inputs; global depth and fault identity are absent. At a stage, extend Gamma on the new invoked compliant keys appearing anywhere in K. Existing keys keep their values. Every adverse outcome and next joint observation enters the update, with actual history and monitor changes.

W_0(K,Gamma) requires a nonempty family with its current safe verdict. W_(n+1) additionally requires a consistent extension Gamma' covering all needed current keys, nonblocking for every admitted following profile, and W_n(Post(K,Gamma'),Gamma'). The update does not split unresolved alternatives into separately controlled worlds.

For finite explicit worlds, alphabets and horizon, enumeration of new-key assignments and successors is an exact procedure. Induction proves its characterization: an accepted extension supplies one table on every generated prefix; conversely, any admissible local policy restricts to such extensions. Gamma must persist across recursion because the same view can recur at different global depths. The old clocked recurrence is a specialization where actual locally observed time distinguishes those occurrences.

For infinite safety, a policy exists iff an infinite extending chain of these safe partial tables covers every generated finite prefix. Restricting a policy gives the forward direction. Conversely their compatible union defines one local policy; every finite generated prefix uses finitely many entries and belongs to some table in the chain, which establishes its verdict. Unused keys receive arbitrary nonempty-alphabet defaults. No runtime clock is introduced.

With finite actor, local-input/observation and command alphabets, each bounded-depth table has finitely many extensions. Include all syntactically possible local histories up to that depth, not one favorable run. Restriction preserves shorter safety/nonblocking verdicts. If every depth has a safe consistent table, the finitely branching tree has an infinite branch by the retained checked finite-extension theorem. Its union wins by the preceding argument. Physical state need not be finite for this existence proof; effective finite-prefix checks over an infinite state space need additional representation assumptions.

This compactness specialization is a written derivation from the checked tree lemma, not a newly mechanized table-tree construction. It gives classical existence, not a finite-memory bound or unrestricted terminating algorithm. Infinite command alphabets can defeat it, as the retained finite-fuel example shows. Unbounded eventual service is not prefix safety. Bounded service fits only through actual counter updates; omega-regular progress requires its own acceptance construction or applicable import.

## Concrete actual-effect adapter

[core_bridge.py](core_bridge.py) imports the existing finite causal Kernel unchanged. It applies local initializers to actual inputs, retains joint observations, masks compliant command/memory pairs, admits source faulty effects and advances actual service ages. Preparing the next observation consumes no extra physical interval.

Actual effect records retain issued compliant commands, actual delivery labels, original metadata and violations, and whether an effect occurred. The finite structured encoding preserves type distinctions; it does not replace history with an unattached good/bad flag. Sticky violation history is retained too. A consumer needing additional physical facts must put them in the source interface; an adapter cannot reconstruct an omitted source fact.

The instance check visits all 4,129 source nodes, 13,040 joint observation boundaries and 258,135 source effects of the retained all-threshold peer-brake implementation. It compares callbacks, masks, memory/service updates, independently recalculates speed and heat, and preserves all next joint observations. This is a factored correspondence check, not an enumeration of full histories or all expanded event states. The general proofs supply the run consequence.

Regressions cover absent calls, preexisting service age, missing observations/effects, correlated joint observations, ghost commands and local history. These diagnose interface obligations; they are not new physical benchmarks. The actuator probe uses a genuinely OFF invocation: a new ON command still pending in a queue is a different fact from no issued command.

The executed adapter fixes the selected initializer and policy. [APPLICATIONS](APPLICATIONS.md) now instantiates its field/run map on actual fallible-enactment and shared-device sources, with independent initialization, provenance, failure and cache-equivalence review plus complete selected-scenario correspondence records. Assembly.lean links the structural joined assignment to normalized source programs and actual steps, runs and nonblocking; initial-good and initializedBy obligations remain separate. [EXCHANGE](EXCHANGE.md) supplies the independently checked same-mission comparison. The final full-program audit and bound aggregate reproduction remain separate.

## Evidence boundary

The transformation is proved against the unchanged Execution module. Its observation/effect relations still need faithful instances. The finite source uses a strong current-command-aware adversary, fixed fault index, bounded actual effects and actual service counters. It establishes no external hydraulic, hardware or cryptographic calibration.

Existing execution, epistemic-tracking and local-refinement comparisons are recorded in research/THEORY and PROGRAM-SOURCES. Structural synthesis and handover have separate source assessments. A shared relation type cannot transfer their guarantees by itself; the maps, actual effects and consumer-specific verdicts constitute the assembly.
