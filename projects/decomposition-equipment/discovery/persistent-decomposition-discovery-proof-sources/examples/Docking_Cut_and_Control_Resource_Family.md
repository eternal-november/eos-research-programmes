# Dynamic docking cuts and permitted sensing

## Plain-language abstract

A small docking machine passes through several binary orientation-changing mechanisms. To dock safely, the controller must compensate for their combined orientation. We ask which mechanisms should belong inside the robot's subsystem, rather than fixing that boundary first. Moving a mechanism inside reduces the number of external wires needed, but does not magically make its internal state visible to the controller. This gives an exact tradeoff between subsystem boundary size and installed sensing.

Every description that omits at least one mechanism has an exact decomposition into an apparently independent nondeterministic robot and the remaining mechanisms. Those local component descriptions agree on their actual exposed records. Nevertheless the complete machine does not have that zero-signal independent decomposition: recombining its purported component transitions introduces impossible docking outcomes. This is a useful failure test for a reconstruction theorem, but its parity and conditional-independence mechanisms are standard. The separate temporal-cycle example supplies the stronger time-refinement obstruction.

## 1 The actual finite plant

Fix n>=2. Robot status q is ready, goal, or crash. Mechanism states are y=(y_1,...,y_n) in {0,1}^n. Each mechanism is a serial orientation inverter, so total orientation is parity(y)=XOR_i y_i. Mechanism n is protected external infrastructure and cannot be included in the candidate robot subsystem.

Actions are wait, dock0, and dock1. The next robot status is

* q'=q if q is goal or crash;
* q'=ready for wait from ready;
* q'=goal for docku from ready if u=parity(y), and crash otherwise.

After each action the mechanisms independently choose arbitrary next states e in {0,1}^n. The whole event record is the literal tuple (q,y,a,e), with target (q',e). Distinct resets remain distinct physical events even if the robot outcome agrees. This is a finite adversarial model, not a stochastic independence claim or an empirical model of a particular robot.

All bits matter to docking. The raw-port convention is physically specific: each external mechanism exposes its own current orientation pin; no installed device computes a combined parity signal. Adding such a device is an explicit capability change, not an allowed free preprocessing operation.

## 2 Locally exact decompositions that fail globally

For a proper subset H of mechanism coordinates, the partial description V_H retains q, y_H, the action, q', and reset records e_H. It is the literal image of whole states and events under these maps. These are abstractions, not asserted Cartesian restrictions of the original event graph.

Because at least one current mode is omitted, both docking outcomes are possible for every retained source mode tuple and every dock command. Thus V_H factors exactly as

    loose robot T × retained mechanism context C_H,

where T has one wait event preserving ready, two events from ready for each dock command (one to goal, one to crash), and one self-loop per action at goal and crash. The mechanism context has all reset events y_H->e_H. The factorization is the literal separation of the record coordinates (q,a,q') and (y_H,a,e_H), synchronized on the supplied action. It is not merely equality of transition counts.

For all single-omission views, the T coordinate extracted from the SAME actual whole event is the same tuple (q,a,q'). State and event anchors therefore agree. However T paired with the complete context has both docking outcomes for every complete current mode y; the whole has exactly one. The spurious outcome cannot be removed by an invisible shared selector without introducing an unpermitted interaction.

There are 9*4^n whole events and 11*4^n events in the unrestricted product. All 2*4^n extra events project into valid events of every single-omission view. Thus even the conjunction of all those local transition descriptions fails to reconstruct the actual correlation. This is a structural transition-factor failure, not yet a controller failure.

## 3 Discovering a proper subsystem boundary

Choose J subset {1,...,n-1}. The unknown subsystem consists of robot q and mechanism states y_J. Its context consists of K={1,...,n}\J. The protected mechanism n ensures K is nonempty, so selecting the whole is excluded.

The declared boundary may expose a chosen subset B of the raw context pins K. The subsystem state carrier is exactly (q,y_J); it receives the action and y_B. It does not secretly read the remaining context state. The context retains its state and reset event. An exact dynamic factor requires an event bijection from the whole to the independent product of those component events, synchronized only on the declared action and boundary values, respecting the literal state cut and source/target maps. In the graph-interface formulation, J has one state and one loop for every pair (a,b) of action and exposed raw-pin tuple. The context labels its event by (a,y_B), and the subsystem labels its event by (a,b). The physical timing convention says b is available before the control action; that availability is not inferred merely from a graph label.

### Theorem 1 Raw boundary criterion

This exact dynamic factor exists if and only if B=K.

If B=K, the subsystem event is (q,y_J,a,y_K,e_J), with the robot target computed from the complete parity and local next mechanism state e_J. The context event is (y_K,a,e_K), exposing y_K. The pair uniquely reconstructs (q,y,a,e), and conversely. Therefore actual state/event factorization is exact for arbitrarily many steps.

If j in K\B is omitted, take two complete current states that differ only at y_j. Their component state, action, and boundary values are identical, but the safe docking outcome is opposite. Any candidate subsystem event family covering both actual whole events must contain both robot outcomes at that same component source/interface. Independent recombination with the first context event then creates the wrong outcome. Removing that event would lose the second actual whole event. Additional nondeterminism or duplicate component records cannot avoid this support-level contradiction. ∎

The result is not merely a count of wires assumed necessary: event recombination derives the necessity. With B=K, the decoder and all reset records are explicit. No arbitrary whole-dependent matching is allowed to carry the missing pin.

## 4 A persistent factor is not necessarily controllable

For a valid cut, suppose the controller observes q and the boundary pins y_K, together with installed internal raw sensors y_L for L subset J. Internalizing a mechanism does NOT automatically grant a sensor. Its physical dynamics is part of the subsystem, but controller access is separately specified.

The objective is sure safety (never enter crash) and eventual goal from every initial mode tuple with q=ready. Waiting forever is not success.

### Theorem 2 Observation and control criterion

A controller, even with arbitrary finite or infinite memory, achieves this objective exactly when L=J.

If every mode is observed, select docku with u=parity(y); the next status is goal, regardless of the subsequent resets.

If an internal mode is unobserved, both its values are compatible with every observed history before docking. Waiting reveals no information about it: the mechanisms can reset adversarially, and all observed coordinates can be kept equal on two histories with opposite hidden parity. At the first docking action of any proposed controller, choose those two histories. The controller selects the same action, so one run crashes. If it never docks on such a history, eventual progress fails. The same reasoning excludes a sure guarantee from randomized controllers. ∎

The proof uses the special reset family to cover arbitrary history-dependent controllers. It is not a general claim that memory never helps under partial observation. The temporal-cycle example exhibits the opposite situation.

### Corollary 3 Exact cut and sensor resource tradeoff

Let k be the maximum number of raw boundary pins and l the maximum number of internal raw sensors. A permitted proper subsystem with an exact dynamic factor and a sure safe-progress controller exists if and only if

    k>=1 and k+l>=n,

for nonnegative integer budgets. The candidate J must satisfy n-|J|<=k and |J|<=l, with |J|<=n-1. Those inequalities have a solution exactly under the displayed conditions. A witness is any J with max(0,n-k)<=|J|<=min(l,n-1), its literal state/event factorization, and the parity controller.

For n=3,k=2,l=0, cuts J={1}, J={2}, and J={1,2} all yield persistent dynamic subsystems, but none is controllable under the given telemetry. Adding one internal sensor and choosing J={1} gives an exact proper subsystem with two boundary pins and a controller that docks in one step. This is boundary DISCOVERY, not verification of a supplied single cut.

A permitted internal parity sensor can reduce the number of internal readouts; a permitted external aggregator can reduce raw boundary wires. Neither exists in this initial language. Their addition is a stated physical repair with a changed resource theorem, not a refutation of the raw-port result.

## 5 Evidence and limits

`check_docking_cut_discovery.py` verifies all proper-coordinate images and all declared raw cut/boundary subsets for n=2,3,4 by direct event-set equality. It checks the observation criterion on 508 mode-observation subsets and the resource theorem on 280 budget pairs for n=2..8. Its JSON output includes the full three-mode docking truth table.

The raw parity mechanism, information lower bound, and sure-control argument are established elementary mechanisms. This family is a sharply checkable benchmark for the integrated decomposition question, not independently a claim of new control theory. Its independent-reset dynamics does not by itself show the stronger temporal-persistence phenomenon; use the cycle family for that. No continuous robot, stochastic controller, or empirical performance claim is made.
