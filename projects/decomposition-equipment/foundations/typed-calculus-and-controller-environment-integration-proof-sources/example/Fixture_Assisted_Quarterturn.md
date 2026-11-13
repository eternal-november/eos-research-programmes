# A controller recruits a corner to turn an object

## Plain language abstract

A gripper in this example can move an object sideways but cannot turn it in free space. A nearby corner can supply the missing pivot. The controller first seats the object against that corner, learns which direction to push, remembers that answer, pushes, and releases the turned object. Whether this works depends on more than the fact that the gripper, sensor and corner each behave correctly. They must refer to the same contact, and that contact must remain valid until the push finishes.

We specify the gripper, corner and object separately and derive their coupled executions. Under an explicit retained-contact assumption, the resulting controller safely completes a quarterturn and releases the object in three steps. A contact-only observation without retention is insufficient: the corner may slip during the push. Two separately correct contact descriptions may also concern different contacts, causing a wrong-direction push. These failures distinguish a usable witnessed decomposition from a list of individually plausible component descriptions.

This is a finite symbolic integration test, not a claim that a physical robot has been certified. Force, clearance, retention and sensing assumptions are declared below. It connects the original ordered typed calculus to one concrete staged dynamical interpretation; it does not discharge the whole research contract or introduce general robot-manipulation theory.

## 1 Independent local assumptions

The finite model is deliberately small enough that every open action and adverse mode can be inspected. It describes one keyed object, one translation-only gripper and a left- or right-handed corner fixture. Handedness is fixed but initially unknown to the controller. The fixture has two physically possible seating pads, numbered 0 and 1; either gives the same macroscopic pivot. A pad is a distinct local seating state, not an extra decorative duplicate of an otherwise identical execution.

The assumptions that a physical implementation would need to justify are:

1. **Gripper authority.** While holding the object it can advance, apply either of two signed lateral drives in an admitted force class, or release. It has no free-space rotation primitive. A released gripper cannot resume these actions during this task.
2. **Geometry and clearance.** Seating and the intended quarterturn have sufficient clearance. The fixture hand determines which signed lateral drive produces positive torque about the admitted pivot. The two seating pads obey the same macroscopic wrench rule.
3. **Force and object response.** Zero wrench preserves orientation; one positive pulse turns a flat object through one quarterturn. Negative torque, lost support, unsupported drive or a further positive pulse on an already turned object goes to a conservative damaged state. This finite response table is an assumption about a bounded operating envelope, not a derived rigid-body simulation.
4. **Contact retention.** A HOLD fixture preserves its pivot through the next admitted drive. A TOUCH fixture can either retain it or slip during that drive. No fairness assumption excludes repeated adverse choices.
5. **Sensing.** Approach returns the hand and the fixture's declared retention grade after the seating action. Subsequent pre-action sensing reports only clear versus engaged, not handedness, pad or orientation. The grade is a certified configuration fact, not a force measurement that proves future retention.
6. **Timing and ownership.** Each action uses the current contact state. Local updates commit together after the action. No unmodeled contact change occurs between ticks; the TOUCH slip branch explicitly models the relevant within-action loss. No component may read another's private register except through its named signal input.
7. **Task.** Initially the gripper holds a flat object at a clear fixture. A successful terminal state has quarterturned object, released gripper and clear contact. The model stops at that terminal state; it makes no claim about arbitrary subsequent commands.

The constants are symbolic classes. They do not assert numerical friction, torque, load or clearance bounds. These would be separate validation obligations for a real apparatus.

## 2 Local states and primitive tables

The gripper owns `g ∈ {held,released}`. The fixture owns fixed `h ∈ {L,R}`, fixed grade `k ∈ {HOLD,TOUCH}`, contact mode `c ∈ {clear,engaged}` and pad `r`. Clear means `r=-1`; engaged means `r=0` or `r=1`. The object owns `θ ∈ {0,1,bad}`. There are 72 compatible open states `(h,k,c,r,g,θ)`.

The open action alphabet is `approach, pushL, pushR, withdraw, wait`. All are retained before any controller is chosen, including unsupported actions and damaged states.

### Gripper primitive

Its table depends only on its own `g` and external action. For held grip, approach emits `advance`, pushL emits `driveL`, pushR emits `driveR`, withdraw emits `release` and changes its own register to released. Wait emits `idle` and preserves its register. At released grip every nonwait action emits `invalid` and preserves released grip.

### Fixture primitive

Its inputs are its own state and the gripper's command. Its outputs are its own next state, a wrench and a post-action reply. The table is:

- Idle preserves the fixture and outputs zero wrench and acknowledgment.
- Release clears contact and outputs zero wrench and released acknowledgment.
- Advance from clear chooses either pad, enters engaged mode, outputs zero wrench and reply `(contact,h,k)`. These are two actual alternative executions with different local target states.
- A drive from engaged outputs positive wrench precisely when its direction equals h, otherwise negative wrench, and retains the engaged pad. A TOUCH fixture additionally has a distinct slip record: it clears contact and outputs loss wrench and slip reply. A HOLD fixture has no such record.
- Every remaining case preserves fixture state and outputs invalid wrench and fault reply.

The fixture cannot inspect object orientation, grip register or controller memory. It does not implement an operation called successful rotation.

### Object primitive

Its only nonlocal input is wrench. Zero preserves θ. Positive sends 0 to 1. All other nonzero cases go to bad; bad is absorbing. It does not inspect fixture handedness, action, retention grade or controller memory.

### Acquisition and controller primitives

A deterministic acquisition has one actual record per whole source state and reads only c. The readable pre-action observation is `o=c`. The post-action reply is the fixture reply above. Different nominal pre/post types enforce their timing even when their payloads happen to coincide.

The controller is implemented by three separately specified mechanisms:

- A request initializer accepts one `quarterturn` request and sets memory to start. It neither selects hidden handedness nor reads the object.
- An action decoder maps start to approach, memory L to pushL, memory R to pushR, withdraw to withdraw, and done/reject to wait. Its only inputs are current memory and the permitted pre-observation; this decoder happens not to use that observation.
- A memory mechanism maps start plus `(contact,h,HOLD)` to h; any other start reply to reject; L or R after its drive to withdraw; withdraw after its action to done. It updates only after receiving the post-action reply. Done and reject persist.

Thus the controller has six named memory values. The handedness distinction is stored only between seating and pushing. The claim is that this controller works, not that six states are globally minimal. On the admitted HOLD initial set reject is unreachable. On TOUCH the safe implementation refuses the requested operation; it does not pretend refusal is task completion.

## 3 Deriving the whole from local records

The dependency order inside a tick is acquisition, action decoder or open action socket, gripper command, fixture response, object response, commit and controller memory update. These are the phases of the previously specified finite causal grammar, with the fixture reply as an explicit post-action wire. The object does not send an instantaneous response back to the fixture. Repetition uses the next tick's registers, not an algebraic feedback loop.

For each action a and source local-state tuple, enumerate the gripper record, each allowed fixture record matching its command, and the object record matching that fixture's wrench. The whole event is the ordered tuple of these actual records. Its next state consists of their local next states. This definition generates W; no correct whole behavior or pre-existing factorization is assumed.

To see the original typed path instance, use interface graph J with states c and edge records

    j = (c,c_next,a,command,wrench,reply).

The edge alphabet is the full product of the declared finite nominal sorts: 4,800 edges, not a subset inferred from successful runs. Source and target are c and c_next. Neither object orientation, grip, hidden hand, grade nor pad is smuggled into J's state. Only 25 edge labels are used by the compiled whole. J records the coordination protocol; it is not the controller's observation alphabet. In particular the controller does not receive the wrench wire or private fixture state.

Construct local graphs Dg,Df,Do over J. A Dg state is `(c,g)`; its edges admit every J label whose command and next grip satisfy the gripper table. A Df state is the fixture state; its edges are actual fixture records paired with a J label satisfying the fixture table. A Do state is `(c,θ)`; its edges admit every J label whose wrench and next orientation satisfy the object table. Coordinates not used by a local primitive are unrestricted cylinder coordinates, not extra sensor inputs. On the physical circuit, command routes gripper→fixture, wrench routes fixture→object and reply routes fixture→controller; no primitive receives the whole j tuple as an unrestricted read capability.

Each component is the loop color `J→J` with identical left and right graph map. The ordered profile is `[Dg,Df,Do]`; it is a genuine path-profile instance. The canonical operation witness

    δ : W → Dg ×_J Df ×_J Do

projects a generated execution to its local records. It is bijective on states and events: matching local records determine exactly one generated whole record, and every generated record provides such a tuple. The state bijection retains the fixture's h,k,r and the other two private registers. Acquisition has its own deterministic exact comparison; it is not inferred from a post-only factorization.

The executable check independently enumerates the full J alphabet and filters matching local cylinder edges, obtaining exactly the 396 generated whole action records. This checks open capability matching, not merely the controller's selected actions.

For a concrete original occurrence refinement, introduce composite color H with graph `Df ×_J Do`, primitive exact witness `H→[Df,Do]`, and exact witness `W→[Dg,H]`. Substituting the H occurrence yields `W→[Dg,Df,Do]`. The semantic substitution sends `(g,(f,o))` to `(g,f,o)`, preserving every actual primitive occurrence. More explicitly, also introduce GF with graph `Dg ×_J Df` and name the four exact primitive witnesses `a:W→[GF,Do]`, `b:GF→[Dg,Df]`, `c:W→[Dg,H]`, `d:H→[Df,Do]`. Impose the original presented equation `a(b,id_Do)=c(id_Dg,d)`, whose common input profile is `[Dg,Df,Do]`. It holds on actual state tuples and event records, not merely their observable values: both sides flatten to `(g,f,o)`. The checker retains the full J label and tagged local primitive record at every slot, including the actual fixture record, and checks both sides on all states and events. This supplies this example's concrete model of the original presentation. As a negative equation test, the pad-swap graph automorphism is also an exact local map and preserves every J label. Replacing just one branch's fixture witness by that automorphism changes its actual pad states and records. The two flattened operations then disagree despite equal visible labels; they cannot satisfy the declared equation. The checker verifies the automorphism on all local records, its involutive inverse, and the existence of disagreements. These are refinements of the same W, not replacement by a different plant. The bridge note gives the general original Calc interpretation and separates it from stronger exactness marking.

## The controller also has a typed decomposition

The controller is not supplied merely as an undecomposed correct policy. Its intrinsic graph K has the six memory states Q. For each current q, pre-observation o and future post-reply v it has exactly one complete tick record: action `a=choose(q,o)` and next memory `q_next=update(q,a,v)`. There are `6 × 2 × 8 = 96` such records. Enumerating future inputs in a complete record does not make them available when its action is selected.

Define an internal coordination graph J_C with states q and full edge alphabet

    (q,q_next,o,a,v,instruction).

Instruction is a nominal memory-write type with the same six possible values as Q. Three local loop colors over J_C give an ordered profile `[Select,Decode,Commit]`:

- Select permits exactly `a=choose(q,o)` and places no restriction on future v, instruction or q_next.
- Decode permits exactly `instruction=update(q,a,v)` and does not select a.
- Commit permits exactly `q_next=instruction`.

All three have the identity map on the SHARED interface state q. That does not mean each has its own memory or that Select holds q fixed: its graph admits every q→q_next edge allowed by its cylinder condition. There is one physical memory owner. Its old value is read before Select, Decode is evaluated after the actual reply, and Commit alone writes its next value. The other occurrences carry the bus state passively. This is a staged acyclic tick followed by graph-state iteration, not feedback added to the original planar syntax.

The exact operation witness `K→[Select,Decode,Commit]` maps each of the 96 records to its three tagged cylinder records. Conversely the matching tuple enforces exactly the three displayed equations, giving one K record. State comparison is the diagonal of the same owned q. Grouping Decode/Commit and substituting their marked occurrence gives the same witness by the original occurrence rule. The checker verifies the record pullback and separately verifies that for every q,o, changing v or future memory never changes Select's action.

K's internal interface includes controller-owned memory, not hidden environmental registers. To connect it to the environmental J, explicitly extend its states to `(q,c)` with `o=c` and extend each record by passive target-contact, command and wrench fields. Forget q on this extended graph's boundary legs to J. This produces 5,760 external controller records; it does not assert that forgetting q preserves the internal pullback. Indeed Select and Commit must not be separated into independent memory copies by forgetting their shared bus before composing them. A concrete countertuple uses Select with old memory L and action pushL, Decode with old memory R and reply ack (issuing withdraw), and Commit with old memory start writing withdraw. Each local cylinder record is valid and their public observation, action, reply and instruction agree. Here forgetting means coarsening the boundary used for matching while retaining the three actual local records, including their old-memory identities. Their old memories disagree, so this particular record tuple has no lift to the one-owner controller. If the records themselves are instead quotiented to public values, those values do have a consistent lift using old memory L throughout; that is a different construction and is not refuted by this counterexample. The checker verifies this countertuple. It is a failure of exact record reconstruction, not automatically a new unsafe behavior. In driver terms, hide the driver's internal state only after its request, decoding and memory mechanisms have been assembled consistently; hiding each mechanism's state first need not give the same driver.

Now couple this external K with the already derived open W by matching the same J record. The whole coupled state is `(x,q)`. Its events are exactly the local plant records whose action is `choose(q,x.c)`, with next memory `update(q,a,v)` for that very record's reply v. Thus refinement of K into the three mechanisms leaves the coupled graph unchanged, rather than merely preserving a successful endpoint. The checker verifies all 468 open coupled records, including unreachable and adverse states, not just the 12 reachable edges of the successful initial protocol. Initialization is the separate deterministic request primitive choosing start, independent of h.

For a SINGLE source-calculus parent admitting both refinements at identical boundary types, use the explicit common protocol graph I with states `(q,c)` and edges `(q,q_next,j,instruction)`. Lift the environmental colors by passively carrying q and instruction, and lift the controller colors by passively carrying the environmental contact, command and wrench coordinates. These are explicitly defined cylinder graphs, not an asserted general preservation law for retyping. The typed operation `[K_I,W_I]` describing the coupled whole then refines to `[Select_I,Decode_I,Commit_I,G_I,F_I,O_I]`. The controller-first and environment-first occurrence substitutions give exactly the same six tagged records. Matching their I labels imposes one shared action and one post-reply, not two independently chosen lookalikes. The resulting states are exactly `(x,q)` and its records exactly the 468 pairs of q with actual plant records having the selected action. The checker independently enumerates this common-interface join and compares it with the previously generated coupled set. No circular action dependence arises: Select ignores v, whereas Decode consumes v only after the plant returns it. The physical owner and read permissions remain those already specified; the larger coordination transcript does not grant its passive fields as sensor inputs.

## 4 A derived guarantee

**Proposition.** On the two initial states with grade HOLD and unknown h, the controller is nonblocking, avoids bad and reaches the terminal task goal in at most three actions, for every actual seating-pad choice.

**Proof.** At start, approach is enabled. Its local gripper record preserves held grip, each fixture record seats at one of the two pads with zero wrench, and the object preserves orientation 0. The post reply sets controller memory to the actual fixed h. No future observation was used to choose approach.

At the next action, memory chooses drive h. The same fixture state that supplied the reply is still engaged. HOLD excludes the slip record; hence every compatible fixture response has positive wrench. The object response is therefore 0→1 while the gripper remains held. The memory becomes withdraw. At the third action the gripper releases, the fixture clears, and zero wrench preserves θ=1. The task goal holds and memory becomes done.

Every step has at least one actual matching primitive tuple, so this is whole-system nonblocking, not separate component enabledness. All local alternatives were included. The rank values start=3, L/R=2, withdraw=1, done=0 strictly decrease along every reachable nonterminal edge. Therefore there is no infinite nongoal run and no fairness premise is needed. ∎

The exhaustive checker finds 12 reachable state-memory pairs and 12 closed-loop edges, including both hands and both pads. There are two terminal states, one per hidden hand; the earlier pad choice remains in the execution record even though release clears the pad register.

This guarantee is stronger than checking a completed input-output truth table. It preserves the intermediate contact state, the occurrence supplying the sensed hand, the adverse open actions, the controller's temporal information restriction and the exact local execution multiplicities. A macro-operation that simply maps flat to quarterturned would omit those obligations. The finite proof itself uses ordinary transition-system reasoning; the contribution of the integration is that these obligations are derived and transported through the typed witnessed presentation rather than supplied by an assumed solved whole.

## 5 Four distinct failures

### A fixture-free gripper has no rotation capability

For the explicitly absent-fixture alternative, idle, advance and release return zero wrench; drives and invalid commands return invalid wrench. This local table has no positive wrench record. Starting flat, the object's orientation therefore remains 0 or becomes bad under every action sequence, and cannot reach 1. The checker explores the full reachable open graph of this alternative. The controller can achieve the task only by recruiting the environment's pivot. This is not proof of a decomposition-search algorithm; it is a checked distinction between the supplied fixture-free and fixture-assisted candidates.

### The next action cannot use a forgotten past reply

After seating, pre-observation is engaged for either h. Safe progress requires pushL for h=L and pushR for h=R; the sets have empty intersection. A deterministic memoryless controller receives the same engaged observation in both cases. Pushing chooses a wrong direction for one case; approach in engaged mode faults; withdraw before turning loses the ability to finish; wait forever violates sure reachability. Thus no memoryless controller on this observation interface solves both initial hands. More specifically, even if an external sequencer supplies the correct protocol phase for free, the push phase still has identical current observations in the two cases and opposite required directions. A controller with phase but no retained information distinguishing h therefore cannot solve both. This isolates the handedness memory requirement from the separate need to sequence actions. The memory mechanism is a genuine required resource under these fixed action and sensor assumptions. An independent exhaustive fixed-point check of all 25 memoryless action maps from the two pre-observations finds none that safely reaches the goal from both initial hands.

### A contact observation is not a retained contact capability

If a wrapper forgets grade and exposes only `(contact,h)`, HOLD and TOUCH seating records have identical visible replies. On TOUCH, even the correct next drive has a slip execution reaching bad. The local gripper, fixture and object tables remain valid; the error is treating evidence of earlier contact as a guarantee that the same pivot remains throughout the drive. A sound summary must retain the adverse execution or require the HOLD condition. This is failure of the proposed retained-contact interface contract, not a theorem that every interface forgetting grade is structurally invalid.

### Separate contact descriptions need not describe one contact

If the sensing branch uses a contact with hand hs and the mechanics branch an independently chosen contact with hand hm, each branch can obey its own table. The controller drives hs; when hs≠hm the actual object receives negative wrench and is damaged. Of the four pairs, two fail. Their coupling is not a refinement of the original one-contact occurrence: it has changed what is shared.

Even when both contacts have equal handedness, duplicating a physical seating invocation is not exact occurrence preservation. One shared two-pad invocation has two aligned records `(0,0)` and `(1,1)`; two independent invocations have four pairs, including off-diagonal pairs. Those extra pairs violate the proposed witness bijection. Equal visible values alone do not erase this distinction. This latter multiplicity defect is not claimed to be unsafe by itself; the physical effects and the exact-record claim are separate acceptance tests.

## 6 Evidence and limits

Run `python check_fixture.py` in this directory. The script uses only Python's standard library and writes its machine-readable result to stdout. `check_fixture_results.json` records the checked result. It checks open tuple equality over the independently declared full boundary alphabet, occurrence reassociation, every reachable controller execution, the rank, and the four negative constructions.

Source bridge: the original Calc interpretation and exactness conditions are provided in the integration theory note. Dynamic semantics and timing are inherited from `persistent_decomposition_20261026/control/Causal_Implementation_and_Control_Transfer.md`, especially Sections 1–5. There is no claim of continuous dynamics verification, empirical robot validation, unbounded controller synthesis, arbitrary parallel or feedback syntax, or new general manipulation theory.
