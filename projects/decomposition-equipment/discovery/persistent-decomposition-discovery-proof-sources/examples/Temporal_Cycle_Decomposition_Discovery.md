# Persistent component discovery across temporal descriptions

## Plain-language abstract

A description that samples a machine once per cycle can exhibit a clean component that does not exist at the machine's actual step-by-step time scale. The smallest example here has four states: a two-position transport mechanism changes a binary orientation on every second movement. At the coarse scale, position stays fixed and orientation toggles independently. At the fine scale, there is no autonomous two-state component compatible with the specified position context, even if we are allowed to discover its update law and its state coordinates. Every individual movement, and every proper selection of movement types in the larger family, nevertheless has an exact decomposition.

The obstruction is a permutation-root condition around a loop. This is a standard algebraic mechanism, used here as a diagnostic for decomposition discovery and temporal refinement, not claimed as a new theorem of permutation theory. A real boundary signal indicating the twisting movement repairs the component model. A controlled variant distinguishes an unavailable current signal from a signal observed earlier: a one-bit controller memory can compensate for a hidden twist and safely complete transport; a memoryless controller cannot. The example therefore separates coarse-time discovery, genuine persistent decomposition, permitted interaction, and causal controller realization.

## 1 Model and declared decomposition class

Fix a station cycle of length m>=2 and a d-element orientation carrier D with d>=1. The actual whole has states

    X = Z/m × D.

There is one advance event at each state, and its target is

    F(i,x) = (i+1, a_i(x)),

where every a_i is a permutation of D. The event record is its actual source state (i,x); it is not an unrecorded transition choice. The context C is fixed: its states are Z/m, and advance takes i to i+1. The context projection X->C is the literal first projection.

We seek an EXACT autonomous d-state component T and a state/event product factorization over this fixed context. The component states are an abstract carrier S of size d, not a preselected coordinate function of x. No phase signal crosses the component boundary. Its transition event set is initially allowed to be an arbitrary finite directed multigraph. Factorization means a bijection of states over C and a bijection of actual transition events with product events, commuting with source and target. Each context advance has one event.

This is a declared cut class, not a claim that the whole lacks every conceivable decomposition. Increasing the component state carrier, changing the context, adding a boundary signal, or adjoining physical controller memory changes the problem and must be stated explicitly.

### Lemma 1 Exactness removes the nondeterministic escape

Any such component T has exactly one outgoing event from every state, and its state update is a permutation sigma of S.

Proof. For any component state s and any context station i, the corresponding whole state has exactly one outgoing event. Its product source fibre is the component source fibre at s times the singleton context source fibre at i. Its cardinality is therefore one. Thus T has exactly one outgoing event at each s, defining sigma. The whole update and the context update are bijections. If sigma(s)=sigma(s') with s!=s', product states (i,s) and (i,s') would have the same target, contradicting injectivity of F. Finite injectivity gives bijectivity. Parallel invisible events, missing events, and nondeterministic alternatives cannot be hidden by an exact event bijection. ∎

Choose an identification S=D only for calculation. A state factorization over C is exactly a family of permutations p_i:D->D, interpreting the component state as p_i(x). Event compatibility is

    p_(i+1) a_i = sigma p_i.                         (1)

No p_i, sigma, or compatible factorization is assumed as input. They are the unknown decomposition.

## 2 Exact classification by loop transport

Write H=a_(m-1)...a_1 a_0, where function composition is read right to left.

### Theorem 2 Unknown autonomous factor criterion

An exact d-state autonomous factor over C exists if and only if there are permutations sigma and p_0 such that

    p_0 H = sigma^m p_0.                            (2)

Equivalently, H is conjugate to an m-th power in the symmetric group on D. Every solution pair (sigma,p_0) determines a unique full factorization by

    p_(i+1) = sigma p_i a_i^(-1).                   (3)

Proof. Multiplying (1) around the cycle gives (2). Conversely use (3) for successive phases; equation (2) says exactly that the final value p_m equals p_0. These permutations give a state bijection over the context and satisfy (1). The event bijection sends the unique actual event at (i,x) to the unique context event at i and component event at p_i(x); equation (1) verifies its target. It is a bijection because the state map is. Lemma 1 proves that no additional nondeterministic component has been missed. ∎

Component-coordinate relabelings act by conjugating sigma and left-composing every p_i. Those are comparisons of solutions, not identifications of distinct actual whole events. The result is a finite classification of the declared factorization family, not a claim about every model of the same traces.

### Corollary 3 Binary even-cycle obstruction

Let D={0,1}, a_i(x)=x XOR t_i, and let m be even. Then an autonomous two-state factor exists exactly when XOR_i t_i=0.

Both permutations of two states have even power equal to the identity. Therefore odd total twist cannot satisfy (2). With even total twist choose sigma=id and solve (3). For odd m, by contrast, every binary twist table admits a factor: choose sigma to have the same parity as H. The odd-m case is an important negative control against claiming that any twist obstructs all two-state dynamics.

For every proper subset E of cycle edges, the restricted whole W_E DOES factor as the identity component times the correspondingly restricted context C_E. Deleting at least one edge breaks all directed cycles, so choose a gauge freely at the start of each path and propagate p_(i+1)=p_i a_i^(-1). Isolated station fibres also have free gauges. The event bijections remain exact. Thus every proper local temporal description passes while the entire even odd-twist cycle fails. Consequently, tests that examine at most a fixed number k of primitive cycle edges at a time cannot detect every member: choose an even cycle with more than k edges. Equivalently, use one chart per primitive edge and inspect only unions of at most k such charts. This is not a lower bound on the number of arbitrary charts: two larger proper charts whose union covers the cycle can expose the obstruction when their actual overlap agreement is checked.

## 3 Minimal four-state example

Take m=2, D={0,1}, a_0=id, a_1=swap. The actual events are

| Source | Target |
|---|---|
| (0,0) | (1,0) |
| (0,1) | (1,1) |
| (1,0) | (0,1) |
| (1,1) | (0,0) |

The whole is a four-cycle. Its context is a two-cycle. An exact component must be either the identity or the swap on two states, so the product update has order at most two. The whole has order four. This proves failure for every allowed component update and every state-coordinate choice over the context.

Physical reading: station 0 transports a binary orientation unchanged, while station 1 reverses it. The task is to identify a phase-independent autonomous orientation component while retaining station as a separate context. The failure does not say that orientations cannot be tracked, that the machine cannot be controlled, or that a phase-dependent open component cannot be defined. It says precisely that this requested autonomous spatial cut is not persistent at the given time resolution.

## 4 Coarse temporal discovery does not lift to fine time

Keep all original states and consider the m-step system W^[m]. Its events are the actual ordered paths of m primitive events. Because the whole is deterministic, each source state has one such path; no internal event identity must be erased. Its context C^[m] returns to the same station.

Let A_i=a_(i-1)...a_0, with A_0=id, and put p_i=A_i^(-1). The m-step orientation update at station i is A_i H A_i^(-1). Consequently the maps p_i make W^[m] exactly the product of stationary context and the autonomous component update H.

Thus every whole in this family has a coarse-time factor. In the binary even odd-twist cases, that factor does not lift to any autonomous two-state fine-time factor over the same context. For the minimal example, the two-step model is simply

    (i,b) -> (i,b XOR 1),

which is an exact product under the original state coordinates.

The obstruction concerns respecting the internal temporal cut of a composite event. It is not necessarily caused by discarding the internal event records: even retaining the whole two-event path, an endpoint-level product factorization need not split through the original intermediate interface. If a practical coarse observation also discards those records, that is an additional information loss, not needed for this counterexample.

## 5 A sharp positive test from multiple time scales

### Proposition 4 Coprime sample reflection for one anchored cut

Let X be a nonempty finite state set, F:X->X a permutation, and fix ONE state bijection phi:X->S×C with nonempty factors. Suppose that, under this same phi,

    phi F^r phi^(-1) = sigma_r × gamma_r,
    phi F^s phi^(-1) = sigma_s × gamma_s.

If gcd(r,s)=1, then F itself has an autonomous product factor under phi. All four factor maps are permutations. Pick integers u,v with ur+vs=1. Then

    phi F phi^(-1)
      = (sigma_r^u sigma_s^v) × (gamma_r^u gamma_s^v).

Proof. Bijectivity of each product and nonemptiness of the factors imply bijectivity of each factor map. The two sampled whole maps commute, so their factor maps commute. Apply Bezout's identity to powers of F and separate the product coordinates. Event factorization follows for deterministic systems with their unique actual path records. ∎

For a finite family of sample lengths, the same argument recovers F^g where g is their gcd. The odd-twist even cycle with sampling length m shows why knowing only a nonunit-gcd time scale need not recover the fine factor. This does NOT assert that every instance with g>1 fails.

The same anchored cut is essential: separately discovering unrelated decompositions at different sampling scales does not supply the common phi required by the proposition. Establishing that agreement is a decomposition-reconstruction problem. The negative powers are a mathematical proof device; this argument does not compile a physical reverse-time operation or license an unavailable inverse actuator.

Reversibility is also essential. For this separate counterexample use coordinates (s,c) on X={0,1}×{0,1}, with the SECOND coordinate c the fixed context projection. Define

    F(0,0)=(0,0),  F(0,1)=(0,0),
    F(1,0)=(0,1),  F(1,1)=(0,0).

Both F^2 and F^3 are the constant product map to (0,0), yet F is not a product under the original cut: its second-coordinate output at context 0 depends on the first coordinate. It cannot factor over the same literal context projection under any fibrewise coordinate relabeling, because the two states over context 0 have different next context states. The transient correlation is invisible at both coprime coarse scales.

## 6 Permitted interface and controlled repair

### 6.1 Physical phase signal

Give the orientation component the actual boundary signal t_i indicating whether the current station twists it. The component is now the open transducer

    (b,t) -> b XOR t.

The context emits t_i and advances station. Their literal state and event synchronization reconstructs W exactly, with no dependence on unexposed phase. For binary twists only one signal bit is needed. This is a different, explicitly less autonomous component class. The repair is physically available only if this signal is actually supplied by an installed port or a permitted interface circuit. Merely writing t_i as a mathematical function of the context does not supply a wire.

### 6.2 History-sensitive compensation

There is a separate controlled variant. The whole has a fixed but initially unknown mode h in {0,1}. All movements except the last preserve b. At the last station, the actuator accepts compensation c in {0,1} and updates

    b' = b XOR h XOR c.

The mode h remains unchanged. The controller receives h only on arriving at station 0, and receives the station index thereafter; it does not read b or h at the last station. Before the last station its only action is advance. At the last station it must select c and advance. These restrictions exclude storing h in a different physical command or an unreported plant channel.

Start a transport episode at station 0 with b=0. Safety is b=0 throughout the episode; progress is completing the m advances. A two-state controller stores the observed h and later selects c=h. It completes in m steps and preserves b. For the structural conclusion, let z be the controller memory and define the calibrated context domain I by: at station 0, either z is allowed; at every station i>0, require z=h. The station-0 acquisition sets z:=h before leaving, and later movements retain z. This domain is forward invariant. On the enlarged state carrier I×{0,1}, allowing BOTH values of b, the closed-loop update is exactly context-update × identity-on-b, and its actual event factorization is literal. The initial task states with b=0 and any fixed initial memory lie in this domain. This does NOT assert an identity factor on every arbitrary plant/controller-memory state: a last-station state with z!=h lies outside I and can flip b.

No memoryless controller using only the stated current observation succeeds for both h values. Its observation at the last station is the same, so it chooses one c; the other h gives b'=1. Without the early sensor, no amount of deterministic controller memory helps, since the entire predecision observation/action history is identical for h=0 and h=1. Randomization cannot give a sure guarantee either.

This repair adds a real controller and restricts the plant's permitted input behavior; it does not prove that the uncontrolled whole already had an autonomous factor. The one-bit memory is a specified physical resource, not a ghost state silently adjoined to the old decomposition. The mechanism of delayed observation and memory is standard partial-observation control; its role here is to make the required interface implementation causal and explicit.

## 7 Executable checks and scope

`check_temporal_cycle_discovery.py` and its JSON output check 508 binary edge tables (m=2..8), 501 proper edge views, 252 ternary edge tables (m=2,3), the macro-time factor, and the stated bounded-memory repairs. For binary m<=5 and all ternary cases, a direct search over all gauge families and component permutations agrees exactly with the root criterion. The minimal case separately rejects all 16 binary transition relations under all four context-preserving state bijections, including nondeterministic and partial relations. The source/event proof above additionally excludes arbitrary parallel records, which relation enumeration alone cannot test.

These are finite tests supporting the proofs, not Lean verification or a priority claim. The main family is reversible and synchronous. Asynchrony, variable durations, stochastic guarantees, arbitrary feedback networks, and physically realizable inverse circuits are not asserted. The component and context sizes, context projection, and allowed boundary signal are part of the declared search class.
