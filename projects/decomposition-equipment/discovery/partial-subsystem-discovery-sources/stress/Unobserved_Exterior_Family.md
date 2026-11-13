# A local subsystem with an arbitrarily large unobserved exterior

## Purpose and scope

This family tests whether a useful local mechanism can be discovered while the surrounding system is not reconstructed and has no prescribed state-count bound. It includes a genuinely interacting two-coordinate core, a delayed input port, a misleading observed coordinate affected by an unobserved bypass, and nonlinear feedback into an arbitrarily large exterior. The local sensor bundles do not identify components one-to-one.

The positive identification result uses an explicit recorded randomized regime. This is additional experimental information, not a consequence of passive readouts alone. It changes an unobserved exterior influence after the current ports have been emitted; it neither resets the local state nor reveals component membership. The exclusion and excitation conditions must be part of the declared experimental universe. A passive indistinguishability example below shows why some such restriction is necessary.

## 1. Growing family

For any N>=2 let the unobserved exterior have bits H=(h_1,...,h_N). The accessible input port is v=h_1. There are observed local latent bits a,b,y, an unrelated port w, and a one-tick register v_prev. The candidate sensor bundles are

    P1=(a,b,y), P2=(b,v), P3=w.

Their internal coordinate assignments and sensor matrices are not given to the learner. Three conditionally independent categorical sensors per bundle have strictly positive full-column-rank emission matrices. The first two bundles have unknown latent cardinalities eight and four; all sensor alphabets may have ten symbols. A selected task sensor has probability .2+.6a of returning one, but its relation to the recovered latent coordinates is also learned.

At each tick, the current port v is emitted first. Then a regime R in {0,1} is drawn independently of the entire past, with both probabilities positive, and recorded. An unobserved exterior bypass Z is drawn with

    P(Z=1 | H,R)=.15+.10 h_N+.35R.

The fresh local updates, independent conditional on the old state and Z, are

    P(a'=1)=.10+.10a+.15b+.20v_prev+.05ab,
    P(b'=1)=.15+.10b+.20a+.15v+.05av,
    P(y'=1)=.10+.10y+.10a+.10v+.40Z.

Set v_prev'=v and draw w' independently with probability .4 of one. The exterior itself updates using independent fresh noise conditional on Z:

    P(h_1'=1)=.10+.15h_1+.10h_2+.15Z+.10a,
    P(h_i'=1)=.15+.15h_i+.10h_(i+1)+.10a+.05h_i h_(i+1), i>=2,

with h_(N+1)=h_1. All fresh probabilities are strictly between zero and one. The core has nonlinear feedback; the exterior receives feedback from a, affects the port v and the decoy y, and can share fresh randomness between those two effects. The exterior is not a collection of independent irrelevant decorations.

This finite instance has a unique stationary law: after two ticks every compatible register state has positive probability. No global matrix is needed to describe or simulate its local rules. More generally the positive local conclusion below allows the exterior to be any causal process, including one with an arbitrarily large or infinite hidden state, provided the core mechanism and admitted port contract are retained.

## 2. What the recorded regime identifies

Let C be any pre-regime covered-history context. Since R is randomized after C, the conditional distribution of H given C is the same at R=0 and R=1. Therefore

    E[Z | C,R=1]-E[Z | C,R=0]=.35.

When C fixes a,b,y,v,v_prev, the conditional next-law differences are exactly

    P(a'=1 | C,R=1)-P(a'=1 | C,R=0)=0,
    P(b'=1 | C,R=1)-P(b'=1 | C,R=0)=0,
    P(y'=1 | C,R=1)-P(y'=1 | C,R=0)=.14,
    P(v'=1 | C,R=1)-P(v'=1 | C,R=0)=.0525.

The hidden exterior posterior cancels. Neither its state alphabet nor its transition rule is learned. The decoy and the incoming port are exterior-affected; the core update is not. Conditioning on a post-regime variable would invalidate this argument by selection, so the timing is part of the type.

A useful general scalar lemma is the following. Suppose a local next-state law at covered context c is K_0(.|c)+z Delta(.|c), independent of exterior history except through z. If a randomized pre-update probe shifts P(z=1|exterior history) by at least gamma>0 in a common direction at every history, then its observed next-law change is Delta(.|c) times a scalar at least gamma. Invariance therefore forces Delta=0; a nonzero change gives a quantitative leakage witness. The response vector Delta may have both positive and negative outcome entries; the common-direction requirement concerns the scalar mixing shift. The conclusion fails if hidden histories have differently signed response vectors that cancel, if there are unprobed bypasses, if the regime directly changes the local mechanism, or if the regime is confounded with the old exterior.

Thus the resulting certificate is conditional on an exclusion/probe-completeness contract. It does not discover that contract from arbitrary observational data.

## 3. Unsupplied local coordinates and boundary discovery

Three-view calibration first identifies each finite patch alphabet and its sensor channel up to a label permutation. Static overlaps between P1 and P2 expose b, but do not separate a and y within the remaining four-state fiber. On any covered old context that includes a,b,y,v and v_prev, the next P1 law is still a product:

    Bern(p_a) x Bern(p_b) x Bern(E[p_y | C,R]).

This remains true despite arbitrarily complicated hidden exterior memory: only y in P1 is directly affected by the hidden current mixture, and a',b' use independent fresh noises with context-fixed probabilities. Conditional product tests across contexts recover the private product coordinates under the same finite separation conditions as the preceding local-atlas theorem. Regime effects then distinguish the stable private coordinate from the leaky one. A task-sensor conditional distribution that is constant precisely on a-fibers identifies the task anchor without giving its hidden labels to the learner.

This family does NOT justify minimizing the conditional entropy of the entire patch over a bounded history and declaring the minimum equal to conditioning on the whole exterior history. The decoy's conditional mean can retain arbitrary exterior memory. Instead the family supplies a direct product-row and probe-separation argument for the stable coordinates. General discovery without this product-mixture property is a separate theorem obligation.

The essential dependencies of the stable pair are

    a' : a,b,v_prev;   b' : a,b,v.

They are found from the recovered finite conditional rows by testing which arguments can be omitted. Strict positivity provides supported contrasts. No exterior state is required. The smallest retained local group containing the a task anchor and using only one existing incoming binary port is {a,b}, with port v and its one-tick delay memory. If b were left outside, the a mechanism would require both b and v under that existing-port contract.

This is not a universal bit-communication lower bound. Allowing arbitrary boundary preprocessing, a different alphabet, extra return messages, random simulation at the boundary, or another timing convention can change the comparison. The admissible existing-port contract must be stated rather than smuggled into a memory count.

## 4. Exterior ambiguity and joint realization

Once the local update K(a',b'|a,b,v,v_prev) is identified as independent of the bypass, any causal exterior may provide v_t as a function of its history and past core outputs. The joint process is constructed sequentially: the exterior supplies the current port; the core samples a',b' from K using its own fresh noise; the shared delay register is updated to v; the exterior advances using its permitted feedback. The kernel normalization at each step gives a positive joint path law. No exterior state enumeration is involved.

The claimed uniformity is over exterior replacements connected through the admitted port and preserving the local mechanism. It is not over interventions that secretly add a new wire into a or b, change their kernels, or expose their latent states to the robot. Different exterior systems may have identical port behavior, or different port behavior that the same open core accepts. Neither requires a unique hidden exterior ontology.

The one-bit delay can be stored in the boundary or in the source's retained state. The two full executions are related by a register-ownership bijection. That bit is charged once. The identified latent core is a generative model; noisy sensors still require filtering for real-time control.

## 5. Why passive fitting is insufficient

Let an observed bit Y' have probability .2+.4Z, with unobserved fresh Z~Bern(.5). Its observable path law is exactly that of an autonomous IID Bern(.4) bit. Add the same independent sensor noise to both worlds: every finite and infinite observation law still agrees. In one world there is no exterior edge; in the other there is an exterior bypass.

Replacing the bypass process by IID Bern(.1) or Bern(.9) changes the second world's output probability to .24 or .56. It leaves the autonomous world's .4 unchanged. No passive amount of data from the original regime can determine which replacement guarantee holds.

Likewise, an unprobed hidden input can be appended without changing any tested regime comparison. Passing invariance tests does not certify the absence of such a variable outside the declared probe-complete universe. The positive result identifies a well-behaved subsystem under an explicit experimental and compositional contract, not by treating empirical stationarity as causal insulation.

## 6. Verification scope

The accompanying numerical fixture uses a small whole-state model solely to generate stationary observable probability tables and independently check the learned laws. The discovery calculations use noisy sensor tables, not latent samples or the exterior transition matrix. The all-size statements above are analytic; a small finite check is not their proof. No finite-data implementation, physical experiment, or Lean verification is claimed here.

### Reproducible exact-law results

Run `OPENBLAS_NUM_THREADS=1 python check_unobserved_exterior.py`.

For N=2, N=3, and N=5, the oracle has 128, 256, and 1024 whole states respectively, but the learner's four-sensor/time observable table has the same 20,000 entries. The learner calibrates unknown 8- and 4-state alphabets from noisy three-view tables, aligns their two overlap fibers, and enumerates all 576 binary-by-binary charts of the private four-state fibers. Exactly eight survive (the two true private factors, up to swap and flips). The nearest rejected chart has a product-row residual above .089. The leaky coordinate has regime gap .14; the **joint** retained two-coordinate law has gap below 9e-16.

The learner then tests all four binary port quotients compatible with the overlap fibers. Exactly two survive, representing the same port up to complement. For these, the retained joint kernel depends only on current core, current port, and previous port: the decoy and the old shared coordinate can be removed. All four retained binary arguments are essential, with next-law entry contrasts exceeding .15. Thus the finite fixture discovers the port and its necessary one-tick memory rather than receiving their labels.

The whole-state oracle is used before the learner boundary to generate observable tables and after discovery to validate factor identities. It is never passed into the learner calculation. This separation is visible in the script. The selected raw binary task sensor is included: its response conditional on the unknown patch states is learned, and exactly one recovered factor explains it. The unrelated P3 sensor is described mathematically but omitted from this focused numerical test. Larger-N **probe gaps and existence of the open core** follow analytically from the kernels. Exact product-chart separation for every N is not inferred from the three numerical instances: the general identification statement retains its explicitly stated finite separation condition.

### Why the joint invariance test matters

Individual retained coordinates can pass regime invariance while their joint law fails. Let U be a fresh fair bit, take A'=U, and set B'=U XOR Z XOR E, with E an independent Bernoulli(.1) bit. Both A' and B' are fair under every regime, but

    P(A'=B' | Z=0)=.9,   P(A'=B' | Z=1)=.1.

A .35 regime shift in Z therefore changes the agreement probability by -.28. Every joint outcome remains strictly positive, so this is not a support degeneracy. The scalar-response lemma must be applied to the proposed **joint subsystem**, not separately to each of its coordinates. Product structure or a separate joint test is an indispensable additional obligation.

### Latent versus physical interface

Here the identified port quotient is a **latent generative interface**, not an exactly observed runtime message. Its calibrated noisy sensor does not reveal its current value to the controller. The one-bit delay realization is an existence statement at this generative interface. Executing that realization from raw readouts requires filtering or a physical digital-port access contract; neither is supplied for free. If the actual device already transmits that bit internally, the realization describes that internal connection, not additional controller sensing. No physical safe-control claim is derived.
