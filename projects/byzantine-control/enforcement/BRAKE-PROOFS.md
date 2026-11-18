# Discrete peer braking: parameter theorem and checked integer instance

Status: derived parametric theorem with an explicit proof; Lean-checked integer instance as described below; independent mathematical and semantic checking recorded in AUDIT.md. This is a theorem about stipulated discrete transition and observation relations. It is not a calibrated rotor, pump, hydraulic, thermal, or continuous-time model. The maintained motivating problem and completion contract govern its eventual integration; no repository acceptance or completion decision is made here.

The result preserves independently selected motor inputs, unknown jointly faulty sensor/planner/actuator components, separate local observations, delayed physical brake engagement, positive service on the same runs, factive prescribed-response justification, and an actor-independent thermal constraint. The kernel omits mechanical failures outside the specified force range, unmodeled paths around the brake, loss of sustained energy or cooling, and continuous intersample behavior. Those omissions are premises and refinement obligations, not properties proved by the controller.

## Primitive plant, information and fault interfaces

For target j, let v_j be a nonnegative mechanical rate state and let d_j(t) be its actual delivered service during epoch t. Fix ell_j>0. An intact joint motor/output chain supplies the fixed motor input tau0_j and delivers d_j(t)=ell_j v_j(t). A compromised chain may independently choose its motor input tau_j in [0,T_j] and withhold output by selecting any d_j(t) in [0,ell_j v_j(t)]. A motor independently exercises this input without collective approval. At most p<M joint motor/output chains are compromised; this permits output failure even when the motor continues turning and permits every named output chain to fail in some scenario. The speed-to-output relation is a declared primitive, not a derived hydraulic or electrical guarantee. There are m_j peer brake chains, with actual engagements e_ij in [0,1]. Define E_j = sum_i e_ij. There is no agreement step or permission filter before these inputs affect the world.

For c_j in (0,1], put a_j = 1-c_j. The unquantized speed relation is

v_j(t+1) = max(0, a_j v_j(t) + tau_j(t) - b_j E_j(t)).

The scalar shared thermal state has relation

h(t+1) = beta h(t) + sum_j kappa_j b_j E_j(t) v_j(t),

with 0 <= beta < 1 and kappa_j >= 0. The thermal state is not clipped at its protected bound H. It is a stipulated accumulated world state, including passive dissipation; its relation to measured temperature is unproved. The lower speed clamp is an explicit unilateral plant relation, not a selector enforcing the upper safety bound. A physical realization would have to justify that relation under the admitted faults.

The variable e is apparatus state: a local command passes through a bounded delay queue and sets the brake engagement. Engagement persists until another command is applied; a malicious brake can refuse, remain engaged, or choose any intermediate allowed engagement. At fixed v and E, the range of target-motor next effects is [max(0,a v-bE), max(0,a v+T-bE)]. Changing E shifts or truncates this realized-motion range. It does not shrink the motor's command alphabet [0,T], and the intervals for different E need not contain one another.

Fix one joint scenario f before evaluating the execution, not separate statistically independent faults by role. Per target, at most f_j chains have a faulty planner or brake actuator; write g_j=m_j-f_j>0. Each identity can be faulty in some admitted scenario. Independently compromisable sources are part of the same scenario: every intact planner receives 2s_j+1 distinct, identified source channels concerning its own target and actual sample epoch, with at most s_j corrupted or substituted channels in that received vector. The remaining channels satisfy |y-v_j(sample)| <= epsilon_j. Corrupted values may be arbitrary and may equivocate; they are not clipped to a truthful interval. Distinct source identity, correct-epoch binding, and receipt before the specified delay are interface assumptions. Shared corruptions count through their actual effects on these conditions; no independence follows from multiple readings. Withholding may consume a faulty-channel slot only if the remaining interface still supplies the required vector within the deadline.

An intact planner computes its own median z and issues ON exactly when z >= q_j. It does not read a pooled estimate, a fault identity, other planners' private readings, or another target's state. Different intact planners can obtain different medians. A good planner with a faulty actuator still obeys the issued-command rule and remains subject to the response obligation; its actuator's deviation enters the physical fault budget. A good planner with a corrupted source remains protected by its remaining source redundancy. A single faulty source is not used to remove an otherwise intact planner from the set of compliant executors.

In the core family, each nonfaulty planner-actuator chain has a fixed positive integer FIFO delay d_i with 1 <= d_i <= D_j, realized by a shift register. Its actual engagement at time t is its command from sample epoch t-d_i. A bounded-variable-age extension permits 0 <= d_i(t) <= D_j only after an explicit delivery rule proves the same actual-command correspondence; arbitrary old replay is not licensed by calling the link delayed. No global trusted schedule publisher is assumed: discrete epochs and maximum ages belong to the model's timing context. Their physical realization remains a premise.

In the positive family, the source vector concerns the same physical epoch as the planner invocation. The delay from that invocation to engagement belongs to the command/effect queue. Thus sample-epoch justification below is justification at actual invocation time. A stale-observation comparison does not inherit that equivalence: its current-invocation conduct rule stays fixed, and an old high sample need not justify a new command.

The stipulated conduct law is fixed independently of the controller threshold: an intact planner may issue ON only when its actual sampled target rate is at least r_j, and the command carries the required target/epoch identity. This is a sample-epoch justification rule, not a claim that the target remains above r_j when the effect arrives. The theorem requires q_j-epsilon_j >= r_j. For the real numerical family below r=6; for the integer instance r=2. Those values stay fixed in threshold/error comparison contexts.

Global requirements are v_j<=V_j for every target, h<=H regardless of actor compliance, and v_j>=L_j>0 for every nonfaulty motor. With at most p<M compromised joint motor/output chains, actual delivered service satisfies sum_j d_j >= min_{P:|P|<=p} sum_{j notin P} ell_j L_j; in the homogeneous case this is (M-p)ell L. Motor speed alone does not certify delivered service. The derivation uses the intact output relation and admits withholding on compromised output chains; the stated primitive needs its own physical refinement before interpretation as actual pumped flow or electrical delivery.

## Median and local response lemma

For 2s+1 ordered values with at least s+1 in [v-epsilon,v+epsilon], the median lies in that interval. If the median were below its lower endpoint, at least the first s+1 values would be below that endpoint, although at most s values are outside the honest interval. The same count applied to the last s+1 values excludes a median above the upper endpoint. This is a deterministic counting proof and permits arbitrary faulty values.

Consequently an intact planner's issued ON implies v(sample)>=q-epsilon>=r. This conclusion concerns every intact planner, including one whose actuator is compromised. Conversely an intact planner's issued OFF implies v(sample)<q+epsilon. Physical safety uses the latter implication only for the g=m-f chains whose actuators implement their commands. No report is treated as evidence of another actor's malicious intent.

In Brakes.lean, median_sound proves the s=1 lemma for unrestricted Int values and any two of the three channels sound. issued_on_justified fixes r=2 and proves the actual sample condition. Its statement has no actuator-compliance premise. ActsOn additionally identifies the actual engagement with such an issued command. TwoAct and local_effect_pair represent the two surviving chains when m=3,f=1; neither selects which chains survive in advance.

## Parameter theorem

For one target, define A_0(x)=x and A_(ell+1)(x)=a A_ell(x)+T. Equivalently,

A_ell(x) = a^ell x + (T/c)(1-a^ell).

Assume 0<L<=V, 0<=tau0<=T, b>=0, m>f>=0, 0<=epsilon, and the following explicit margins:

1. tau0 >= cL+bm;
2. b(m-f) >= T-cV;
3. 0<=q+epsilon<=T/c and A_(D+1)(q+epsilon)<=V;
4. q-epsilon>=r;
5. sum_j kappa_j b_j m_j V_j <= (1-beta)H.

These are inequalities on declared coefficients, fault budgets, delay, error and mission bounds. They do not assume the invariant or the existence of a winning local policy. The chosen threshold rule is given above. The family allows parameters to vary while the margins hold, and parameters change actual dynamics, timing, sensing or capacity rather than merely renaming the same instance.

Initialization is explicit: 0<=v_j(0)<=q_j+epsilon_j, additionally v_j(0)>=L_j for every nonfaulty motor, and 0<=h(0)<=H. Initialize correct command buffers OFF and start observation and command generation at epoch zero. During the first D_j epochs a chain need not yet have an applied command from a nonnegative sample epoch. Early safety follows from the startup envelope, not invented observations before startup. After the queue fills, the bounded-age correspondence applies. The initial family is nonempty whenever L_j<=q_j+epsilon_j for potentially nonfaulty motors; include this as an initialization feasibility condition.

**Theorem.** For every joint scenario meeting these component and timing bounds, every admitted causal choice of faulty inputs and faulty reports, and every admitted initial state, the local policy generates a nonempty infinite discrete execution satisfying the speed, thermal, service and prescribed-response requirements.

**Proof.** The plant maps, median and local command maps are total. Each pending queue has a specified next state, each faulty component has at least one available bounded action, and each source vector has at least one admissible realization. Recursive execution therefore produces a next state at every epoch; no permission predicate can block a physical transition. No finite maximal execution or deadlock is counted as success. For the variable-delay extension, choosing an admissible delivery age is also a nonempty environment move and must preserve the stated correspondence.

Because 0<=a<=1 and all inputs are bounded above by T while braking is nonnegative, v(t+ell)<=A_ell(v(t)) for every ell by induction. Nonnegativity comes from the plant map. For x<=T/c, A_ell(x) increases with ell and stays at most T/c. Thus startup v(0)<=q+epsilon and the delayed margin establish v(t)<=V throughout the initial delay interval.

Consider a later epoch t with v(t)<=V. If every nonfaulty planner-actuator chain is ON, E(t)>=m-f, so v(t+1)<=max(0,aV+T-b(m-f))<=V. Otherwise some such chain is OFF. Its sample age d is at most D and its actual sample rate is below q+epsilon by the median lemma. The growth envelope gives v(t+1)<=A_(d+1)(q+epsilon)<=A_(D+1)(q+epsilon)<=V. This proves the upper invariant without agreeing on either a state estimate or the faulty identities.

For a nonfaulty motor, E(t)<=m always, including all malicious and stale engagements. If v(t)>=L, then a v(t)+tau0-bE(t)>=aL+tau0-bm>=L. Therefore v(t+1)>=L. This service proof permits every brake to remain ON, so it does not assume timely release in order to obtain the service floor.

Given all speed bounds and h(t)<=H, the thermal update is nonnegative and at most beta H+sum_j kappa_j b_j m_j V_j<=H. This bounds the shared consequence of all engagements on the same execution, including unjustified faulty engagements. Per-target thermal budgets may replace the shared state only with a declared allocation whose sum meets the same shared constraint; independent local maxima cannot silently spend one common cooling budget repeatedly.

The median lemma proves the fixed response rule for every intact planner. Finally, each intact joint motor/output chain has v_j>=L_j and therefore actual d_j=ell_j v_j>=ell_j L_j. Every compromised output contributes d_j>=0, even if it withholds all delivery. For the actual compromised set P, summing gives sum_j d_j>=sum_{j notin P}ell_j L_j, which is at least the displayed minimum over permitted P. This proves the floor for actual delivery, not merely for a sum of speeds. All arguments are simultaneous on the same actual streams. This completes the discrete theorem.

Information is load-bearing through response justification and the responsive local policy. Under the deliberately conservative service and heat margins, an always-ON policy can satisfy the physical invariants while violating the fixed conduct law at low samples. The theorem does not claim that imperfect information is necessary for physical safety alone or that the threshold rule is optimal.

## Concrete real regime and sensitivity

A homogeneous one-target regime is c=1/10, tau0=4/5, T=13/10, b=1/5, m=3, f=1, L=1, V=10, epsilon=1/10, q=41/5, D=1, r=6, beta=9/10, kappa=1/10, H=6. Exact calculations give aL+tau0-bm=11/10; aV+T-b(m-f)=99/10; A_2(q+epsilon)=9193/1000; and beta H+kappa bmV=6. The normal unbraked equilibrium is 8, whereas the faulty maximum-input equilibrium is 13>V. For M such targets sharing one thermal state, H=6M suffices; H=6 does not automatically suffice for their aggregate heat.

The margin theorem covers a continuum of coefficient choices around the strict speed inequalities, with thermal capacity adjusted explicitly where needed. More delay or larger observation error increases the envelope burden. Larger brake strength improves upper-speed control but consumes the service and thermal margins. The lower-margin proof is sufficient, not necessary: its failure does not by itself establish impossibility, because a less conservative release argument might work.

Holding the other real parameters fixed, increasing b to 3/10 violates thermal protection in the admitted initial state v(0)=83/10,h(0)=6 when all three engagements are ON: h(1)=6147/1000>6. This numerical state requires the corresponding ON apparatus/queue initialization; it is a local transition obstruction, not asserted to arise from the OFF-buffer startup above. The integer comparison below supplies a reachable OFF-startup thermal witness. A stronger intervention can be physically effective and still inadmissible under the unchanged global thermal law.

## Quantization family and exact integer adapter

To include quantized discrete plants without falsely claiming that rounding is invisible, replace the speed update by Q_v(max(0,av+tau-bE)) and the heat update by Q_h(beta h+sum_j kappa_j b_j E_j v_j). Each Q maps nonnegative reals to nonnegative reals, is monotone and downward (Q(z)<=z), and Q_v(L)=L. Identity and floor quantizers both qualify when L is an integer for floor. The preceding upper-speed envelope and thermal arguments use downwardness; service uses monotonicity and Q_v(L)=L. Thus the same theorem holds in this explicitly enlarged model family.

The floor map loses less than one unit on each nonnegative update. The service proof does not pay a full unit of pessimistic loss every time: an integer lower bound L is a fixed point, so floor(z)>=L whenever z>=L. Replacing this fact with an arbitrary independent error in [0,1] would be a different and potentially stricter model. Quantization is a declared transition parameter, not a proof that an unquantized physical plant is bisimilar to the integer one.

The integer instance has c=1/2, tau0=4, T=6, b=1, m=3,f=1,L=1,V=10, epsilon=1,q=3,D=1,r=2,beta=1/2,kappa=1/10,H=6. Both quantizers are floor. Integer embeddings x->x and h->h identify the mechanical states and preserve time, actual input choices, source readings, issued commands, engagement queues, conduct and thermal predicates exactly. With ell=1, intact output is d=x and a compromised output may choose any integer d in [0,x]; embedding this d into the real interval preserves the actual-output interface and its lower guarantee. Other output discretizations require their own adapter. For integer x,u,E,h,

x' = max(0, floor((5x+10u-10E)/10)),
h' = floor((5h+Ex)/10).

These equal the quantized-family transitions by ordinary floor identities, including max(0,floor z)=floor(max(0,z)). The real family margins specialize to tau0>=7/2, b(m-f)=2>=1, A_2(4)=10, q-epsilon=2=r and kappa bmV=3=(1-beta)H. The initializer is 0<=x0<=4, and x0>=1 for a normal motor. Intact issued commands are 0 or 1 and use their own three-source median. With integer readings, OFF implies the stronger sample bound x<=3, which yields the sharper two-step upper bound 9 used in Lean.

Brakes.lean proves: unrestricted integer median robustness; issued-ON justification at actual sample x>=2; physical dichotomy E>=2 or previous sample x<=3; startup safety; delayed speed induction; positive normal-motor service for all time; thermal induction for the same speed and engagement streams; and totality of every primitive plant transition. The stream assumptions are the explicit transition equations, bounded primitive inputs, sound local source pairs and delayed actual-command correspondence. No assumption says that the next state is safe.

At most one faulty planner-actuator chain among three yields TwoAct by local_effect_pair. In the s=1 source case, at most one corrupted source among three yields TwoSound. These are combinatorial projections of the one joint scenario, not assumptions of independent budgets. An implementation or finite encoding must show its fault inventory satisfies these projections; the Lean propositions do not inspect hardware identities or automatically authenticate channels.

The unbounded-time theorems are speed_run, service_run and heat_run. service_run proves the normal motor's speed floor; actual-output assembly is the explicit summation argument above, not an additional mechanized delivery theorem. issued_on_justified concerns the intact planner and therefore survives an actuator fault. Arbitrary independently faulty actuator behavior still appears in speed_run's actual engagements. The finite worker's model must discharge these hypotheses from its concrete queues, source choices and fault masks; similarity of constants is insufficient.

## Explicit ablations, global consequence and scope

Removing only counterbraking while retaining the same motor alphabet and normal control admits x0=4, faulty u=6, and trajectory 4->8->10->11. This violates V=10 at the third update. It is checked by ablation_trace; no honest service action was removed. engagement_changes_motion checks that the same x=10,u=6 produces 11 with E=0 and 9 with E=2. startup_history_matters separately verifies that x0=10 with an empty engagement queue is not covered by the safe initializer.

For an actor-independent protected-outcome comparison, change brake strength to b=3 and retain the associated heating law (both torque and heating scale by that strength), leaving H=6 and the other integer constants fixed. From x0=4,h0=6,E0=0 and faulty u0=6, the next state is x1=8,h1=3. Exact source readings 4 at epoch zero justify all intact planners' ON commands under r=2, and a faulty brake may also choose ON. Thus E1=3 is admitted with delay one. At that next transition, the strong brakes reduce the speed to x2=1 while h2=floor((5*3+3*3*8)/10)=8>6. strong_brake_heat_violation checks the decisive arithmetic. The law counts this violation regardless of which actor caused it. The stronger-brake context is an explicitly losing comparison, not a run of the winning b=1 context.

A separate composition witness shows why a common thermal budget cannot be reused per target. Take three integer targets with x0=4, a shared h0=6, empty queues, two faulty motors choosing 6 and one normal motor choosing 4 (p=2<M=3). After startup, speeds are 8,8,6 and shared heat is 3. Exact source readings 4 justify all three local ON decisions at each target; every actual brake can then be engaged. The next shared heat is floor((5*3+3*8+3*8+3*6)/10)=8>6, although each isolated target obeys the one-target H=6 theorem. The shared context fails its aggregate cooling margin; it is not covered by the shared theorem. shared_heat_composition_failure checks the arithmetic. This is a failure of naive product assembly, not a faulty-controller diagnosis.

Sustained service assumes continued availability of motor input and passive dissipation with the declared coefficients. A finite battery or exhausted cooling resource would need additional state and cannot support this unbounded-time conclusion merely by truncating the horizon. Arbitrary structural destruction, unrestricted brake jamming forces, hidden actuation bypasses, thermal state manipulation, source-roster compromise, unbounded delay, and loss of the unilateral plant relation remain outside the certified family. The force and cooling relations are mathematical capability laws, not claims that real hardware cannot fail that way.

Physical counterintervention and the service output remain deliberately abstract. To interpret them as rotors or pumps, provide a simulation/refinement relation preserving epochs, all admitted fault effects, service delivery, heat and conduct monitors; prove intersample constraints and resource sustainability. None follows from Lean's integer arithmetic. The theorem also does not establish an all-policy information impossibility result or universal synthesis completeness.

## Verification surface

Compile with Lean 4.33.0, using Std only:

`C:\Users\Sean\.elan\toolchains\leanprover--lean4---v4.33.0\bin\lean.exe theories-and-designs/byzantine-control/enforcement/Brakes.lean`

Run the exact rational margin and witness check with Python 3.12:

`C:\Python312\python.exe -B theories-and-designs/byzantine-control/enforcement/brake_checks.py`

The script does not simulate an unbounded fault space; it checks the displayed rational arithmetic and witnesses. The unbounded integer invariants are Lean theorems; the parametric real and general 2s+1 median arguments are the written derivations above. A successful compilation and the printed axiom dependencies establish only the encoded integer statements. Inspect the adapter and primitive assumptions separately. No custom axiom or admitted proof is introduced. Independent checking is recorded in AUDIT.md; repository acceptance remains a separate outstanding judgment.
