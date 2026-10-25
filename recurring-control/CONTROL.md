# Conditional physical control, engagement and shared resources

Status: derived component construction for the admitted [INSTANCE](INSTANCE.md), with selected kernel-checked policy/timing/arithmetic lemmas in [Control.lean](Control.lean) and exact executable checks in [control_model.py](control_model.py). Independent source checking and the full RN/IA assembly remain separate. The effective fault support, current information, actual stored program and renewal return are suppliers to this component, not assumptions that close the program. The full Goal remains active.

The prior-result assessment in [SOURCES](SOURCES.md) precedes this construction. Robust image inequalities, deadband feedback, monotone access progress, order-statistic error bounds and stock induction are established mathematics. The local contribution is the compatible source/policy/timing/accounting adapter, including the distinction between factive issued conduct and actual hostile effects. No publication-level novelty claim is made.

## C0 The exact component interfaces

All statements refer to one source trace with the same x, held commands, engagement, code, raw acquisitions, route state, queues and stock. Let J_t be an analyst set of impaired physical paths, with weight beta_t=sum_(i in J_t) w_i. No policy reads J_t. The renewal/realization argument must establish that every path outside J_t has actual engagement1 and currently held flow correction produced by the prescribed routine from its own actual receipts. Its estimate must have error at most eta_e relative to x at the physical effect time, including holding and command reordering. Inside J_t, source bounds alone apply: a in[0,1], u in[-2,2]^2 and v=a(2+u) in[0,4]^2.

The conduct interface is separate and stronger in a different direction: EVERY causal intact executor issuing a nonzero correction must have an issuance-time estimate error at most eta_i, or its actual program must issue zero instead. Merely counting a physically impaired path in J_t does not excuse an intact decision executor's factive duty. Corrupted executors are classified by actual state/intrusion/initialization history, not whether their action happens to violate that duty. In particular, a calibration-only defect can leave that body's decision execution intact: its own bad raw row is one affected input, and the distributed information argument must still justify every nonzero command it issues. A coarser body/support label does not waive this obligation.

For the common numerical interface use beta_t≤5/34 in the equal branch or beta_t≤3/17 in the pinned unequal branch. The latter is the mass of five weight3/85 paths. These are outputs to obtain from the raw-rate/renewal proof; this component does not assume a primitive useful-good count. Uniform five-path accounting suffices here even when a later phase theorem improves it. The one additional initially disengaged intact path is charged separately during startup, not to a permanent sixth programming fault.

The runtime supplier must establish its actual sample/send schedule, finite work, g initialization/holding and fresh-report use. The candidate schedule samples at local phase congruent to role-id modulo10 and sends the completed row to34 destinations at the next phase. Under genuinely aligned nominal phase, at most four nominal bodies sample or broadcast in any tick. A damaged phase/configuration/route is charged through the same support, not credited with that schedule. The one-stock bound below is conditional on this interface and the actual source capacities; independent runtime checking must discharge it.

## C1 A finite factive feedback routine

Fix the source threshold r=1/20, gain k=8/5, design error eta=3/1000, issued limit U=3/2 and invariant radius R=4/5. For a median m expressed in milliunits, the exact integer routine is

`q(m) = sign(m) · min(1500, floor(8·max(|m|−53,0)/5));  u=q(m)/1000`.

This is rounding toward zero. The selected program must use bounded integer arithmetic and this sign/rounding meaning, not floating-point tolerance or rounding away from zero. The packet range[-4000,4000] keeps8m within[-32000,32000]; intermediate operations fit the supplied32-bit arithmetic. The source limit U is independent of the physical cap2.

If q(m)>0 then m/1000>r+eta. Whenever the actual issuance error is at most eta, x_k≥m/1000−eta>r. A negative command gives x_k<−r symmetrically; zero is always permitted. Clipping preserves sign and guarantees |u|≤U. This proves the factive issued-response duty for the actual data condition; it does not declare hostile realized effects lawful. The scaled integer counterpart and universal command-range/guard lemmas are checked in Lean.

Let S_D(y)=sign(y)max(|y|−D,0), with D=r+eta. Then |S_D(y)−y|≤D. With quantization error epsilon_q≤1/1000 and the cap inactive,

`|u−k x_effect| ≤ k(r+eta_i+eta_e)+epsilon_q`.

The numerical eta_i=eta_e=eta yields epsilon_u=453/5000=.0906. More generally, clipping is nonexpansive and fixes k x_effect whenever kR≤U, so that condition suffices for the displayed error estimate. The numerical branch has the stronger inactive-cap property on the relevant source prefix: |x_issue|≤R and |hat x−x_issue|≤eta imply |hat x|≤.803, hence the unrounded magnitude is at most k(R−r)=6/5<U. Toward-zero rounding cannot increase it. The proof does not apply an inactive-cap identity to arbitrary malformed data; the total integer routine still clips those inputs, and the information/conduct argument must justify when they may be used.

The .003 guard margin matters. A naive deadband at r alone takes the admissible estimate .051 when the true state is .0491 and can issue a positive rounded correction although the factive condition fails. The53-milliunit deadband issues zero in that case. Raw noise.00149 gives.05059 before nearest-milliunit rounding, so this example fits the actual.002 raw-error source allowance without using the larger design error as though it were an attained sample error. This is an actual nominal-error/decision witness, not a claim that arbitrary state reconstruction is always necessary.

## C2 Access is physical progress, not an acknowledgment

For a general contact range[0,A], a sustained actual effort g≥G against o≤O<G gives progress at least G−O until saturation; from a0 the required integration count is at most ceil((A−a0)/(G−O)). This is a source force-versus-opposition condition, not a promise that commanded effort is realized. For the pinned coordinate, g=1 and o in[0,3/4] imply `a+≥min(1,a+1/4)`. Iteration gives `a_after_j≥min(1,a_before+j/4)`, so four actual integration steps suffice from any a in[0,1]. Once a=1, the same effort maintains it against continued maximal opposition. No owner acquiescence is used. Because a newly issued g setting acts one tick later and the current a determines current flow, a g=1 issued at B establishes full current-flow engagement by B+5 under INSTANCE's order.

By contrast, g=0 from a=0 under the identical opposition leaves a=0. A hostile g=-1 can remove any engagement in one update. These compare actual operations with the same physical resistance and show why deployment matters to v=a(2+u). They are local source witnesses; the global theorem still has to pay for the access interval and maintain the other paths. The sealed input h remains arbitrary throughout: this mechanism changes the available external flow, not the sealed target's program or command alphabet.

Held g is not cleared by processor halt. An intact role's actual previously issued g=1 can therefore maintain engagement while its processor is unpowered. A previously hostile g remains hostile until a real setting replaces it. The return argument must charge that path until the physical g/flow consequences are useful. An actual action whose contact/field state fails to reach the target cannot receive restoration credit from this lemma.

## C3 Actual ages, reordering and startup

All physically possible flows lie in[0,4]^2. On K, the row-sum bound of A is.11 and the centered baseline minus weighted flow has magnitude at most2. The declared per-body physical maxima give at most2N sample events,2N maintenance-field units, N deployment-effort units, N selector motions and one acquisition in a tick. For N=34 this is205; the associated source impulse allowance is pbar=205/100000. The source charges selector drive/hold separately even while the CPU is unpowered. Sustained intrusion uses the reached body's ordinary peer-side capacities; external physical repositioning is privately powered and its extra collateral effect shares the same w_env envelope, rather than adding another uncharged disturbance allowance. Thus

`D_x=.11+2+.5+.01+pbar=52441/20000`,

and any safe prefix satisfies `||x_t−x_s||∞≤delta D_x(t−s)`. This is a source-wide bound; it does not assume nominal feedback. Costs and effects are counted for held/failed actions as specified, not only successful instructions. Any additional physical operation charge or effect introduced by realization must update this interface rather than disappear into an unproved budget.

A source row with raw error.002 and sample age at most13 ticks at issuance has current error at most `.002+13 delta D_x`. A held command does not necessarily have age at most4 merely because every command arrives within4 ticks. If commands can arrive out of order, a later old arrival can overwrite a newer one. When a feedback command is issued every tick, choose the command issued t−L: it arrives no later than t and no earlier than t−L. The last applied arrival at t is at least that late, and its own issue time is at least its arrival time minus L. Consequently the held command's age is at most2L. This order argument, without FIFO, is encoded in Lean.

For L=4, sample-to-effect age is therefore at most13+8=21, giving error `4001101261/2000000000000 < .003`. Both issuance and effect bounds fit the same design eta. In the parameterized interface, require raw error nu plus delta D_x times the derived sample-to-effect age L_s+2L to be at most the selected eta; changing sampling/transport/actuation timing rechecks this inequality and the renewal return horizon. This does not infer report freshness from a timestamp; the runtime/renewal supplier must derive the sample/send/selector/queue conditions.

Generic transition into a new command class needs a2L flush after the first new-class issuance, because old arrivals may overwrite early new ones. The executable check exhibits that failure of a one-L argument. A stronger actual program can do better: issue one zero baseline at boot B, then issue no u during the remainder of a16-tick drain. All baseline/preboot commands arrive by B+4, before the first fresh feedback issuance B+16. Its arrival by B+20 is therefore not overwritten by a baseline. This improvement is conditional on the actual quiet-drain sequence, not a new FIFO premise. The shared interface conservatively keeps24 ticks after boot (D=m+30 in the renewal package); an earlier observed return does not narrow source behavior.

From the full initial box, a direct cap-based induction gives radius at most `1/2+t delta D_x` through t=24, strictly below R. At each step this bound lies inside K, justifying the next physical rate bound; no infinite safe-prefix premise is assumed. By t=24, every path credited outside the derived J_t must satisfy the feedback/effect interface. Newly reconstructed paths receive their own return interval and are not prematurely removed from J_t.

Startup service requires a separate argument. Each nominal initial body is powered at q=0 and must actually issue g=1 at tick0 before later maintenance. With g initially0, its engagement has lower bounds1 at t=0,1/4 at t=1,1/2 at t=2,3/4 at t=3 and1 thereafter. The additional initially disengaged path can remain0 through t=1, then reaches1 by t=5. The initial program issues no nonzero feedback in those first ticks. Apart from the derived early five-path support and that one extra disengaged path, actual contribution at the minimum tick is at least1/2. Thus startup service is at least7/17 in the equal branch and67/170 in the unequal branch, both above.3. After t=5 the extra path is engaged or belongs to the actual impairment set; clamped legitimate held outputs alone give at least(1−beta)/2 during the remaining startup. This proof cannot be replaced by a bound on x.

## C4 Weighted robust invariance with different local estimates

Write beta for the actual impaired weight and g=1−beta. For a path outside J, write its actual held command as `u_i=k x+e_i`, with `||e_i||∞≤epsilon_u` supplied by C1/C3. The estimates and errors may differ at every recipient and may be correlated. The source update becomes

`x+ = [I+delta(Aθ−gkI)]x + delta(2beta·1 − sum_bad w_i v_i − sum_good w_i e_i + h+w_env+p)`.

Since bad v_i lies in[0,4]^2, the first two disturbance terms have combined magnitude at most2beta. For a nonnegative matrix coefficient, ensured by `1+delta a_min−delta k≥0`, its infinity norm is at most `1−delta lambda`, with `lambda=k(1−beta)−(a_max+c_max)`. Hence

`||x+||∞ ≤ (1−delta lambda)||x||∞ + delta[(1−beta)epsilon_u+2beta+.5+.01+pbar]`.

If lambda>0 and the bracketed term is at most lambda R, the radius-R box is invariant. This is a numerical/structural condition over the actual influence/error/delay source interfaces, not a premise that the complete product already wins. It holds uniformly over theta and every changing J whose weight fits the bound. The same program is chosen before the actual model and compromise history.

| Branch | Maximum beta | lambda lower bound | Additive bound | Positive radius margin |
|---|---|---|---|---|
| Equal weights |5/34|2133/1700|300371/340000|40909/340000|
| Pinned2/85,3/85 weights |3/17|2053/1700|63893/68000|1803/68000|

All values include milliunit rounding and selector-motion effects; omitting either would establish a different numerical certificate. The error term is weighted by the good mass; replacing it by an unweighted bound is a further conservative option, not an equality. The exact checker verifies the affine envelope at all multi-affine corner combinations, as well as the symbolic rational inequalities. These corner checks verify the overapproximation; they do not assert every corner is generated by the actual deadband policy.

For actual good feedback on radius R, C1 gives |u|≤6/5, so actual good flow is at least4/5 in each coordinate. Impaired paths still contribute nonnegative flow. Recurrent service is therefore at least58/85 in the equal branch and56/85 in the unequal branch. The weaker cap-only bounds29/68 and7/17 remain available without the sharper good-data magnitude lemma. All service statements use the same realized v that enters the process equation.

The full source consequence is an initialized simultaneous induction: source initialization pays startup and supplies the first safe prefix; actual source/renewal operations establish the next support and information facts; C4 extends state safety; C5 supplies affordability; these same facts allow the following source step. The information/support/runtime modules must discharge their hypotheses. A valid C component does not close the full RN/IA program in their absence.

## C5 One resource account, including continuing bad behavior

For a parameterized cohort/schedule let C be the maximum number of genuinely nominal broadcasters/samplers per tick, B the maximum number of other physical bodies, W the per-body word cap, O_cpu the per-body operation cap and c_cpu its unit cost. One sufficient demand expression is `C·N+B·W+2(C+2B)+N·O_cpu·c_cpu+2N+N+8N+N+2A_tick`, using this source's units and one selector drive/hold allowance per body. C may be ceil(N/P_s) only after the actual phase/id schedule establishes it; A_tick bounds actual raw acquisition onsets. This expression deliberately overbounds some overlapping work, which is safe for a positive demand bound, but cannot be reused as a negative actual-cost witness.

Each physical copy of a64-bit transmission costs1; receiving/parsing work is in the bounded CPU account, not a second transmitter charge. With at most four nominal broadcasters and at most five other bodies each using their full64-word egress capacity, transmission cost is at most `4·34+5·64=456` per tick. A body counted in both upper allowances only makes the estimate conservative; no actual sender is given two budgets. The explicit schedule must be implemented before this bound may be consumed.

At most four nominal sample jobs and two samples per bad body cost at most `2(4+2·5)=28`. All34 CPUs at their full200000-operation limit cost34/5=6.8. Independently of which roles are bad, total maintenance fields cost at most68, deployment effort34, selector drive/hold34 and actual flow magnitude272. At most one acquisition contributes2. This gives the declared peer cost bound `4504/5=900.8` per tick. Malicious fields, held output, off-schedule traffic, failed attempts and rejected inputs are not assumed absent. The private opposing source's energy is outside the community pool as INSTANCE states; its physical effect and response cost remain inside the control argument.

Supply at least4504/5 per tick (for example901), within the admitted range[0,1000], makes cost no larger than supply. Thus the finite stock is nondecreasing until capacity and always nonnegative from its stipulated[1000,1500] initial interval. No fair allocator is needed, and source underfunding remains an actual failure outcome. The support/information proof may use only the already affordable prefix; a first-failure argument closes the coupling rather than assuming infinite available power.

There is a distinct necessary resource boundary. Since all v are nonnegative and each weight is at most w_max, the service requirement gives `sum_(i,k) v_i,k ≥ .6/w_max`. That actual flow cost is at least102/5 per tick for equal weights and17 for the unequal branch, before inquiry/maintenance. Consequently supply below that lower rate cannot sustain the mission indefinitely from finite stock. At R=0 and initial stock≤1500, the unequal branch cannot supply89 complete service ticks. This lower-cost argument concerns actual delivered flow; it does not use the sufficient900.8 upper bound as a failing trace or claim an optimal threshold between the two rates.

The source role/operator accounting must remain explicit. The selector drive/hold and external sustained-intrusion boundaries above are part of the source binding. If realization introduces another operation or extra sustained effect beyond INSTANCE's table, its cost/impulse must be added and the same inequalities rerun. It cannot be called free because this proof has headroom.

## C6 Scope of comparisons and executable checks

Access checks compare g=1 with g=0 against the same continued o=.75 and show the actual engagement/flow consequence. The coordinator's separate whole-source boundary work owns the stronger changed-opposition and denied-access impossibilities. Command checks compare the justified deadband with the unguarded nominal-error counterexample. Resource checks separate necessary actual service cost from sufficient shared workload. The source remains partially observed: a scalar row does not by itself establish a whole-class no-communication impossibility, because local-coordinate control, histories and physical signaling are genuine alternatives. Root boundary work supplies the exact scoped information comparison; this component does not claim more from row rank.

The exact Python checks use Fraction arithmetic, reject optimized execution that would remove assertions, compare the integer routine with its independent rational specification, inspect source-age/command-arrival order, verify both weighted affine envelopes and startup/access/resource certificates, and bind the record to this document, the code, Lean file and INSTANCE. Selected Lean statements prove universal integer guard/range/bias and order implications plus exact rational certificates after clearing denominators. The full real-valued matrix, source, service and recurrence reasoning is written here and needs independent semantic checking; simulation counts are not an unbounded proof.
