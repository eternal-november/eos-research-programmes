# Evidence-relative crossing certificate transport on a learned parity mission

31 October 2026. Scoped theorem and constructive proof. This imports the earlier common-response/ownership construction and finite-field support-learning theorem; no novelty, full RC4, whole-contract, or adoption claim is made. Its target is the same-object, evidence-relative crossing-interface theorem stated in §1.

## 1. Exact statement and independent semantics

Use the physical filter/probe/service semantics of `uncertain_coupling_20261030/uncertain_coupling_mission_theorem.md` §§1–6,8. A world has a fixed stationary finite-memory binary linear filter driven by fresh fair innovations; D is a supplied memory ceiling. Source coefficients and source grouping are unknown. Isolation, reliable noninvasive measurements, clock/gate/interlock behavior, physical draining, and unchanged calibration-to-service law remain supplied physical hypotheses. No chart below establishes them.

Let n=2m>=2. The actual source has selected captures

    W=(r0,z1,...,zn,r1,...,rn,d).

These are obtained from the full H-window Y by a known coordinate projection P_cap. Safe probe i records (r_(i-1),zi,r_i) on ONE fresh isolated block; the endpoint probe records (rn,d). No chart permits any new physical joint probe. Probes are fixed before the fresh block, each reserves its H+D spacing, including the last calibration-to-production gap. Optional delay discovery uses the earlier simultaneous family of candidate endpoint probes; d denotes the subsequently chosen slot. Other slot evidence remains in the physical uncertainty record.

The actual service controller captures r0,z1,...,zn, computes p=r0+sum_i zi with its declared matched implementation, and enables the supplied XOR interlock only at the chosen load slot. The physical bad event there is exactly p+d=1; all other slots remain isolated. Its capture, computation, timing margins, gate, memory and complete drain/tail envelope are independently specified, as before. Refusal or missed useful completion counts as failure, not as automatic safety/success.

Let E be the single simultaneous correct-projected-support event from the original acquisition design, with probability at least 1-delta. For K probe types of output dimension k_e<=3, m_e>=k_e+ceil(log2(K/delta)) independent fresh samples suffice. The compiler below accepts this positive subclass only when each retained local triple span is exactly

    L_i={(a,u,b): b=a+u}

and the chosen endpoint span is exactly L_end={(b,d): d=b}. Acceptance of this particular relation pattern is not the only possible mission solution. On E, any true member of this positive subclass passes; arbitrary filters can legitimately fail/refuse.

Let K_phys be the nonempty class of stationary physical filter worlds consistent with all retained true evidence and physical premises. For the positive construction use the relaxed CAPTURED support

    V={w: r_i=r_(i-1)+zi for all i; d=rn}.

Let C={T<=V: A_iT=L_i for all i and A_end T=L_end}. Every captured support P_cap(S_full) from K_phys belongs to C. Additional delay evidence can make K_phys smaller. V is defined from the selected chain constraints, NOT claimed equal to the projection of a maximal all-evidence full-window support. It need not realize unselected delay readouts. Unobserved window coordinates are neither reconstructed nor used to bypass the physical isolation requirement.

**Theorem.** On E, subject to the compiler and capability/budget guards below:

1. One explicit positive local representative of V has two genuinely crossing, constant-size ownership charts, a common source-preserving operational refinement, and strictly commuting record-grouping maps under finite tile concatenation.
2. Both chart realizations and every T in C factor the same preparation/test cylinder for O={(0,0),(1,1)} through Q(w)=(p,d). The actual physical service policy therefore has zero service hazard and completes within its original matched envelope, without identifying the actual full source law.
3. A finite compiler produces and checks the chart witness and transported mission certificate using the explicit bounds in §7. It retains K_phys, E, actual resource identities and physical timing guards. It does not turn V into a physical model assertion or give the controller new observations.
4. Removing a specified local information channel invalidates an exact chart implementation; removing a specified evidence relation invalidates the old physical zero-risk certificate. The repairs in §9 have separate permissions, time/storage costs and confidence accounting.

Consequently, for a true source in the named full-plane/diagonal positive subclass, with the requested chart/controller permissions and physical capability guards satisfied and initial acquisition, compilation/checking and service fitting the original hard opportunity budget, the compiler necessarily accepts on E. Under these positive-case hypotheses, unconditional missed-or-unsafe probability is at most delta, plus any separately justified nonzero physical/acquisition premise allowances. This is a sufficient uniform policy/certifiability theorem for the declared mission, not negative completeness for all controllers.

## 2. Positive local mechanism and two crossing ownership charts

Representative source events are U0,U1,...,Un, independent fair bits. Their IDs name events in the CHOSEN REPRESENTATIVE, not recovered physical innovation coordinates. U0 initializes r0. For each i, zi=Ui and r_i=r_(i-1)+Ui; d=rn. Each source event is drawn once and its value is retained until its declared uses finish. There is no redraw on a chart change.

The map g:F2^(n+1)->V is bijective: the inverse reads (r0,z1,...,zn), and the equations uniquely determine the other captures. Uniform independent local events therefore induce uniform V. This proof uses a product carrier mathematically; it does not require a centralized sampler, a stored n-bit seed table, or a global history predictor.

For tile j, i=2j-1, put a=r_(i-1), u=Ui, v=U_(i+1). The four labelled output occurrences are

    (1,2,3,4)=(zi,r_i,z_(i+1),r_(i+1))
             =(u,a+u,v,a+u+v).

Its normalized kernel is

    K(z,b,z',c | a)=1/4 * 1[b=a+z and c=b+z'].

**Column chart C:** owner C1 owns occurrences {1,2}, draws u, computes b=a+u, and sends b to C2. Owner C2 owns {3,4}, draws v, computes c=b+v, and sends c onward. Equivalently its two sequential conditional kernels are 1/2 times their XOR equation indicators. Incoming a and seam b are declared data, not access to an external hidden state.

**Row chart R:** owner R1 owns {1,3}, receives/draws the two named fair source events at their scheduled times and delivers u and v to R2. R2 owns {2,4}, retains a then b, and computes b=a+u and c=b+v. Its source kernel is the four-point uniform law and its recurrence is deterministic. R2 has no independent access to the event values except through the declared deliveries. Owners are resumable components with time-stamped output events; neither is an atomic tuple-return call.

Both charts use the same two events and equations, not independently fitted pair marginals. Their equality is pointwise for every a,u,v, and positivity follows from normalized sources and deterministic updates. This is an explicit feasible constant-size common-response certificate for `Discovery_and_Reuse.md` §13; §14 supplies the ownership interpretation. No universal fixed-endpoint response recovery is asserted.

The ownership partitions {1,2}|{3,4} and {1,3}|{2,4} have all four nonempty singleton intersections. Their blocks overlap without inclusion, so they cannot both be cuts of one laminar tree. They change the actual required communication seam, not just factor labels. A common directed graph with these crossings is admitted here; no claim is made that it is a common ordered-planar C5 refinement. The earlier ordered C5 crossing obstruction remains intact.

## 3. Local states, schedule, identity, and resource semantics

For a tile retain two source cells, two XOR cells, and one outgoing parity channel. A source cell has states `ready`, `held(bit)`, `spent`; an XOR cell has states `wait_parity`, `have_parity(bit)`, `have_pair(bit,bit)`, `done(bit)`. A channel is empty or contains one bit plus its immutable source/output event tag; send/receive ownership is explicit. Static owner/event identifiers cost index bits, not zero storage.

Fix a canonical elementary witness schedule. Initialization draws U0, then delivers it to the first XOR cell (two ticks). Each tile performs:

1. draw u, recording output occurrence 1;
2. deliver/copy u to the first XOR cell;
3. XOR with its already available incoming parity, record occurrence 2;
4. draw v, recording occurrence 3;
5. deliver/copy v to the second XOR cell, whose parity register is b;
6. XOR, recording occurrence 4;
7. send c to the next tile's incoming register, or to the terminal d-copy register.

Finally copy the terminal register to d (one tick). Initialization and every draw, copy/delivery, XOR and seam send cost one abstract elementary tick. Total is 7m+3 ticks. The parity transfer from step 3 to the second XOR's register is part of that specified XOR transition: its output register is the sole register read by the next XOR, not an uncharged extra network message. Where owners differ, that register is a named shared handoff slot, with write authority at the first XOR and read authority at the second. If the actual implementation requires a further message, its extra tick/cost is added in BOTH chart implementations; equality does not silently omit it.

Both charts execute this SAME elementary schedule, even when a delivery is an internal copy under one ownership and an inter-owner send under the other. Owner phases suspend between their scheduled operations. Thus no contraction hides source draws, pending messages, resource access or elapsed witness time. A fixed permission table names the sole writers/readers of each register and channel. Regrouping does not copy the authority token or create two independent resources.

Each tile has a fixed finite number of bit registers and finite-state phases; at most two innovation bits cross the row seam, at most one parity bit crosses a tile boundary. The construction has O(n) cells/events/identifiers and constant value-state per cell. Global dispatch can be a static schedule or a counter; it is explicitly included in §7. No unrestricted broadcast is used.

**Two clocks must not be confused.** These 7m+3 witness ticks specify an executable local sampler if it is run. They are not the actual filter's physical capture times. The common mission cylinder below records values with the original fixed capture labels and actual policy's independently supplied timing envelope. The charts are normally certificate representations, not replacement environmental hardware. If a user wants their sampled outputs physically delivered at the original timestamps, initialization, buffering, sampler latency and the full causal delivery schedule require an additional implementation/capability check. That stronger timed source replacement is NOT this theorem. Actual physical block/readout/gate/resource identities remain in the physical certificate; representative coin identities remain in the representative witness.

## 4. Fine records, actual maps, and tile substitution

Let H_f be the finite set of complete elementary witness records generated by the schedule, including event IDs, source values, register/channel updates, owner permissions and witness tick numbers. Its probability law is the pushforward of the independent local coins. Records have one coin choice at each specified draw; no branches other than those values. The analytical carrier may contain exponentially many records; compiler/runtime never enumerate it.

For each ownership chart d in {C,R}, H_d retains the same elementary records packaged by that chart's owner resumptions. Define f_d:H_f->H_d by deterministic regrouping. Because the packaged records retain a unique immutable elementary event index, tick, and update order, unpacking by STABLE MERGE in that global event order is an inverse. Concatenating owner lists is not unpacking: the row owners resume in an interleaved order. Thus f_d is a bijection preserving preparation weights. It is not a grouping into an atomic return kernel. Define e_d:H_d->V by reading the labelled capture outputs. This too is a bijection for this deterministic schedule, since the outputs recover all coins and hence all scheduled internal updates. In particular e_C f_C=e_R f_R=g_rec, where g_rec extracts the same complete captured output.

A reduced chart may hide selected internal event fields only after its test language is fixed. Such a forgetting map is a surjective deterministic realization morphism; it is not automatically an isomorphism or adequate for later resource/timing tests. The theorem uses the full cost-labelled witness records for implementation comparisons.

Tile substitution is ordinary actual sequential wiring, not assumed by nomenclature. Conditional on incoming parity a, the tile draws independent u,v and emits outgoing c. Composing tiles uses that ONE c as the next a, with the same channel event ID. By induction, after tile j the register is U0+sum_(i<=2j)Ui and all preceding output records satisfy the corresponding equations. The finite joint path weight is 2^(-(1+2m)). Therefore serial composition is exactly the global normalized V law, not a product of independently fitted overlapping triple laws.

For any subdivision into consecutive groups of tiles, define coarsening by restricting to the relevant tagged events and STABLY MERGING constituent owner lists by their immutable elementary event indices, then repartitioning by the requested owner map. Owner-list concatenation is expressly excluded. Direct grouping and iterated grouping retain exactly the same indexed events in the same unique order, so they give literally the same ordered tagged lists. Thus q_AC=q_BC q_AB and identity grouping is identity. The assertion uses indexed event restriction/merge, not a false claim that nonlaminar owner resumptions form contiguous list blocks. A concrete trace-transform implementation must charge its merge/index-array traversal if it is actually executed; the static certificate only emits/checks the local event-index maps. Applying each chart's crossing partition inside tiles commutes with concatenation: neither changes an intertile source or parity identity. This proves the claimed limited substitution coherence. It is not a theorem identifying arbitrary alternative schedulers or proving every graph assembly opcartesian.

## 5. Common observable cylinder and physical controller transfer

For T in C, let p_T be uniform on its finite set of captured records. Set Q(w)=(r0+sum_i zi,d). Since T<=V, the two coordinates coincide. Because the terminal probe is surjective onto its full diagonal, Q(T)=O={(0,0),(1,1)}. Q:T->O is a surjective linear map, so its two fibers have equal cardinality. Hence q_T p_T=p_O, where p_O is uniform on O.

For each y in O, let m_y^T(w)=1[Qw=y], and let m_y^O be the coordinate indicator. Then

    m_y^T=m_y^O q_T.

For each chart define q_d=Q e_d and preparation p_d=(f_d)_*p_f. The local positive construction proves q_d p_d=p_O and m_y^d=m_y^O q_d. These are actual forward-preparation/pullback-test realization maps. They require no arrow T->H_d, no section O->T, and no recovered physical source realization.

Optional deterministic capture-slot labels and the unchanged physical policy's public schedule can be adjoined to these outputs: their law is fixed by the guarded selected policy, not inferred from representative witness ticks. If a new context queries additional early-bit details, a new cumulative-query coverage proof is required. In particular the row owner seeing both representative coins does not grant physical joint observation or prove equality of actual early-input transcripts.

Only now invoke the earlier fixed-cylinder CFS comparison theorem: each actual realization of this labelled cylinder has its comparison span to the common canonical middle; the explicit realization maps above induce the source-changing normalizer cells. Record grouping triangles give their corresponding compatible cells under the proved normalization rule. No finite/executable nature of the canonical middle, and no physical section, is inferred. This is an application of the existing machinery, not a new lifting theorem.

Actual service soundness is even more direct. On E every physical captured support in K_phys satisfies all learned local equations. Summing them gives p+d=0 on every possible actual service record. The same physical controller therefore passes the actual interlock and completes if its unchanged capability/deadline envelope fits. This is one controller across K_phys. It does not run the V sampler to predict a fresh physical coin.

The older `Timed_First_Loss_Assurance.md` §§1–7 gives a compatible broader assurance pattern but is not needed to invent new probability here. Exact chart re-expression preserves that theorem's first-loss/exposure certificates only when its source actions, augmented adapter histories, coverage gate, physical timing/labels and source kernel are preserved. The parity result establishes its own zero-loss implication on the restricted Q cylinder; it does not claim full-history conditional-TV agreement to arbitrary physical controllers.

## 5A. Actual deterministic controller substitution, not only a simulator comparison

The previous positive-law layer can be connected to actual constrained execution without treating representative coins as physical innovations. Replace each representative source cell by the already permitted real sensor delivery of zi, and replace r_i in the computation by a NEW controller register p_i. Set p0 to the actual captured r0. The physical environmental r_i remains only an evidence/readout variable; the controller does not read it during service.

For every deterministic early input stream (r0,z1,...,zn), regardless of its distribution or unresolved correlations, both owner charts compute

    p_i=p_(i-1)+zi, hence p_n=r0+sum_i zi.

Proof: for tile input a=p_(i-1), both charts output the same controller values (u,a+u,v,a+u+v), now with u,v supplied by real sensors rather than freshly drawn coins. The identity is pointwise; induction over actual parity seam deliveries proves equality at the actuator. No independent-zi hypothesis is used for controller substitution. Local support evidence then supplies the separate implication p_n=d on E. The common deterministic input/output implementation is therefore valid for EVERY physical input law in K_phys, although the common stochastic V sampler is not that law.

The actual-controller comparison preserves source/capture and actuator/gate identities and the logical accumulator values. Each implementation retains its OWN explicit register/channel ownership and cost ledger; row sends uv whereas column sends b, so their deployed message/resource histories are not claimed bijective or equal. Logical register labels are linked by the pointwise recurrence, not treated as duplicated physical memory authority. This comparison is distinct from both the representative coin-event maps and the H_f bijection for its deliberately common witness schedule. Pointwise actuator equality plus separately checked physical resource/time guards is the required controller-transfer guarantee. A component cannot read the sampled physical load d before committing its prediction unless the original service protocol explicitly admits that observation; this construction does not require it.

**Concrete charged timing/capability fixture.** This is a named implementation subclass, not measured hardware or an assumption silently added to all platforms. All n+1 early bits are captured at physical time 0 and available at time 1 in the already charged n+1-bit distributed capture bank. The one-tick capture/availability envelope is a supplied capability. Register r0 initializes the first accumulator input. A XOR instruction takes one tick; a permitted channel sends a word of its declared capacity in one tick; selected output-gate setup takes one tick. Every intermediate delivery is executed, not inferred from a simulator event.

For each tile use these sequential schedules:

- Column implementation: XOR p_(i-1) with zi (one tick); send the resulting p_i to the second owner (one tick, one bit); XOR with z_(i+1) (one tick).
- Row implementation: send the pair (zi,z_(i+1)) from the capture owner to the accumulator owner (one tick, TWO-bit capacity); perform the two XORs (one tick each).

Between consecutive tiles send the final parity bit to the next tile (one tick). After the last tile issue the gate/actuator setup (one tick). Therefore completion of the prediction and gate setup is at

    t_ready = 1 + 3m + (m-1) + 1 = 4m+1 = 2n+1.

Column sends n-1 internal/intertile bits; row sends 2m+(m-1)=3m-1. The actuator command is common and excluded from both counts (add its one-bit command to each if counting it). The same n XORs, n+1 captured-bit storage and one physical actuator are used. Static code/identifier storage and monitor storage remain charged separately. A row owner cannot obtain its two input bits by unrestricted broadcast: the named two-bit delivery is the exact required primitive.

Let the physical slot/capture guard require prediction and setup by L minus a supplied margin mu. Both implementations pass the same ready-time guard 2n+1<=L-mu under these unit envelopes, with equality allowed only if the certified gate-ready event precedes the load pulse at that boundary; otherwise require strict inequality, and the same final physical drain/tail is appended. For arbitrary certified primitive latencies, substitute their actual sums into the displayed schedules and check the guard separately for each chart. If the row channel has capacity one, transmitting the pair needs two charged sends: the simple serialization gives t_ready=2n+1+m. A different parallel or pipelined implementation is allowed only with its own proof and resources. Equality of function does not give equality of affordable deadline.

The positive fixture is nonempty for an unbounded growing family. For each even n choose, for example, an integer margin mu>=0 and L=2n+2+mu, D>=L, H>=L+1. Use the predecessor's stationary filter with r_i(t)=R(t)+sum_(j<=i)Zj(t) and d(t)=R(t-L)+sum_(j<=n)Zj(t-L). Its selected early captures and delayed load satisfy all local equations, while the independent-zi and z1=z2 versions still share the same retained probe laws. Give the acquisition/compiler/service budgets their displayed finite bounds and the stated gate/capture permissions. Both controller charts then complete before L-mu, and local source grouping is still not identified. This is a conditional mathematical witness, not empirical validation of those supplied hardware envelopes.

These module replacements use no new environmental experiments or readout capabilities. They do require the listed local computation/delivery permissions; the capability checker may find either or both absent. If the original platform only supports its serial accumulator, it retains that old policy and the corresponding certificate; this theorem does not declare it incapable merely because a new chart is unavailable.

**Actual constrained-agent invalidation.** Consider the row implementation with one missing timely u=zi delivery. Restrict the declared policy class so that before actuator commitment there is no alternative path to u: no direct sensor access by the actuator-side controller, no intermediate environmental r_j carrying u, no observation of d, no shared seed determining u, and no timing/resource side channel encoding it. Previous calibration is on independent fresh blocks. For any retained K_phys containing the independent-zi physical witness (in particular the growing fixture above), in that witness u is fair conditional on all permitted precommitment information; all other bits and controller randomness leave that uncertainty intact. Thus any committed prediction has Pr[p_hat!=d]=1/2. Aborting has missed-completion probability one and cannot lower this bound. Therefore no policy in this restricted architecture has uniform missed-or-unsafe risk below 1/2 across such a K_phys. Additional evidence or prior guards may exclude that witness, in which case this particular lower bound is not asserted. This is a genuine capability/communication obstruction, not merely an inaccessible simulator variable.

Restoring one authorized timely u bit (or an authorized sufficient parity bit) restores the deterministic module proof. Its communication, mailbox, computation and deadline costs must fit the remaining opportunity. If the bit cannot arrive before commitment, repair fails for that mission even if it is eventually observable. Other architectures or the old serial controller may still succeed; this is not a universal agent impossibility theorem. In worlds with extra correlation, such as z1=z2, u may be inferable, which is why the negative statement is uniform across K_phys, not impossibility in every world.

## 6. Certificate format and implementable transfer algorithm

Input to compilation:

- a versioned acquisition record with probe/capture maps, up to three basis rows per triple, endpoint basis, sample counts and freshness/isolation provenance; each basis must reference an already verified original sample-to-span computation, or the checker must recompute it from the retained samples;
- the original physical premise/guard versions and full evidence-class description K_phys (not an enumerated list of worlds);
- n, chosen delay slot, exact clock/gate/service envelopes and capability inventory;
- the common local source/XOR templates and the requested ownership chart;
- the machine's bounded costs for the finite operations below.

Retaining K_phys means retaining its finite defining evidence/premise record, not enumerating physical models. The algorithm may operate with its sound selected-chain relaxation but may not claim that relaxation is exact physical uncertainty.

Algorithm:

1. Check n even, capture/occurrence IDs distinct as required, all triples refer to consecutive chain occurrences, endpoint refers to rn and the selected load capture, and counts/provenance/versions satisfy the acquisition contract. Reject any missing guard.
2. For each triple basis (at most three 3-bit rows), enumerate its span using at most 2^3 subsets and compare its 8-bit membership mask with the hard-coded XOR-plane mask. For the endpoint use at most 2^2 subsets and compare with the 4-bit diagonal mask. This checks exact full-plane support, not just that sampled rows satisfy an equation.
3. Emit one source cell per zi, initial r0 source, XOR cell per i, terminal d-copy, fixed event IDs and the named channel/authority table. Emit two owners per tile with their selected C or R ownership. All source IDs refer to the same common witness, not fresh chart-specific seeds.
4. Enumerate a,u,v in {0,1} for the ONE template. Check nonnegative weights summing to one for each a, both owner recurrences, equal four-output labels, and the seven-step register/permission schedule. If a template implementation differs, check it anew. For each tile check its index substitution, source IDs, incoming/outgoing parity IDs and resource permissions against this verified template. No global record enumeration is needed.
5. Emit/check the linear telescoping certificate: a length-n list of local equations, their XOR cancellation order, and the endpoint equation. Verify each internal r_i occurs twice and r0, all zi and d once. Conclude Q is diagonal. The full terminal span proves its nonzero diagonal value occurs, hence the uniform Q-cylinder map; no enumeration of V is needed.
6. Retain the original mission policy and actual physical capability/timing/risk guards, or select one of the pointwise-equivalent deterministic controller modules of §5A and check its OWN physical delivery/latency schedule. Add chart representation/checking costs, and, only if requested, the separately scheduled witness-execution cost. Check total remaining opportunity. Reject rather than silently adding an input read, shared source, message permission or time allowance.
7. Output a certificate tagged by the hash/version of the complete input evidence/premise record, the selected-coordinate projection, the requested chart, common witness IDs, permitted Q tests, cost envelope and confidence allocation. Output also the explicit local projection/grouping functions and proof-rule tags to the already checked cylinder construction.

Transfer C->R or R->C keeps steps 1,2,5 and physical service guards only if their dependencies' versions are unchanged. It regenerates ownership/delivery permissions and checks steps 3,4,6,7; it never resamples acquisition evidence or independently re-fits each chart. If both target permissions pass, the common H_f construction proves transfer. If permissions fail, return `UNRESOLVED/unsupported chart` or the explicit information-deletion `NO under these permissions`, not physical mission incompatibility.

## 7. Explicit size and cost envelope

The compiler is a finite algorithm with a certifiable operation ledger. We do NOT infer a particular machine-step constant from an informal O(n) claim or from the regression verifier. Timely certifiability is conditional on the matched implementation supplying valid costs for the elementary routines listed below.

Let K be the full original number of probe types, M=max sample count, d_phys the number of ambient physical ports, and I_max the largest numeric identifier/offset in the encoded input. Choose a word width sufficient for all indices, counts and time bounds, for example

    w_bits >= max(16, ceil(log2(16(n+K+M+D+H+B+d_phys*H+I_max+2)))).

Opaque strings, provenance hashes and longer rational/time/confidence encodings keep their actual lengths; parsing and exact arithmetic on those payloads are separate costs C_io and C_num. No oversized datum is silently packed in one word. Every chart record contains a fixed list of typed fields (tag, owner, source/target ID, value-slot ID and timing/permission reference); expanded schedule records use seven entries per tile plus the three initialization/terminal entries. The compiler's schema emits n+1 source records, n XOR records, one terminal-copy record, two owner records per tile, the named channel/register records, those schedule entries, and the evidence/dependency records. The exact emitted field count F is recorded by the implementation; each field is individually type/bounds checked. All these lists have O(n+K) fixed-width fields, but arbitrary physical certificate payloads and retained raw samples are outside that small-list claim.

A concrete ledger for the algorithm is:

1. **Input/ID checks.** Let J be the length of the distinct-capture/occurrence identifier inventory and R the number of indexed references in the input/output schema. Validate each inventory entry once, compare every unordered pair for forbidden aliases (J(J-1)/2 comparisons), and verify each indexed reference once. This is deterministic quadratic validation, not assumed constant-time hashing. IDs intentionally reused as references are not mistaken for distinct capture entries. Charge J c_id + J(J-1)c_cmp/2 + R c_ref.
2. **Sample-to-span verification.** Either use a valid previously checked sample-to-span reference and charge its verification, or stream every sample through a fixed k_e-row binary elimination array. At most k_e row tests and k_e row-XOR updates occur per sample. Charge sum_e m_e k_e(c_test+c_rowxor(k_e)+c_loop), plus its actual record-read/provenance cost. Here c_rowxor(k) is the certified cost of XORing a k-bit row, not a unit-cost unbounded matrix operation. For k_e<=3 this is a bounded local routine.
3. **Full-support masks.** Let E_chain be exactly the n chain triples plus the ONE selected endpoint. For each e in E_chain enumerate its at most 2^k_e subsets, form each subset sum with at most k_e row XORs, and set its membership-mask bit. Then compare the mask to the plane/diagonal mask. Charge sum_(e in E_chain)[2^k_e(k_e c_rowxor(k_e)+c_mask+c_loop)+c_maskcmp]. Empty or redundant rows do not bypass the complete mask comparison. Unselected candidate-delay endpoint supports may legitimately be full and are NOT required to match the chosen diagonal mask. Their original consistency/delay-selection checks remain explicitly charged in C_old unless separately itemized.
4. **Template check.** For each of the two charts enumerate eight (a,u,v) inputs, seven elementary schedule transitions, and four output values. Charge at most 112 c_transition +64 c_bitcmp +4 c_normalize, where c_transition is the cost of checking the fixed finite transition/permission table and c_normalize checks its two-point/four-point source row. These routines have explicitly fixed-size arguments; their implementation costs must still be certified. The deterministic physical-controller templates are checked separately on the same eight input triples; charge their exact transition count and output comparisons, denoted C_controller_template.
5. **Instantiation and maps.** Emit and check every schema field once using its canonical loop index, including source identity, owner, channel and incoming/outgoing parity links. Charge F(c_emit+c_fieldcheck). The direct array indices make this a bounded field loop; external identifier equality costs remain in item 1. Check the n telescoping equation entries and endpoint, using a 2n+2-entry occurrence-parity counter array. A literal loop initializes each counter, visits the three entries per chain equation and two endpoint entries, and checks each final count. Charge (2n+2)c_init +(3n+2)c_toggle +(2n+2)c_countercheck, plus indexed-list access costs.
6. **Guards and schedule.** Sum the listed physical-controller transition latencies, channel capacities, storage and tail demands; compare with the supplied capability/remaining-budget bounds. Charge the actual finite schedule-list traversal and exact arithmetic, C_schedule+C_num. The independently supplied physics/provenance/old-check payload verification costs remain C_phys+C_old+C_io; they do not absorb or erase the algebraic loops 1–5.

Define C_chart as the sum of items 1–5 EXCLUDING the separately named C_controller_template, using the matched machine's certified routine-latency upper bounds. Item 6 contributes the remaining separately named terms. Thus

    C_compile = C_chart + C_controller_template
                + C_schedule + C_num + C_phys + C_old + C_io,

Each term is counted once. Implementations should record the six numbered subtotals to prevent ambiguity. This is an explicit cost formula, not a promised universal numerical instruction bound. A word-machine implementation supplies the routine latencies; a bit-machine expands the same loops with its actual bit costs. If those latencies or the physical payload checker are not certified, the finite mathematical certificate exists but timely certifiability is NOT established.

Storage is the sum of the actual typed-field lengths F*w_bits (for fixed-width fields), the J-entry ID inventory, the 2n+2 counter array, the tiny per-probe basis/mask/count arrays, and the separately sized external payload/retained-sample storage. Streaming span recomputation needs at most k_e^2 basis bits plus counters for the currently processed probe, provided its input records can be streamed with charged access. Simultaneously retained evidence bases take sum_e k_e^2 bits plus their actual counts/IDs. The actual physical controller capture bank needs n+1 bits in the simultaneous-capture fixture and is charged separately. The O(n+K) chart size is not a claim that all original evidence, monitors or physical certificate payloads have that size.

For charts used only as certificates, total initial opportunity required is

    D + sum_e m_e c_e + C_compile + C_service,

with final freshness/drain already included in c_e/C_service as in the original theorem. If acquisition elimination is already charged in c_e and is rechecked here, this deliberately charges the recheck too; a referenced already verified computation instead uses its reference-verification cost. C_old retains original checks not subsumed by the specialized loops. C_service is the selected actual controller's checked physical schedule and complete tail. Witness simulation, if run, additionally costs its 7m+3 elementary witness ticks and stated storage/communication; it is unnecessary for physical mission certification.

Representation/checking cost can therefore alter certifiability despite equality of the restricted mission law. The common witness schedule has equal ticks by deliberate retention of copies; the physical controller implementations have equal ready time only under the specific matched §5A primitive capacities/latencies. Neither statement asserts equality of all optimized implementations.

### 7A. Executable normalized-schema implementation

The delivered manifest pins the exact compiler, ledger note and replay versions cited in this subsection.

`compile_crossing_certificate.py` instantiates the finite algorithm for a declared normalized special case. Its admission layer requires validated even n>=2, fixed-width typed arrays, canonical injective capture/source namespaces, retained valid evidence/K/confidence/physical-premise references, nonnegative finite numerical fields and word-width bounds covering every intermediate arithmetic result, including rejected paths. Original source-to-span correctness and physical provenance are verified before admission; the core does not establish them by copying a token or checking a Boolean.

The compiler checks every selected triple's full plane mask and the selected endpoint diagonal, verifies canonical occurrence links and source IDs, executes the fixed local template checks, emits owner/cell records, checks telescoping, and checks the selected physical-controller capacity/time/service envelope. It is a finite actual program, not just an existential certificate search. The named physical fixture is §5A's supplied unit-cost implementation, not the witness sampler clock. Positive replay uses load slot 2n+2; readiness 2n+1 is admissible at an equal slot only with a separately verified ready-before-load event ordering.

Its explicit abstract word-RAM counts fixed-width reads/writes/arithmetic/tests/branches and initialization, including loop overhead. For every admitted successful even-n input the phase ledger is:

    header 22; references 27; source IDs 8n+11;
    plane checks 324n+125; template 288; assembly 64n+4;
    telescoping 49n+45; guards 53; opportunity 13; output 9.

Mask initialization and each subset accumulator reset are explicitly charged immediate-register writes (nine additional operations per triple and five for the endpoint relative to a ledger omitting those writes). Adding the displayed terms gives exactly **445n+597** operations. This is derived by the program's fixed loop expansion, not inferred by regression interpolation or Python wall-clock time. The detailed expansion and admission exclusions are in `verification_crossing_compiler.md`. Rejected admitted inputs exit earlier and do not exceed the successful bound. The separate normalized compiler workspace admission requires 32(n+16) words; capture-bank and external evidence/payload storage remain separate.

Thus this implementation's sufficient remaining-time test is

    b_remaining >= C_norm + C_phys
                   + tau_word*(445n+597) + C_service.

C_norm includes parsing/type/range checks, canonicalization, original-ID injectivity validation and arithmetic-width/workspace admission. C_phys includes the actual original evidence/provenance/guard verification or their valid dependency references. Any sample recomputation or old checker work not yet verified is added there explicitly, not omitted. The fixed linear core bound does not cover arbitrary names, sorting, variable-length hashes, raw samples or external physical proof payloads. tau_word is a supplied upper bound for this abstract machine or a certified implementation thereof, not a measured claim about Python. Compilation consumes no additional statistical error allocation.

The finite replay checks both target charts for n=2,4,6,8,16,32 and eight mutated invalid inputs, and agrees with the all-n operation ledger. These checks corroborate the explicit compiler; the general positive/cylinder/physical arguments above are not reduced to these finite instances. The broader ledger in §7 remains applicable where this normalized admission contract is unavailable.

## 8. Refinement and guarded reuse

At the SAME physical state, remaining budget, mission and policy protocol, K_fine subset K_coarse implies every policy uniformly successful on K_coarse remains successful on K_fine. This elementary law applies to nonempty physical model classes; it does not certify the affordability of rechecking. Executing acquisition changes state and budget and must use the full cost ledger.

Pure chart re-expression changes neither K_phys nor the actual service observations. New source IDs, enlarged owner views, faster assumed messages or relaxed timing are not pure presentation changes. Their authorization/cost/semantics must be rechecked. A capability enlargement preserves old policies only through a feasible causal embedding retaining their costs and executions.

The certificate dependency record invalidates reuse when: source/calibration regime changes; a local support relation or its provenance is retracted; capture identity/delay choice changes; selected Q is enlarged; gate/interlock/timing authority changes; or target chart permissions/costs fail. Unrelated additional evidence can shrink K without invalidating the old proof, provided state/opportunity guards still hold. Failure of compilation/refinement is not a universal physical NO.

## 9. Matched obstruction and repair proofs

### 9.1 Missing local information

Keep the positive V tile and fixed a,v. Delete every delivery of u (or an equivalent sufficient function) to the parity owner in R. Its allowed input is (a,v), public phase and private randomness independent of u; it has no access to the u event provider, a shared seed determining u, an observation of b, or a later channel revealing u before b must be output. This is the precise permission class.

Conditional on that allowed information u is fair. Any possibly randomized output b_hat therefore has Pr[b_hat=a+u]=1/2. Exact pointwise/common response realization is impossible, regardless of the size of the owner's unrelated private memory. This is a direct implementation-class NO, not an obstruction to the physical parity mission under another controller.

Repair: authorize delivery of one bit u, or equivalently b=a+u from an authorized provider, before the required output. The one-bit message restores the explicit recurrence. Its repair ledger includes one single-bit channel/mailbox, the event/permission ID, one send/copy slot and its latency/buffer cost; a request protocol adds any receive/handshake costs. In the canonical schedule this is precisely step 2, already budgeted. If repairing a schedule from which it was removed, add its full cost and recheck deadline. Merely granting access to a common source is an alternative capability change, not a zero-cost consequence of shared notation. This repair has no new statistical delta because it does not learn a physical relation.

### 9.2 Retracted chain evidence on the SAME physical family

Delete one retained triple constraint k but keep every other triple law and the endpoint law. A good physical source uses independent fair R,Z1,...,Zn, with r0=R, zi=Zi, r_i=R+sum_(j<=i)Zj and delayed d=rn. A second stationary finite-memory source additionally uses a fresh independent fair E and defines

    r_i=R+sum_(j<=i)Zj + 1[i>=k]E,
    d=R+sum_(j<=n)Zj+E

at the same capture-relative delays. These are linear filters of the original physical class; select their output lags exactly as in the predecessor's physical construction. Initial/fresh-block timing remains unchanged.

For every i!=k the equation r_i=r_(i-1)+zi holds and its triple has full plane support: conditional on zi, the independent R masks the preceding parity. Endpoint is the full diagonal. Thus every retained probe law agrees with the good source. At k the bad source has the full three-dimensional triple support. The old p+d equals E, so its actual hazard risk is 1/2. Retaining the zero-risk certificate after retraction is unsound. This proves failure of that certificate/old policy under the enlarged uncertainty, not impossibility of all policies with additional service observations.

For optional delay acquisition, retain this obstruction only when the unselected candidate-slot probe laws agree as well; the stationary family with independent innovations at distinct time indices and nonmatching endpoint pairs full supplies such a case. Alternatively use the fixed selected-delay subfamily, which is already within the theorem's class. Do not claim the obstruction for arbitrary extra evidence that already reveals E.

**Repair after evidence loss, unchanged good physical regime.** Reacquire the missing triple on fresh isolated blocks, with the probe selected before each activation. Choose a new confidence allocation delta_r and

    m_r=3+ceil(log2(1/delta_r)).

Conditional on all past completed data and on a current fresh-start boundary, future blocks have the unchanged filter's independent uniform projected law. The span failure probability is <2^(3-m_r)<=delta_r, so the repair event E_r has conditional probability at least 1-delta_r. Randomly deciding to repair from prior data does not change this bound. Selection based on unreleased values or gap observations would invalidate it.

Check the newly learned span against the XOR-plane mask, replace only the retracted evidence entry, and rerun the global equation/dependency/budget checks. In a genuinely good unchanged source, on E_r the original certificate is restored. In the bad injected-E source, on E_r the full triple is recovered and the old certificate is refused. Reacquisition does not repair bad physical dynamics.

The remaining-budget requirement is

    b_remaining >= C_boundary + m_r c_k + C_recheck + C_service.

C_boundary includes any outstanding physical drain and the time to the first valid fresh start; each c_k reserves the complete fresh-block/sensing/update/drain interval, including the final repair-to-service transition. Storage is at most three new 3-bit basis rows, their count and provenance metadata, plus existing checker workspace. One conservative C_recheck is C_compile from §7; a dependency-aware local version may be cheaper but is not assumed.

The combined success-confidence claim for retained old relations and the new repair is at least 1-delta_old-delta_r, by union bound; delta_old is the valid simultaneous failure allowance for retained old evidence. Repeating repairs uses separately allocated delta_r,j with their sum charged, or another proved sequential confidence rule. It is invalid to reuse the same unconditional delta for unbounded retries. If the physical mechanism actually changed, the old stationarity guard fails and the untouched old relations require independent revalidation; this one-probe repair theorem no longer applies.

## 10. Scope and completion criterion

The construction proves a bounded operational crossing bridge on an existing growing evidence-bearing family: local positive sampler, distinct crossing owner views, source-preserving common refinement, explicit same-cylinder maps, uniform physical mission certificate, checked costs and matched guard repairs. It uses standard XOR/linear-support reasoning and the already proved common-response/normalizer tools. It does not identify the true physical source factorization, reconstruct arbitrary hidden state, preserve all-context laws, or solve universal fixed-endpoint lifting.

Finite checks should exercise the local scheduled charts, grouping identities, source/resource tags, physical retraction witnesses and compiler cost/count invariants. They are regression evidence, not a replacement for the argument above. Scoped acceptance requires independent audit of these exact claims and any implementation. No full RC4 equipment/representability/CULF/I5 or RC7 completion follows, and no contract ledger is amended.
