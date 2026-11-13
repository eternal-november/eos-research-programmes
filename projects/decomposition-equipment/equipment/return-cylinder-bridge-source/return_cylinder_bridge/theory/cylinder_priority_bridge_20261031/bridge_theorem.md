# Shared-priority constraints as a two-sided cylinder wiring instance

31 October 2026. Scoped theorem: concrete instantiation of existing machinery, not a new generic CFS theorem. No claim of whole-contract completion, new physical hardware, or adequate-CFS span functoriality.

## 1. Source definitions and dependency boundary

The operational source is `../local_wiring_transport_20261031/transport_theorem.md` §§2–6: one required job per module, all-ready atomic batch, intrinsic lower work bounds exceeding callback jitter, one persistent strict priority, and sound acquired comparisons P. These derive rank=priority order and one common assignment sigma in LE(P). Section 4 proves the exact role-parity certificate; that proof is imported, not repeated.

The doctrine is **Boolean complete modules** (complete join-semilattices with join-preserving maps), as constructed in `../cylinder_audit/quantale_module_joint_wiring.md` §§0–4. For a Boolean kernel phi:A×B→2, the actual discrete cylinder has object 2 at each preparation a and each test b; entry 2→2 is multiplication by phi(a,b). The E-cocone generates and the M-cone separates; its canonical middle is im(phi_!:2^A→2^B), the union-closure of its rows. Both labelled legs are retained. It is NOT Set's bare set of rows, and NOT an Isbell fixed-point lattice.

The applicable wiring theorem is that note §4 (explicit same-witness contraction), with normalized substitution from §§2–3, or equivalently `compact_boundary_cfs_wiring.md` §§1–4. We do not invoke `general_adequate_cfs_span_criterion.md`: its adequacy hypotheses do not follow for surjection/injection image CFSs. Nor do we assert a lift of arbitrary raw comparison spans through tensor.

`joint_comparison_bridge.md` §§2–4 supplies the already established warning: existential support inclusion is not a same-cylinder map, and local fiber nonemptiness is not fiber overlap. The construction below supplies actual overlap witnesses rather than restating that warning.

## 2. Fixed operational boundary and cylinder

Fix n, the job labels J, roles rho:J→R, an acyclic P, the all-ready productive batch interface, and the supplied physical bridge. Let B={0,1}^n be possible observed rank-bit words and Y={0,1}^R be candidate physical role-command vectors. Define

  K_P(b,y)=1 iff there exists sigma in LE(P) with
  y_a = XOR_{k:rho(sigma_k)=a} b_k for every role a.

Here b is a **formal external context parameter**, not a controllable physical preparation of uncontrollable bits. The kernel is a conditional possibility/constraint relation; it is not a stochastic kernel and is not claiming a physical intervention setting b. Each test y asks whether y is compatible. A hard-safe useful output at b requires that this row has exactly one member. Nonemptiness follows from acyclicity. Section 4 of the operational theorem decides precisely this singleton property.

The finite relational construction below computes K_P from local primitive constraints. It does not take this entire global table as supplied input.

### 2A. Actual operational profile comes first

The physical preparation profile here is the singleton {p_0}: run the declared safe commissioning diagnostics, drain, and admit the fixed all-ready productive batch on the supplied hardware. The retained commissioning record E is conditioning evidence about that execution, not an actuator. The physical external trace is (fixed timing, observed rank word b); y is the role-load response computed from the actual addressed productive invocations under the supplied physical bridge. Test labels (b,y) are semantic response predicates on that joint execution. They need not be online sensor queries revealing y to the controller. Omitting that distinction would grant exactly the source attribution the problem lacks.

Its evidence-relative ASSURANCE SUPPORT cylinder is

  H_E(p_0,(b,y))=1 iff a legal world/run consistent with E has word b and response y.

Thus the physically grounded preparation is p_0, never b or P. For the §6 fixture, H_E(p_0,(b,y))=K_P(b,y). In general only inclusion holds. K_P displayed as a B×Y matrix is the conditional-section presentation of this response relation; treating it as its own mathematical cylinder is useful but does not make its B-index physically controllable. No claim is made that the canonical middle of H_E is identical to that of K_P: changing the preparation/test split changes the CFS factorization.

To realize the actual profile H in the same constraint network, move b from the formal input to an external OUTPUT, add a full-support bit-generator relation G: {*}→{0,1}^n (or n unary full-support generators with equality copy wires), and use external output (b,y). This is an exact support interpretation of the fixture's uncontrollable fresh fair bits, not a controllable generator. The single external input is p_0. The resulting contraction H_N(p_0,(b,y))=K_P(b,y) follows from the same witness bijection. This supplies the honest assurance-profile cylinder independently of the conditional-section convention.

## 3. Actual primitive network, including its shared-variable wiring

Use hidden variables x_j in {1,...,n}, one for each job. Equality wires COPY EACH SAME x_j to its occurrences. Add the following finite Boolean primitives:

1. For each unordered pair of jobs i,j, the factor D(x_i,x_j)=[x_i!=x_j]. Since n distinct values lie in an n-element set, these factors force a bijection job→rank.
2. For each retained generating edge i<j of P, the factor C(x_i,x_j)=[x_i<x_j]. Its meaning is supplied by the acquired sound comparison on the same persistent arbiter. Transitive closure may replace the generating edges without changing solutions.
3. A selector for each job, S(x_j,b,c_j)=[c_j=b_(x_j)]. The vector b is one shared external parameter copied to these selectors, not independently chosen copies. If desired this finite selector can be expanded into rank-equality and Boolean gate factors; no physical access to the latent x_j is being granted.
4. For each role a, an XOR chain over exactly the c_j with rho(j)=a, initialized at 0 and terminated at the external y_a. Empty roles terminate at 0. Every chain intermediate is a shared wire with equality gluing.

All factors are their FULL joint relations. A factor can be oriented as a kernel from its complete input tuple to the singleton output {*}; copier relations distribute shared values. Terminal constants and y equalities are additional Boolean effects. This is a finite typed constraint diagram in 2-Mat, with declared equality/copy couplings. It need not be a physical causal scheduler or a directed acyclic circuit; its semantics is finite existential constraint gluing.

For complete internal assignment z (all x_j,c_j,chain values and copied-port labels), let F_v be these primitive factors. Then

  K_N(b,y) = OR_z AND_v F_v(local boundary values from b,y,z).

A satisfying z gives the unique permutation sigma obtained by sorting x_j; the D and C factors give sigma∈LE(P), selectors assign the actual rank bits, and XOR chains give y=V(sigma,b). Conversely any such sigma and b determine x,c and chain values satisfying every factor. Therefore **K_N=K_P**, in both directions. The equality-wire condition is the exact primitive witness-alignment law, proved here from a single assignment, not an assumption that reconstruction preserves compatibility.

Unused copy-wire values are constrained by their copier factors; no independently chosen representatives are inserted at a cut. Evidence grouping only repartitions this conjunction. With P=tc(union_i P_i union E), its solution set is exactly the intersection of constraints on this ONE bijection x. Cyclic P gives no solutions and must be rejected as evidence inconsistency before mission certification, as in the operational theorem.

## 4. Explicit two-sided carrier and comparison

Let M_v be the canonical Boolean complete-module middle of the primitive joint kernel F_v, with its preparation elements alpha_v and test maps beta_v. These are small finite-factor descriptions, not promises that every completed element is physically executable. Let Z be the set of complete internal wire assignments and put

  X_N = direct_sum_{z∈Z} tensor_v M_v.

The existing theorem gives concrete legs, here with external parameters b and y:

  e_N(b) = OR_z i_z(tensor_v alpha_v(in_v(b,z))),
  q_N(y)(i_z(tensor_v m_v))
         = AND_v beta_v(out_v(y,z))(m_v).

Boundary orientation can place b on input wires, y on output wires, with all other factor inputs supplied by z; terminal effects have singleton output. On a single z-summand both sides use exactly the same x values and all other shared variables. Consequently

  q_N(y)e_N(b)=OR_z AND_v F_v(...)=K_P(b,y).

Thus this is an HONEST realization of the declared cylinder, not merely a carrier for marginals. Let U_N be the submodule generated by all e_N(b). Evaluation into 2^Y has image

  M_P = im((K_P)_!:2^B→2^Y).

The comparison is exactly

  X_N  ←[injective, M_0]  U_N  →[surjective, E_0]  M_P.

Both arrows preserve the preparation and test legs of this same cylinder. The right map sends e_N(b) to K_P(b,-), and the left map is inclusion. This explicitly fills the honest-realization premise needed by the old construction. The singleton certificate is a property of the labelled generator K_P(b,-); unions of other rows in M_P need not be singleton and need not represent physical preparations.

### Assurance-profile factorization, not just the conditional-section factorization

Apply the same formula to the network with the full-support bit generators from §2A. Write its carrier X_H, its single preparation e_H(p_0), and its tests q_H(b,y). Then

  q_H(b,y)e_H(p_0)=H_N(p_0,(b,y)),
  X_H ← U_H ↠ M_H=im((H_N)_!:2→2^(B×Y)).

For a nonempty profile this image consists of bottom and the entire joint support; it is deliberately NOT identified with M_P. The formal singleton-preparation completion is small because this selected test/preparation split is coarse; it does not discard the labelled support predicates. Mission certification conditions on the observed b and asks whether the y-fiber of that support is singleton. Those fibers are exactly the rows of K_P. Hence the operational certificate reads sections of the honestly realized assurance response relation, without turning conditioning into physical control. Only on §6's exact fixture is H_N=H_E; otherwise this is an overapproximate physical response relation.

## 5. Precisely proved coherence

Regroup the SAME factors into subnetworks, retaining every exposed shared variable and both local legs. Expanding the witness-indexed carriers gives the same tuple of internal assignments and same tensor factors; the canonical tensor/coproduct distributivity and reassociation maps preserve e and q. This is the old theorem's witness-preserving raw flattening specialized to priority, with its semantic premise established by §3.

Alternatively normalize each subnetwork, retaining its complete exposed boundary kernel. Serial image composition and parallel normalized tensor composition then reconstruct the same conjunction/existential kernel K_P. Canonical image-factorization uniqueness gives the unique isomorphism of final middles preserving all b/y labels. Associativity and units follow from equality on labelled generators and tests. Inserting identity factors need not preserve raw X_N, only the normalized middle. This is coherent normalized constraint wiring, NOT an invertible raw-span compositor theorem for arbitrary image CFSs.

Eliminating a rank variable before its last external use is allowed only if the resulting JOINT boundary relation is retained. Independent projections per outgoing port do not satisfy this premise. Grouping changes neither job IDs nor the single global priority witness; adding per-group arbiters is a different network.

## 6. Operational identification: exact in the fixture, one-sided generally

For arbitrary retained physical data E, define F_E(b) to consist of priority assignments that extend to a physical world/run reproducing the ENTIRE retained diagnostic and productive record, with word b and all primitive guards. The operational theorem proves F_E(b)⊆LE(P), not equality. Therefore the actual physical possibility cylinder K_E satisfies K_E≤K_P. A singleton nonempty K_P row certifies the actual role vector; a nonsingleton row is only UNRESOLVED. A support inclusion does NOT turn X_N into a realization of K_E, nor give an equality-preserving CFS comparison to its canonical middle.

There is an exact concrete instance: the operational theorem §5's equal productive demands Q, zero jitter, fixed productive timestamp sequence (Q,2Q,...,nQ), and retained slow/fast pair diagnostics giving precisely selected comparisons P, with the permissive fair-bit payload fixture of §7–8. For every sigma∈LE(P), each retained pair diagnostic has the same times because its tested comparison agrees; its complete observed bit word has positive probability by the independent fair-bit law. The productive timing is common across sigma; assigning productive payloads by rank realizes any prescribed b with positive probability. Hence every sigma has a full-record witness. Conversely every physical witness satisfies P. Thus F_E(b)=LE(P) and **K_E=K_P** on this fixed context family. The carrier and comparison in §4 now realize an evidence-relative physical assurance support cylinder, with no false inference of probability equality.

This is conditional support over retained records, not a posterior prior over sigma; no distribution on priorities is introduced. Extra diagnostic records, unequal demands, informative timestamps, new release patterns, different roles, or new tests require a new full-record fiber proof. The role-word quotient is task-relative, not a context-complete physical state reconstruction. Explicitly, priorities (x,z,y) and (y,z,x), with roles rho(x)=rho(y)=A and rho(z)=B, share productive role word ABA. The already admitted safe diagnostic D_x/P_z has first arrival 2Q in the first priority and Q in the second. Thus even the existing diagnostic context distinguishes states identified by the fixed-productive-batch role-word quotient. Extending the profile to include these preparations requires retaining the priority distinctions; there is no context-congruence theorem.

## 7. The four-job witness pinpoints the obstruction

Take jobs 0,1,2,3; roles A,B,A,B; P generated by 0<3 and 1<2; b=0011. The six extensions listed in the operational theorem all give y=11. Thus the actual fixture row K_P(0011,-) is the singleton {11}.

Replace the retained joint rank constraints by only their job-wise projections: x_0,x_1∈{1,2,3}, x_2,x_3∈{2,3,4}, still requiring distinct ranks. The assignment x=(1,3,2,4), equivalently rank order (0,2,1,3), survives but violates 1<2 and yields y=00. The relaxed row includes {00,11} (indeed these are its only possible vectors since the total input parity is zero).

This is a different cylinder. Any putative map between its decorated realization and the exact one preserving BOTH b-preparation and y-test legs would force equality of all scalar entries. At b=0011,y=00 those entries are 1 and 0, so such a same-cylinder map is impossible in either direction. This elementary obstruction applies to these actual operational kernels; no generic row-kernel counterexample need be rerun.

Repair is not an extra categorical axiom: retain the edge factors on the shared x variables, or an equivalent exact joint exposed-boundary relation. In this example the two inequalities suffice. The old polynomial poset certificate can verify singleton rows without constructing the exponentially large module/carrier.

## 8. Unsupported steps remain visible

SUPPORTED: exact priority constraint kernel; explicit two-sided Boolean-module realization; correctly oriented mono-left/epi-right comparison; normalized grouping/substitution coherence; physical exactness for the declared full-record fixture; one-sided physical safety elsewhere.

NOT ESTABLISHED: identifying K_P with a general full-record cylinder; a map of decorated middles from support inclusion; Isbell adequate-span pseudofunctoriality in this image doctrine; new observational powers; probability/causal feedback semantics; small canonical carrier or polynomial-time construction of all middles; preservation under arbitrary new contexts or changes of scheduler; general equipment/representability/CULF completion.

The exact missing action for broader physical contexts is: supply and verify a factorization of their full retained-evidence relation into primitive joint kernels on declared shared variables, then prove the resulting witness projection equals (not merely contains) the physical context-response relation. Without that evidence, the present K_P remains a sound abstraction and cannot support an honest same-cylinder comparison to the richer physical cylinder.

### Experimental-test boundary

The construction proves a cylinder of evidence-relative **response semantics**: y is the physical required-command/role-load predicate supplied by the mission bridge. If the intended phenomenological doctrine admits only experimentally executable, publicly observable tests, these y-predicates are not automatically admitted. One must either explicitly allow semantic response predicates as the test doctrine, or supply and authorize an experimental implementation of them and prove its compatibility with the existing observation/cost restrictions. Anonymous timing plus the algebra does not provide such an implementation. For the ORIGINAL tight-budget protocol, this is the exact remaining bridge obligation, not a completed experimental-test reconstruction. Section 12 separately discharges it for an explicitly budget-enlarged admitted protocol; it does not retroactively change the old tests.


## 9. Actual observation versus assurance: the explicit forgetful wiring

Here is the final separation of the two doctrines, superseding any reading of “physical profile” above as an experimentally observable y-test. The actual observation outcome in the fixed fixture is b together with its fixed productive timing record. Let the latent physical role response be y under the supplied bridge. The derived evidence-relative assurance relation is

  K_E ⊆ B×Y.

No sensor for y is supplied. The actual observation support is

  O_E(b) = OR_y K_E(b,y).

More generally retain the entire actual observation transcript o in place of b; reducing o to b is justified here only by the fixed-timing fixture and retained E. Conditioning on additional observed information must occur before the reduction.

Use the joint outcome interface B×Y and the Boolean relation

  F((b,y),b') = [b=b'].

This is projection, represented as an actual forgetting/deletion kernel. Its physical interpretation merely discards the latent response annotation; it does not read that annotation. Writing the assurance preparation kernel as A_E:{p0}→B×Y, its serial composite is

  F A_E:{p0}→B,       (F A_E)(p0,b)=O_E(b).

Thus the **actual observation cylinder** has preparation p0, tests b (actual observed-record occurrence predicates), and entries O_E(b). Its honest carrier and canonical middle are constructed by the same old serial decorated-realization formula, now with the y-port forgotten. The assurance cylinder retains y only as trusted physical interpretation. No equivalence of these two cylinders or middle objects is claimed.

In the Boolean module doctrine, F induces the join-preserving direct-image map

  F_!:2^(B×Y)→2^B,       S↦{b:exists y,(b,y)∈S}.

Restricting to the canonical image generated by the assurance preparation gives a surjective map M_assurance→M_observation. For a nonempty singleton preparation profile, both modules have exactly two elements (bottom and their respective nonempty support row), so this underlying map happens to be an abstract module isomorphism. This DOES NOT make their decorated cylinders equivalent: one has response tests (b,y), the other only observation tests b, and the displayed transformed-test law is a join over y. The complicated support information resides in the labelled test legs, not in the two-element abstract carrier. Their description can be large; no compactness inference follows. The eight/six counts in §10 concern the differently indexed conditional-section cylinders ONLY. It preserves the preparation and precisely the PULLED-BACK observation tests: evaluation at b after projection is OR_y evaluation at (b,y). It does not preserve each individual response test (b,y). This is the exact comparison direction and its test translation. It is an ordinary module map between DIFFERENT labelled cylinders with the declared observation-test transformation, not a same-cylinder realization map preserving all response tests.

### Why the observation cylinder cannot supply safety by itself

Let B contain b*=0011 and Y contain 00 and 11. The relations K^+(b*)={11} and K^-(b*)={00} have the same observed projection {b*} but require different commands. Both are physically possible fixed-priority equal-Q realizations with the same productive raw timing/word: use priority (0,1,2,3) for 11 and (0,2,1,3) for 00, roles A,B,A,B. This comparison uses local-only retained evidence (or any evidence admitting both priorities), NOT the fixed acquired comparison 1<2, which excludes the latter priority. Thus it neither changes the four-job positive record silently nor invents a physically impossible world. Projection cannot distinguish these two possible interpretations of the same production observation.

The existing positive and marginal-relaxed four-job relations likewise project to all B while differing in response fibers, but the relaxed relation need not be the exact same-evidence physical class. The two single-priority worlds above establish the physical observation-indistinguishability claim independently.

### Policy correctness has universal, not existential, variance

For an admitted observed word b, a proposed command delta(b) is justified precisely when

  K_E(b) != empty and K_E(b) ⊆ {delta(b)}.

For a partial policy with completion domain D⊆B, require this at every admitted b∈D; nonempty fibers outside D represent refusal/missed completion, not successful safety. Full useful completion requires D cover the allowed observation support and satisfy the physical timing/resource guards. The relation itself supplies no execution-time guarantee.

A nonempty sound outer relation K_P(b)⊇K_E(b) implies that a command uniformly correct on K_P(b) is correct on K_E(b). More generally, fix a common domain D⊆projection_B(K_E), and let Safe_D(K) be the policies correct on every fiber at b∈D. Then all actual fibers in D are nonempty, and

  K_E⊆K_P  implies  Safe_D(K_P)⊆Safe_D(K_E).

This reversed inclusion is the assurance comparison that the operational certificate needs. It is not obtained by interpreting the Boolean existential coefficient K_P(b,delta(b))=1 as success: that coefficient only says some compatible assignment permits the command. Universal exclusion of every other y is necessary. The already proved poset criterion exactly decides singleton fibers of K_P and therefore computes this universal policy condition without constructing the whole carrier. For arbitrary retained evidence it is sufficient, not necessarily complete; for the exact fixture it is complete for this fixed response task.

## 10. Explicit four-job conditional-middle comparison

For the conditional-section presentation (not the singleton physical-preparation presentation), write u={00}, v={11}, O={01,10}, and E=u∪v. Across all sixteen words, the exact kernel's rows are u, v, O, E. The v rows occur at 0011 and 1100; zero/four-one words give u; odd words give O; other weight-two words give E. The marginal-relaxed kernel has the same rows except that v is replaced by E.

Therefore the exact Boolean-module middle M_A is the eight unions of the three disjoint atoms u,v,O. The relaxed middle M_B is

  {empty, u, E, O, u∪O, E∪O},

with six elements. There IS a preparation-compatible join map f:M_A→M_B given by

  f(u)=u,  f(v)=E,  f(O)=O,

extended by joins. It takes each exact row at b to the relaxed row at that SAME b. It is surjective and satisfies S⊆f(S), so its response evaluation is order-lax. It does not preserve tests: evaluating 00 at v gives 0, while evaluating 00 at f(v)=E gives 1.

There is no reverse preparation-compatible function M_B→M_A: the same relaxed row E occurs both where the exact row is v and where it is E, forcing two different images. Conversely, the set inclusion M_B⊂M_A is join-preserving and response-test-preserving, but is not preparation-compatible at the v words. These are the precise available directions; the generic no-map-in-either-direction example from the old bridge is not falsely imported here. No map in either direction preserves BOTH all preparation labels and all response tests, because the scalar kernels differ.

## 11. Completion statement and retained boundary

The bridge now closes the following scoped loop:

1. Actual shared-priority semantics and sound acquisition give a common latent assignment and K_E⊆K_P; the fixed fixture gives equality.
2. Primitive finite joint rank/comparison/selector/XOR constraints derive K_P by same-witness gluing.
3. Existing Boolean-module two-sided realization machinery supplies explicit carriers, canonical comparisons, and coherent normalized wiring for that assurance relation.
4. The declared projection forgets latent y, yielding the actual raw-observation cylinder and its precise direct-image comparison.
5. Universal singleton-fiber certification, not existential realization, transports a policy from the sound outer relation to actual physical correctness, subject to the old full operational cost/physical premises.

This is an actual instantiation plus an explicit observation-to-assurance boundary, not a new generic quotient theorem or generic equipment completion. The loss of y under observation is exhibited, rather than patched by assuming new tests. Nothing here recovers latent response interpretation from raw phenomenology alone: the intrinsic/FIFO/arbitration/persistence/role bridge remains independent supplied or acquired operational structure. Full experimental reconstruction under arbitrary context changes, implementation of arbitrary y-tests beyond the expressly budgeted §12 enrichment, arbitrary stochastic/causal-feedback doctrine, adequate Isbell span action, and whole-contract representability/CULF obligations remain outside the proved scope. No additional diagnostic protocol is silently authorized by the assurance result; §12 separately specifies and budgets an optional diagnostic context that realizes the tests.

## 12. Costed observable-test realization by a DIFFERENT admitted protocol

The preceding distinction is not a claim that y-response predicates can never become observable. The existing acquisition theorem supplies a concrete context enlargement; the following is its explicit test-realization law, not a new learning theorem.

### Protocol, physical assumptions, and budget

Fix the exact §6 fixture: productive P_i demand Q, diagnostic D_i demand 2Q, J=0, persistent priority, safe drained probes, and fresh independent fair uncontrollable payloads. Let E be the OLD retained record, giving precisely the priority constraints P as before. Supply a new commissioning interval with independently fixed budget; do not redefine the original mission deadline after seeing diagnostic outcomes.

The enlarged protocol p_plus performs, from a justified empty/drained start, one already admitted D_i/P_j pair diagnostic for every unordered module pair (fixed orientation per pair). Each probe is drained before the next. The old theorem §8 shows that first arrival Q versus 2Q decodes that pair's priority comparison, and all pair comparisons determine the actual strict permutation pi. The protocol then admits a FRESH required productive all-ready batch at the independently fixed grid-aligned time T0 and observes it through its complete closed horizon. No diagnostic payload substitutes for a productive payload.

Use the existing fully charged §8 ledger with m=binomial(n,2):

  S_init=R ceil(C_init/R),
  S_pair=R ceil((D_P+D_D+rho_probe+C_probe)/R),
  S_compile=R ceil(C_compile/R),
  A_plus=S_init+m S_pair+S_compile.

Here R=nQ is the existing fixture's grid, caps D_P≥Q,D_D≥2Q are supplied before observations, and C_compile includes consistency/permutation recovery and preparation of the batch/decoder. Require T0≥A_plus (plus any not-sunk local acquisition, separately charged by the old theorem). Reserve all m slots regardless of outcomes; endpoint ordering/guards, physical tails, retention, finite arithmetic, storage and energy remain those of the old theorem. Charge another 2m probe invocations plus the fresh n productive invocations. Require the new mission envelope T0+nQ+gamma, where gamma includes the actual decoding/role-XOR/output/tail implementation costs. This need not fit the OLD tight mission opportunity; no same-budget transfer is asserted. If available time or capability does not cover this protocol, this context is simply not admitted physically.

All-pairs acquisition is used for a transparent fixed schedule; substituting the already proved bounded sorting acquisition is permitted only with its own charged worst-case schedule. This enrichment neither discovers the supplied work-invariance/arbitration assumptions nor changes their status.

### Executable observation and exact support law

Let z=(d,b) denote the enlarged protocol's actual public record, where d includes the full new diagnostic timing/bit record, and b is the productive rank word (with its fixed productive timing). The deterministic, finite, charged decoder pi_hat(d) reconstructs the unique priority. Define

  eta(z)=(b, V(pi_hat(d),b)).

This computes y from actual newly acquired priority information and actual observed bits; it does not query an unprovided role sensor. For EVERY legal run satisfying the acquisition and rank assumptions,

  pi_hat(d)=pi_actual,       eta(z)=(b,y_actual).

Hence response predicates (b0,y0) are genuinely executable tests of the enlarged observed record: accept iff eta(z)=(b0,y0). For arbitrary payload laws this gives pointwise correctness on the enlarged runs, but does not by itself reflect every support possibility of the old experiment.

For the fresh independent fair-bit exact fixture, however, let Obs_plus(E) be the support of all enlarged observed records consistent with OLD E; the new diagnostic record d is allowed to vary and is NOT fixed as additional conditioning evidence. Then

  eta[Obs_plus(E)] = K_E = K_P.                       (E+)

Proof of inclusion: old E forces actual pi∈LE(P); the decoder is correct and the productive bridge gives V(pi,b). Proof of reverse inclusion: given any pi∈LE(P) and word b, §6 provides a world reproducing old E. The added safe diagnostics preserve that same priority/work law and always complete inside the fixed reservation. Choose any allowed diagnostic payload outcomes; each finite such word has positive probability. Fresh productive bits realizing b also have positive probability and are independent of that finite diagnostic history. All Q/2Q timings are then forced by pi, and eta of the resulting observed record is the required (b,V(pi,b)). Thus every element of K_E is hit. END.

The support reflection is an existential statement over the entire NEW diagnostic record d. After conditioning on a particular observed d, the priority class shrinks, and one must not continue claiming the old unrefined K_P is the exact enlarged-record fiber. The equality also relies on freshness/full support and noninvasive persistent dynamics; arbitrary payload correlations or probe-sensitive regimes do not inherit it.

### Two-sided comparison with actually executable tests

Let W=Obs_plus(E). The enlarged actual-observation kernel is L_plus:{p_plus}→W with full support on its legal records. Let T_eta:W→B×Y be the graph of eta. The old decorated serial-composition construction yields

  T_eta L_plus = A_E,

where A_E(p0,(b,y))=[(b,y)∈K_E], after the explicitly declared singleton preparation reindexing p_plus↦p0 and under (E+). Preparation labels here refer to DIFFERENT physical protocols; the equation identifies their selected output-support semantics, not their execution traces, times, observations or costs.

At module level the direct image eta_!:2^W→2^(B×Y) sends the enlarged support preparation to K_E. Pulling a response test (b,y) back along eta gives the executable predicate [eta(z)=(b,y)]. The resulting map of generating/separating decorated realizations preserves preparation under that named reindexing and preserves precisely these translated tests. The canonical image CFS comparison is therefore an honest comparison for this costed observational test realization. The old raw test b is recovered by projection_B eta; discarding diagnostic information returns the old productive bit-word support, not an inverse test translation.

This closes the licensed-test bridge in the stated enlarged context without masquerading latent y as an original sensor. It is an actual operational context with a proved decoding/test map, paid by the existing acquisition ledger. It is not an isomorphism of the old and new protocols or a guarantee that the original tight-budget mission admits the enriched context.

The enrichment is a licensed operation on protocols, not a deterministic map from an old raw record to a new diagnostic record. The map eta runs only AFTER the additional experiment exists. Its fresh productive invocation/event IDs are distinct from those of any old run, and productive times are relative to the new T0. Equality (E+) is equality of selected outcome SUPPORTS across these protocols, not equality of events or coupled per-run payloads. Test translation is contravariant (t↦t∘eta), while preparation-support transport is covariant (direct image along eta).
