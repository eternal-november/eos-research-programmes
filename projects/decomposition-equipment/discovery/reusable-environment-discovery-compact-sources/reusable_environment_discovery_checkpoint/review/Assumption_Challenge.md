# Independent assumption challenge

Review history, 29 October 2026. The early sections record initial feasibility concerns raised before the main proof was written; they are not the final review status. The frozen-proof and final-report signoffs at the end supersede the provisional checkpoint language. This review does not assess novelty. No author files were changed.

## Executive conclusion

A substantive local discovery theorem is feasible **inside an explicitly restricted predictive class**. The current integer additive-response route has a valid mechanism for learning unknown scopes, then residual source blocks, without recovering a hidden global state. The important distinction is that the finite-memory/sparse-additive/fresh-innovation assumptions are premises, not discoveries certified against arbitrary environments by the same low-order tests.

The strongest promising ingredients are:

1. Union-scope conditional tests give a concrete witness-complete local search under a bounded true scope premise.
2. An integer response gap can turn approximate mean tests into exact response recovery, up to one fixed translation per output.
3. Irreducible **subset** tests recover unknown independent innovation blocks without the false assumption that every block has connected pairwise dependencies.
4. Stable observer quotienting and a single positive shared response witness are necessary for recursion and crossing reuse. Separate fitted laws, copied seeds, or one-step row equivalence do not suffice.

The theorem must not advertise unrestricted discovery of physical components, certification of the premises, arbitrary off-policy prediction from passive logs, or behavior-level completeness of a pinned source encoding.

## A. Local tests need a structural class, not only a memory ceiling

Let X_1,...,X_m be independent fair action bits. World 0 outputs Y=X_1 XOR ... XOR X_m; world 1 outputs its complement. Both worlds are memoryless. Every proper marginal of the (m+1)-bit vector (X,Y) is identical in both worlds, while the complete laws have TV distance one. Under the unseen action X=0, their outputs disagree surely.

Thus bounded observable memory alone cannot promote narrower local-cylinder agreement to a reusable full joint or feedback guarantee. A parent-width premise or a proved residual witness-completeness condition is indispensable. The premise itself cannot be validated by those same narrow tests against arbitrary higher-order alternatives.

### A positive local lemma

Suppose P(Y|X=x)=p(Y|x_T), where the unknown true scope T has at most d coordinates. For a candidate U of size at most d, compare its conditional law to the conditional law given U union V for every V of size at most d. If

    max_(V,u,v) TV(P(Y|U=u,V=v), P(Y|U=u)) <= r,

then taking V=T proves pointwise prediction error at most r on every covered union context. No faithfulness assumption is needed for approximate predictive discovery. If every estimated conditional row is within TV eta of its truth, accepting empirical discrepancy at most 2 eta yields a learned candidate conditional row within 3 eta of the true pointwise kernel; the true scope passes.

This is a concrete local search, not generic whole-program enumeration. It is, however, conditional on the stated class and coverage. It does not establish the class premise from unrestricted data.

## B. Integer additive-response recovery

For Y_i=f_i(X)+E_i with integer-valued f_i, true scope T_i of size at most w, and E independent of all pre-step X, let mu_i=E E_i. The conditional mean on U union T_i is f_i(x)+mu_i. Suppose all empirical conditional means have uniform absolute error at most e, and U passes every augmentation test at empirical threshold 2e. Then

    |f_i(x)+mu_i - E[Y_i|X_U=x_U]| <= 4e.

Two covered full contexts with the same U therefore have f_i values differing by at most 8e. If e<1/8, integrality makes them equal. U is exactly sufficient inside the covered domain. Rounding differences between estimated U-conditional means recovers f_i(u)-f_i(u_0), since their error is at most 2e<1/2.

Checks required in the main statement:

- X is entirely pre-innovation. Conditioning on a current other output generally destroys innovation independence.
- Innovations have a known boundedness or tail contract adequate for the mean concentration theorem; existence of a finite mean alone gives no advertised finite-sample rate.
- The translation uses one fixed reference value u_0 per output, not a separately selected baseline per history or policy.
- The same response map and innovation law are reused across times. Pooling unmodeled time variation can cancel response effects.
- Discovery and held-out residual estimation are split or use a simultaneous argument. Conditioning on successful training does not make reused residual samples independently distributed for free.
- Discreteness is a substantive separation assumption. Arbitrary real-valued responses do not admit this exact-recovery conclusion at a fixed nonzero radius.

## C. Independent innovation groups without pair faithfulness

Assume the joint innovation law factors across its finest mutually independent partition, every block of which has cardinality at most q. Examine each S of size at most q. Call S irreducible if P_S fails to factor across every nontrivial bipartition of S.

No irreducible S crosses true blocks: intersecting S with any one of the blocks gives an independent split. Every non-singleton true finest block B is itself irreducible, since any factorization of P_B would refine the partition. Therefore the connected components of the hypergraph of irreducible subsets are exactly the true finest blocks. Retain isolated vertices as singleton blocks.

For a split S=A disjoint-union B, let d_A=TV(P_S,P_A tensor P_B). If the three marginal estimates each have TV error at most eta, then

    |dhat_A-d_A| <= 3 eta,

using TV(product(P_A,P_B),product(Q_A,Q_B)) <= TV(P_A,Q_A)+TV(P_B,Q_B). Include a subset as an edge only if **all** empirical split distances exceed 3 eta. This produces no false cross-block edges. Recovery of every true block is guaranteed if its minimum split distance is strictly greater than 6 eta. Without this margin the conservative answer can be an unresolved or over-refined partition; a claimed independent factorization of the over-refinement is NOT justified merely because no dependence edge was detected.

The number of split checks is sum_(s=2)^q binom(m,s)(2^(s-1)-1). For an r-symbol residual alphabet, estimating an s-variable marginal has r^s outcomes. A union-bound TV estimate uses a logarithmic term of order r^q + q log m + log(1/delta), not merely log m. Estimation still has exponential dependence on q and the source alphabet.

Pairwise dependence is insufficient. The full-support law P(e)=2^-3[1+theta*(-1)^(e_1+e_2+e_3)], 0<theta<1, has every pair independent, but the three-variable block is irreducible and each split has TV dependence theta/2.

## D. Coverage is joint, controller-relative, and costly

The effective minimum logging probability must cover complete U union T cylinders (up to 2w ports, including their entire retained suffixes), not individual coordinates or parent scopes separately. Fair binary coordinates have excellent individual coverage while a specified k-coordinate cell has probability 2^-k. Distinguishing a change confined to probability-rho contexts needs on the order of 1/rho episodes even before estimating its magnitude.

Independent endpoint samples from separate episodes are a safe concentration contract. Multiple overlapping time windows within one trajectory are not independent samples; any effective sample size claim must prove a mixing or martingale bound. If using all time points, simultaneous per-time bounds or explicitly stationary pooled-law assumptions are necessary.

Local coverage can replace exponential global importance-weight coverage only because the structural predictive premise transfers the local conditional mechanism. This is not a model-free off-policy theorem.

A set of covered episode-start controllers does not automatically cover switching between them. At horizon two, the environments Y_2=0 and Y_2=1[A_0 differs from A_1] agree under both constant-action controllers and every exogenous episode-start mixture of them, but disagree surely under actions (0,1).

### Closed domain obligations

Declare the global admissible suffix domain D, the controller action domain, and the initial suffix contract. Show both the true process and the emitted predictor remain in D, or totalize their exits with an explicitly charged error symbol. True-law zero probability alone does not define a predictor's continuation.

If the learned innovation distribution is an empirical distribution on **exact recovered residuals**, its support is a subset of the true translated support; genuine closure under the true support then implies predictor closure. But checking closure only under observed innovations does not validate closure under unseen true innovations.

Projected local suffix languages can lose global feasibility information. Any quotient using a partial local shift automaton must preserve legal-domain distinctions or use an explicit totalization; silently dropping undefined transitions can yield an apparently smaller but non-executable observer.

## E. Recursive memory and local executability

For the order-two deterministic process X_(t+1)=X_(t-1), suffixes 00 and 01 have the same next-output law. After that common output 0, they become 00 and 10, whose next-output laws differ. Equality of immediate response rows is not a recursively stable state equivalence.

Use stable right-congruence/partition refinement: equal response labels and equal successor classes for every permitted action/readout symbol. A Moore quotient is minimal only relative to its declared deterministic transducer and input language, not among arbitrary stochastic implementations or all physical decompositions.

A mathematically sufficient summary is not automatically locally executable. A processor with only port A cannot update the current parity of ports A and B without receiving B or an equivalent permitted message. Charge read access, initialization, warmup, local memory, the clock, messages, and source distribution.

Sequential factorization P(Y)=product_j P(Y_j|Y_<j) must not be called parallel local generation unless the prescribed same-tick generation phases and messages are actually available. Additive pre-step local responses avoid this particular issue, but source delivery within an innovation block remains a physical interface cost.

## F. Global worlds and common positive witnesses

An episode-level hidden fair bit Z with Y_1=Y_2=Z is not equivalent to redrawing a fair bit every step: the latter has probability one half of disagreement, the former zero. Preserve persistent world parameters or retain sufficient observable memory; do not independently refit uncertainty rows or resample persistent sources.

A successful reusable certificate has one executable implementation before quantifying over compatible worlds/controllers. The weaker statement 'each world admits some implementation' need not supply one common predictor.

For crossing views, preserve shared source identities, memory identities, and update maps. Independent copies of the same marginal source generally destroy the joint law. Positive realizability of separate cuts is not positive realizability of their common refinement at a fixed source budget (the prior one-hot example remains a regression test).

## G. Source encoding is not behavior

The root checker tests F_1(a,e)=e and F_2(a,e')=e' XOR a with fair seeds. These are the same output kernel for every action. No single action-independent coupling lambda(e,e') makes their outputs equal for both actions. Yet the allowed local recoding e'=e XOR a repairs this immediately.

Consequently a fixed-witness common-coupling feasibility theorem is only complete within its declared source-response encoding universe. It must not be sold as completeness for all behavior-compatible implementations. If local action-aware recodings are allowed, include them in the response universe and charge their input access. If not, state the restriction.

The same checker separately verifies the genuine local positive-source obstruction for the PR relation x XOR y=a*b with local responses x=f(a), y=g(b): no deterministic response atom satisfies all four contexts, hence no positive shared mixture does. One bit of communication repairs it. These are distinct obstruction types: a poor pinned encoding versus a real restriction of the permitted information protocol. No novelty is claimed for the Bell-locality calculation.

## Frozen-proof audit checklist

- Exact structural premises, target domain, and startup law are stated before the theorem.
- Union-scope proof uses the unknown true scope as an augmentation, without assuming it is already supplied.
- Mean concentration includes all tests and all adaptively selected candidates through one simultaneous event.
- Exact response recovery, fixed residual translations, held-out source estimation, and the probability-budget sum are separately proved.
- Missing detected dependence is not treated as established independence without the class/margin completeness event.
- Runtime outputs are generated by one positive normalized joint program, not incompatible marginal kernels.
- Local observer updates and crossing source/state transports commute on a proved closed domain.
- Feedback guarantee follows by a sequential coupling/telescoping argument with initialization and per-step group errors charged.
- Complexity states dependence on w, L, q, alphabets, minimum cylinder mass, output range, and partition gaps.
- Any compatibility/minimality/completeness claim is relative to the declared implementation universe; no universal endpoint lifting is inferred.

## Checkpoint audit of posted proofs and implementation

Read `theory/Discovery_and_Reuse.md`, Sections 1–5 as posted around 17:50 UTC. The actual partial-coverage proof uses e<1/12, rather than the simpler full-support e<1/8 argument above. Its derivation is sound: passing U implies its empirical mean differs from the true context mean by at most 3e, and subtracting the common reference produces at most 6e error before rounding. Counts on U are at least the corresponding union counts, so no unestimated base row is used in a tested union row. The simultaneous event also licenses the data-selected reference. Fresh Stage-II filtering by pre-output contexts retains iid residual innovations on the Stage-I success event.

Two corrections were sent to the author: the quotient checks its totalized learned table rather than empirically testing every continuation; and the runtime coverage gate needs a separately charged raw-suffix monitor, or the quotient must preserve its gate predicates. Minimized response states need not retain enough information to evaluate coverage. The author is revising these points.

The author's margin-free crossing stability lemma is also correct. If P factors over tau and Q over pi, both with block size at most b, and every marginal of size at most b differs by at most d in TV, define R as the product of P marginals over the common intersection partition. Then

    TV(Q,R) <= |pi| d,
    TV(P,R) <= (|tau|+|tau meet pi|) d,
    TV(P,Q) <= 3 n d.

For the second inequality, marginalize Q to each B in tau, factor it over B intersect C for C in pi, and compare each intersection marginal to P. A single coherent feasible product law whose tested marginals lie within r of the empirical laws is therefore within 6nr of the true law on the radius-r event. This avoids a gap-based false independence claim, but searching coherent product laws is a nonconvex synthesis problem; independently choosing arbitrary marginal rows is not a replacement.

Read `theory/Witnessed_Feedback_Composition.md`. Its finite support/fixedpoint search is complete for the stated pinned witness universe, with no behavioral-completeness upgrade. A gluing paragraph initially needed an explicit restriction to fixed state/source maps: context-dependent recoders cannot be glued by choosing a separate coupling per input. The author reports that this restriction and its required matching initial/source pushforwards have now been added.

Read the runnable growing-environment experiment. The specialized held-out support certificate is valid inside its declared class: a nonzero multilinear polynomial of degree at most 5 is nonzero on at least 1/32 of uniform binary input vectors, and a nonzero integer response offset yields an invalid +/-1 residual with probability at least 1/2. The independent stride-5 validation windows start after a 4-row action-buffer gap, making them disjoint from training windows and each other. The implementation now uses a two-sided empirical-Bernstein log(4*cells/delta) allocation, and separate calibration halves for grouping and source-kernel estimation. The resulting source confidence remains conditional on the declared block-gap premise, the degree bound, fresh temporal innovations, and symmetric binary coordinate noise. Its histories are action-only; it is not a demonstration of arbitrary readout-dependent memory discovery.

The example author reports adding an explicit minimum block split-gap premise of .18 (true hardest synthetic split .185), executable learned-memory feedback checks, response-based quotient distinguishability witnesses, and labels limiting truncation rejection to the actual truncated candidates. These reported amendments must be verified against the completed rerun before treating them as passed.

### Exact regression artifacts

- `tests/check_assumption_boundaries.py`: PASS. Exact rational checks cover a five-parent parity counterexample with all proper marginals identical and full TV one; a full-support pairwise-invisible triple; recovery of an independent triple/pair partition through irreducible hyperedges; failure of immediate-row memory merging; uncovered controller switching; persistent versus fresh noise; and integer-offset support separation.
- `tests/check_source_encoding.py`: independently read and run, PASS. Distinguishes fixed encoding incompatibility from a genuinely unavailable local positive response implementation.

The numerical confidence constant was also checked against the primary paper: [Maurer and Pontil, *Empirical Bernstein Bounds and Sample Variance Penalization*, Theorem 4](https://www.cs.mcgill.ca/~colt2009/papers/012.pdf). Its one-sided formula uses log(2/delta). Applying it to both a Bernoulli indicator and its complement, then union-bounding over all chosen cells on independent calibration data, gives log(4*cells/delta). The implemented sample variance q(1-q)N/(N-1) matches the theorem's variance definition. The subsequent KL bound uses KL(P||Q) <= sum (p-q)^2/q for q>0; unseen empirical cells correctly give an infinite bound.

Independently read and reran the two later root/bridge checkers:

- `tests/check_crossing_product_stability.py`: PASS, 300 exact rational crossing-product cases and an out-of-class parity control.
- `tests/check_witnessed_feedback.py`: PASS, positive triangle infeasibility/repair, support fixedpoint and recoding feedback checks, persistent-source distinction, and 5,804 ordered-partition pairs for the stated inversion criterion.

One further margin-free synthesis obligation was sent to the main author: an alternative feasible product law can assign innovation values outside the true support. Its generated outputs may therefore leave the declared readout/domain alphabet even before the next gate. Use an explicit common extended alphabet and escape totalization (or a specified failure projection); unlike the exact true-block empirical support argument, automatic support inclusion is unavailable. Arbitrary real synthesis weights also need a numerical/sampling precision contract if advertised as physically executable rather than ideal probabilistic programs.

## Audit of the conditional-product extension (Sections 8–15)

The newly added non-additive extension is mathematically sound in the audited formulation. Its structural premise is a conditional product over unknown output blocks of size at most b, with each block depending on at most w input ports of a known finite observable suffix. A marginal on at most b outputs therefore depends on at most bw input ports. Testing an arbitrary selected candidate marginal against every augmentation of at most bw ports includes the unknown true marginal scope; width 2bw input cylinders suffice. This is the decisive witness-completeness argument.

The actual partition/scopes appear as options in the empirical local catalogue. Each tested true-block row has error at most eta, at most b blocks contribute to a tested marginal, and the empirical conditional test contributes another eta. Therefore the actual-block candidate passes at t=(b+1)eta. For any passing candidate, choosing the true marginal scope gives marginal error at most t+eta, and the crossing-product lemma yields full one-step TV at most min(1,3n(t+eta)). The common confidence event covers all data-selected candidates without a separate model-count penalty.

The finite exact-cover/constraint encoding does not enumerate arbitrary bounded programs or the whole environmental state. Its width-based cost is conditional: the selection constraint graph may be dense even for small b,w. The statistical/local table cost includes all output sets of size b and input scopes of width 2bw; the smaller block/scope catalogue count alone is not the full data-processing cost.

The stopped feedback proof and the sharper unstopped price H*epsilon+beta_Q are correct. Couple until a covered-output mismatch or a common gate failure. A first common gate failure before mismatch is a subset of the model's gate-failure event, so a second exit-probability term is unnecessary. Initialization is a shared observed suffix; an arbitrary startup law is not learned for free.

The exact-grid subcase is also valid as stated: coordinate errors are bounded by TV, the true block rows round exactly when eta<1/(2D), all b-output marginals have denominator dividing D^b, and distinct such marginal laws are at least D^-b apart in TV. The stricter 2eta<D^-b condition forces exact equality on covered rows. The approximate non-grid theorem need not yield useful exact memory compression: stable refinement minimizes the learned table, which can have distinct empirical rows throughout.

The direct coherent response-table LP is preferable to pinned source names. Its finite-context deterministic-table argument is exact for a common implementation with unrestricted finite shared randomness and the declared views. It does not infer a common implementation from separate matching chart laws. The two PR charts are a genuine counterexample under their different local read permissions. Per-block source synthesis is exact within that implementation language; it is not automatically globally optimal over all cross-block source-budget schemes.

One domain wording request remains tracked with the author: an evidence count gate alone may admit globally infeasible or off-contract contexts. The pointwise structural promise must cover every context to which the theorem applies, or the gate must additionally enforce the declared continuation domain. All predictor exits must be totalized. The coupled stopped proof only needs the pointwise bound on the coupled admitted histories, but the stated universal context claim should not silently exceed that domain.

## Improved numerical source-law certificate

Independently checked the primary result [Agrawal, *Finite-Sample Concentration of the Multinomial in Relative Entropy*, Theorem I.3](https://arxiv.org/pdf/1904.02291). For N samples and k outcomes, the empirical-to-true KL divergence has MGF at most (1-t/N)^(-(k-1)), for 0<=t<N. True independent innovation blocks make their fresh calibration histogram arrays independent, so the exponents sum to D=sum_B(k_B-1). This application is conditional on correct response and partition selection from earlier independent data; the final calibration half is not reused to select those objects.

The resulting centered MGF is bounded by D*t^2/[2(1-t)] after scaling by N. Hence the probability that N*sum_B KL(emp_B||true_B) exceeds D+sqrt(2D*l)+l is at most exp(-l). Taking l=6 and x=D+ceil(sqrt(12D))+6 gives a rational integer threshold. The implementation verifies a finite positive Taylor lower sum for exp(6)>400, certifying failure below 1/400. The same source event implies KL(Q_feedback||P_feedback)<=H*x/N for every feedback controller, and Pinsker gives TV<=sqrt(H*x/(2N)). This direction avoids the empirical-zero-cell infinity of the earlier reverse-KL estimate.

The updated implementation's integer square-root rounding to denominator 10^6 is outward. Its H=10 bounds are .041890, .055929, .073859, and .099591 for n=12,24,48,96. Per-case failure is at most 13/2000+n/2^64 using the conservative support-validation bound; a simultaneous claim across all four experiments must union-bound their failures. The earlier Bernstein confidence is marked an alternative comparison, not intersected or minimized without paying another failure budget.

## Frozen main-proof signoff

Audited frozen `theory/Discovery_and_Reuse.md` SHA256:

    6c5a77af7069936d2c9a653bb34858ef18bd636d1692fe258ed55e3fb29773dc

No remaining mathematical correctness blocker was found in this version, relative to its explicit structural, coverage, sampling, and implementation premises. This is an independent proof review, not a formal verification, novelty approval, or certification that a real environment meets the premises.

The tracked domain issue is resolved in Section 8: the main promise covers all syntactically admissible contexts; narrower domains require membership gating or separately guaranteed/charged exit. Gate costs are separated from predictive-state minimization. Section 9 now gives a simultaneous local-memory synthesis extension: normalized mesh approximations of state-response rows preserve the original recursive observer and incur block TV at most k^b/D. The existence proof t=eta+b*k^b/D is valid without a physical probability-grid premise. Its cost comparison is explicitly to the constructed finite-precision witness, not to an arbitrary exact-real representation. Restricted-source completeness is conditional on preserving a permitted positive witness; independent row rounding is not assumed to preserve locality.

Section 13 explicitly restricts its exactness claim to the independent selected-block-source implementation language, and distinguishes unrestricted finite deterministic-table mixtures from fixed source cardinality with private coins. Section 16 states sampling/finite-precision costs and allows the reverse empirical-to-true KL direction used by the final experiment.

Independently read and ran `tests/check_conditional_catalogue.py`: PASS. The exact population-table fixture is nonadditive and action-dependent. It checks all 112 block/scope candidates, with precisely one accepting exact controlled joint law, and rejects a model that matches all individual readout kernels but loses the joint dependence. This is regression coverage of the catalogue/augmentation mechanism, not a finite-data or arbitrary-size proof.

Independently reran the final example verification: all six `test_discovery.py` tests passed; `check_saved_artifacts.py` reconstructed certificates, empirical sources, and quotient tables for all four n=12,24,48,96 saved runs and executed their local observers under feedback. The checker did not call the data generator or the simulator-truth audit. The source code SHA256 at this verification was:

    5e555e76c6f67c930dd7a6799bd5ba4af7d17f8d8baaf2bb91ad3b6427138501

The final TXT report was reviewed for its strongest claims. It correctly distinguishes the generic conditional-product theorem, the specialized action-only polynomial experiment, per-run versus all-run confidence, exact implementation from physical entropy, and operational versus original ordered C5 refinement. A correction was requested and incorporated for the general witness search: the greatest-invariant shortcut is complete only for fixed source projections or fixed encoder input domains; reachable-only encoder-law constraints require retained-state enumeration as well.

The additional `examples/check_exact_source_sampler.py` was independently read and executed for every frozen candidate: PASS. Each block histogram denominator is 131072=2^17, so a 17-bit uniform index plus cumulative integer intervals samples its saved law exactly. Different independent blocks consume disjoint fresh bit segments; the two crossing ownership implementations receive projections of the same chosen group event. The checker verifies integer interval preimage sizes, all saved dyadic probabilities, bounded bit usage, and owner-local compressed execution against the raw-history reference under four feedback controllers. Totals are 85, 153, 306, and 612 ideal fair bits per global tick. NumPy supplies only reproducible test bits; a physical independent-fair-bit source remains the explicit runtime contract.

Final report signoff: `Reusable environment discovery results.txt`, SHA256
`49590fc620038a030e967532284f266de2e2109143d03de3717c95d211d91732`, was checked against the frozen proof, saved numerical results, and implemented runtime permissions. No remaining delivery-blocking correctness or coherence issue was found. The abstract correctly conditions its all-event, ten-step bound on the stated class, and the body distinguishes the generic theorem from the narrower broadcast-permitted input-memory experiment. This approval does not certify novelty or a real environment's satisfaction of the premises.

Final editorial amendment: the report was subsequently line-wrapped and its already stated polynomial bound was made explicit as degree at most five. The final report SHA256 is `3ccfd61f2c067f9230fb08eda5297e9ad7943b5d406f45d1b321610b77571db9`. This source-aligned editorial clarification changes no theorem, numeric result, or approval condition; the final report signoff applies to this version. The earlier report hash is retained above as review history.
