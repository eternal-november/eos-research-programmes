# Incomplete experiments and nonlinear mechanisms: a growing matrix-gauge stress family

## Plain-language abstract
Experiments can identify how each small subsystem behaves, and how each measured pair moves together, without determining how all the subsystems share a hidden influence. This example retains that ambiguity instead of supplying each subsystem with its own independent error bar. The possible mechanisms must use one shared matrix choice. Some individually acceptable choices cannot coexist. A new measurement of an unmeasured pair reduces the ambiguity, but does not automatically settle every remaining distinction.

This is an exact stress family, not a claim that arbitrary physical architecture can be recovered. The observation cover supplies candidate module patches; discovering an unknown partition of arbitrary sensors is NOT proved here. The family exercises shared-world compatibility after local mechanisms have been discovered from conditional readouts. Its mechanism is standard matrix factorization combined with positive stochastic realization, not a new matrix-completion theorem.

## 1. Family
Let G=(L⊔R,E) be any connected bipartite graph with N vertices, for example an even cycle C_(2m), m≥2. Each module has state x_i=(a_i,b_i)∈{0,1}² and a binary admitted input u_i. Write c_i=(a_i,b_i,u_i), with reference c0=(0,0,0).

At each step a SINGLE fresh shared source Z is drawn from {0,±e_1,…,±e_d}, independently of previous states, controls, and source draws. Regime e chooses
P_e(0)=1−τ_e, P_e(±e_k)=τ_e/(2d), 0<τ_e<1.
At least two distinct τ's are available. This probe matrix has rank2, whereas the source alphabet has size2d+1. It does not identify odd hidden response directions. The entire regime distribution is declared, not inferred or certified by randomization alone.

For d=2 use four output states and the full-column-rank zero-sum contrast matrix
U=((1,0),(-1,0),(0,1),(0,-1))^T.
The mechanism is
K_i(y|c,z)=B_i(y|c)+s_i(c)[U A_i z]_y,
where A_i is an unknown invertible2×2 matrix, s_i(c)>0 is unknown with s_i(c0)=1, and B_i is an unknown strictly positive stochastic row. Require every displayed K_i row strictly positive. Given Z, modules draw their next states independently.

A concrete nonlinear baseline uses positive unnormalized weights
w(c)=(2+a+2ab, 2+b+ua, 2+(a XOR b)+u, 2+2(b XOR u)+ab),
B(c)=w(c)/sum(w(c)), and s(c)=1+0.2a+0.15b+0.1uab.
There is internal state feedback, mixed old-bit interaction, and input interaction. The source creates genuine stochastic coupling between modules. There is NO direct causal state-feedback edge between different modules in this stress family; extending the all-history argument to that case would need another proof.

Small A_i guarantee positivity, uniformly over all contexts. For any N, λI with λ=0.025 and nearby invertible transformations give an open positive family. All global transitions are positive. Hence every fixed-input finite global chain has a unique stationary law, generally nonuniform.

## 2. What readouts discover
Assume transition readouts of each measured edge are available with enough support to identify every conditional pair row. Exact population tables are used here. If noisy three-view observations are used, a separate valid calibration/deconvolution theorem is needed; it is not proved by this construction.

The single-module conditional row is B_i, because E[Z]=0. The pair row on an observed edge is
J_ij^e(c_i,c_j)=B_i(c_i)⊗B_j(c_j)+(τ_e/d)s_i(c_i)s_j(c_j) U A_i A_j^T U^T.
Let U^+=(U^T U)^(-1)U^T. Projecting the centered pair row and multiplying by d/τ_e gives
D_ij(c_i,c_j)=s_i(c_i)s_j(c_j) C_ij, where C_ij=A_i A_j^T.

Because C_ij is invertible, context response factors are identified without knowing A: D_ij(c,c0)D_ij(c0,c0)^(-1)=s_i(c)I. Thus B_i, all s_i, and all measured edge matrices C_ij are recovered. These are learned nonlinear state-conditioned mechanisms, not supplied numerical response values. The imposed affine hidden-source vocabulary and candidate patch alphabets remain structural assumptions.

## 3. Exact shared-world fiber
Suppose one invertible factor solution A_i^0 exists. Every other solution to ALL observed edge equations has exactly the form
A_i=A_i^0 H for i∈L; A_j=A_j^0 H^(-T) for j∈R,
for ONE H∈GL(d), subject to the positivity inequalities from EVERY state/input/output/source row.

Proof. Choose a root in L and set H=(A_root^0)^(-1)A_root. An edge equation determines its neighbor uniquely as A_j^0 H^(-T). Propagating through a connected graph alternates these two forms. Every edge is between opposite sides, so both forms satisfy every edge equation. Conversely propagation covers all vertices. □

The admissible fiber is therefore not a Cartesian product of local uncertainty sets. It is one matrix gauge constrained by all local positivity conditions. One fixed H defines one mechanism for every context and every time, and one fresh Z is shared at each time. H is NOT redrawn at different contexts or rounds.

Existence and cycle obstruction can be checked constructively. Set a root factor to I, propagate A_j=C_ij^T A_i^(-T) on a spanning tree, and check every remaining edge equation. If any fails there is no invertible shared factorization. If all pass, solve the additional joint positivity constraints over H; satisfying cycle equations alone does not guarantee a positive stochastic realization.

On a four-cycle with scalar-multiple matrices, edge data C12=C23=C34=cI and C41=2cI cannot coexist, though every edge separately has invertible positive factors when c is small. Propagation forces C41=cI. This is an exact inconsistency of a shared source representation, not just disagreement between fitted marginals.

## 4. Positive assembly and temporal meaning
For each admissible H define the actual global transition by
P_H^e(x'|x,u)=sum_z π_e(z) product_i K_i^H(x_i'|c_i,z).
It is positive and normalized. Every observed edge has the recovered pair kernel. Any regrouping into larger components must retain the SAME Z and corresponding conditional kernels. Multiplying already-averaged module kernels instead would generally destroy edge correlations.

Each observed pair is itself a closed controlled Markov system: after summing all other output states, its next law depends only on its own old states and inputs. Consequently equal observed pair kernels imply equal complete pair-history distributions for equal pair initial laws, under any causal input policy based only on that pair's observed history and public regime sequence. Under fixed inputs and stationary initialization, the unique stationary pair law is determined by the pair kernel and hence also agrees for every H. This includes nonuniform stationary starts.

Do NOT extend this conclusion to controllers jointly observing several masks, or to a hidden global policy selecting pair inputs from unobserved states. Those are additional observation channels and can distinguish worlds.

## 5. Tests that reduce particular ambiguity
For a newly measured same-side pair i,k∈L,
C_ik=A_i^0 H H^T (A_k^0)^T.
Thus one full-rank same-side pair determines HH^T and reduces the remaining gauge to a right orthogonal factor. This does not always identify the whole world: the discrete source distribution is invariant only under signed coordinate permutations, not every orthogonal rotation.

For example take all A_i=λI in a base world and A_i=λQ in another, where Q is a45-degree rotation. Every pair covariance (even previously unmeasured ones) is equal, since QQ^T=I. Odd source moments vanish. But four distinct modules' selected centered output indicators have expectation proportional to E[Z_1^4]. In the base world this is τ/2; after the45-degree rotation it is τ/4. A four-module same-time record therefore distinguishes the worlds. This is an explicit positive higher-order obstruction invisible to ALL pair histories. Unlike an arbitrary triple-table fiber, its remaining parameters are shared mechanism matrices linked across all contexts by the local response geometry.

No finite test here certifies absence of arbitrary omitted physical effects. It resolves a named ambiguity inside the declared source/mechanism class.

## 6. Size and limitations
For d=2 every module has four states and eight state/input contexts. Every measured pair has64 context pairs and16 next-state outcomes. A cycle needs O(N) such tables while the global state space has4^N states. Exact table algebra is polynomial in N at fixed d, but statistical coverage and calibration costs are not established here. Positive-gauge feasibility need not be easy; this note supplies explicit positive witnesses, not a polynomial solver for arbitrary instances.

The growing family retains nonlinear internal feedback, unobserved shared influence, positive joint implementations, nonunique mechanism parameters, cycle incompatibilities, and higher-order observations that shrink genuine ambiguity. It DOES NOT establish unknown sensor partition discovery, arbitrary nonlinear hidden mechanisms, unknown source support/calibration, cross-module causal feedback under partial-history observation, finite-sample learning bounds, or controller/physical-hazard guarantees.

## 7. Statistical caution for the distinguishing test
The four-way centered-moment gap in the displayed λ=0.025 example is τλ^4/4≈7.32×10^−8 when τ=0.75. It is exact and nonzero, not automatically an economical experiment. For independent trials with bounded centered-product observations, a generic concentration estimate requires order gap^−2 (up to logarithms) samples; temporal data require their own dependence treatment. No practical sample advantage is claimed. Positivity witnesses may be chosen with larger amplitudes, but quantitative test cost must remain explicit.

## Verification status
The companion Python script checks positivity for every local context in three displayed gauge worlds; all64 pair context combinations under both regimes; context-gain recovery; a nonuniform stationary pair law; a fully assembled four-module row; the fourth-order distinguishing moment; an incompatible cycle; and nonzero nonlinear mixed state dependence. These are floating-point reproducible checks supporting the symbolic proofs above, not formal verification or a finite-sample theorem.

## 8. Discovery rather than supplied subsystem: an eight-state variant
The four-state matrix family above tests compatibility but does not guarantee a useful task quotient. The following variant adds genuine quotient discovery. Candidate observation patches are supplied, but their subsystem partitions are NOT.

Each patch is now x=(a,b,y)∈{0,1}³, with task signature a. Its baseline row is
B8(a',b',y'|a,b,y,u)=B4(a',b'|a,b,u) D(y'|a,b,y,u),
where B4 is the nonlinear baseline in section1, and D is Bernoulli with parameter0.25+0.1y+0.05a+0.03bu. Thus the nuisance y has internal memory and responds to the core, but does not drive the core.

Replace U by U8: for output(a',b',y'), set the row to (2y'−1)e_1 if a'=b', and (2y'−1)e_2 otherwise. Let s=1+0.2a+0.15b+0.1uab+0.05y. The hidden-source row remains B8+s U8 A_i Z. With A_i=0.005I and the displayed nearby gauge, all rows are positive. The same pair-response, matrix-gauge and positive-assembly proofs apply unchanged because U8 is zero-sum and full-column-rank.

**Discovered subsystem.** Among all partitions preserving task a, exactly one is both hidden-response cancelling and baseline lumpable: the four core blocks {(a,b,0),(a,b,1)}. In particular the task signature a alone is insufficient; data force the additional state b, while y can be removed.

Proof of cancellation constraint: within a fixed task-a fiber, only one core value(a,b) contributes to each U8 column. A block has zero summed U8 row iff it includes both y values or neither for each core. Thus every cancelling task partition groups whole core pairs. Baseline transition probabilities for a' differ between old b=0 and old b=1 at fixed a (already at u=0); hence those old core pairs cannot be merged. Conversely the four core blocks cancel U8, and their next probabilities are B4, independent of old y. This proves uniqueness. No hidden amplitude or shared gauge must be resolved first.

**Nontrivial rejection case.** Perturb B8 by0.005(2y−1)v, where v=(1,1,0,0,−1,−1,0,0) in lexicographic output order. This remains a positive stochastic baseline but lets old nuisance y affect the task's next state. Cancellation still requires keeping each old core pair together, whereas these two old y values now have different task transitions. No task-preserving cancelling/lumpable quotient exists. The correct outcome is a witnessed rejection, not a falsely isolated core.

The script check_discovered_core.py enumerates all225 task-preserving partitions: exactly one passes in the positive discovery case, and zero in the feedback counterexample. This is bounded exhaustive verification, not a proposed exhaustive algorithm for large hidden alphabets. A nonlinear local state quotient is discovered inside each supplied patch; discovery of the patch cover or an additional minimal incoming interface itself remains outside this example. The shared source couples the retained nuisance/remainder mechanisms, not the discovered core transitions. At fixed independent inputs the recovered cores decouple. Ordinary control inputs may connect them, but this note does not claim autonomous cross-core feedback discovery.

## 9. Stronger conditional discovery: the useful core itself retains shared uncertainty
Section8 deliberately discovers autonomous cores. The following fixture is more consequential for incomplete experiments: the discovered core is not autonomous, and its unresolved shared influence must remain in the assembled model.

Again use raw states(a,b,y), task signature a, and the four-state nonlinear macro baseline B4. Define the full raw mechanism
K(a',b',y'|a,b,y,u,z)
 = [B4(a',b'|a,b,u)+s(a,b,u)(U4 A z)_(a',b')]
   T(y'|a',b',a,b,y,u),
where U4 is the matrix in section1, s=1+0.2a+0.15b+0.1uab, and T is Bernoulli with parameter
0.2+0.1y+0.05a'+0.03b'+0.02a+0.02bu.
All displayed probabilities are strictly positive for the same λ=0.025 gauge examples. This is still affine in Z because the residual mechanism T does not depend on Z. Summing y' gives a macro transition independent of old y. The quotient S=(a,b) is therefore pointwise lumpable for every admitted hidden source value, but its transition depends on Z.

The learner is given arbitrary raw state labels, the task emission/signature, and observed conditional single and pair tables—not the(a,b,y) coordinates or quotient. Write the raw coefficient matrix at old context c as F_c, so K_c=B_c+F_c Z. Pair this patch with any fixed reference context whose coefficient matrix F_ref has full column rank. The centered observed pair table is
D_c=(τ/d)F_c F_ref^T.
For any target block Q, equality of the summed D_c rows between two old states is equivalent to equality of their summed F_c rows, because multiplication by F_ref^T is injective on row vectors. Consequently a candidate partition is pointwise conditionally lumpable iff its averaged B block rows and observed D block rows are constant on every old block. This criterion uses no unknown gauge values and no source-coordinate reconstruction. It certifies a conditional mechanism, not exterior independence.

**Result.** Searching task-preserving partitions of the randomly relabelled raw alphabet yields a unique coarsest four-state quotient; after search it is verified to equal(a,b). Task a alone is not lumpable, while refining all the way to eight states is unnecessary. The hidden response on the four-state core is nonzero, so the algorithm correctly labels it conditional rather than autonomous. No task-preserving autonomous quotient exists.

Proof of coarseness: the next-a probability under B4 distinguishes b=0 from b=1 at each fixed a, forcing every lumpable task partition to separate the two core values. Keeping both y values together for each core is valid by the displayed factorization, establishing the coarsest quotient. Any autonomous task partition would have to refine these core blocks. For each core, its U4 row is nonzero; splitting its y outputs cannot remove that nonzero response (T is positive), so no such partition cancels the source effect.

The matrix-gauge constraints from the other sections now act on the discovered useful core itself, not only on discarded nuisance. Whole-system positive assembly retains one shared source and one fixed admissible matrix gauge. One cannot choose a separate conditional core law for every module or every visit. This provides the contrast between a certified autonomous decomposition, a certified conditional decomposition, and incompatible choices within the remaining world family.

The script check_conditional_core.py uses random raw labels and searches all225 task-preserving partitions using only B and D. Exactly two partitions are conditionally valid: the four-state core and the eight-state identity; the four-state one is uniquely coarsest. No autonomous partition passes. The learner's result is checked against every source value afterward. Minimum raw probability is0.02586.

Calibration qualification: this executable starts with exact population conditional tables on an identified raw alphabet. Unknown noisy three-view sensor calibration and task-emission recovery require the main calibration theorem. They are not separately implemented or proved in this fixture. Candidate measurement patches and the low-dimensional shared affine source universe remain declared. Ordinary macro outputs can be wired into other modules' inputs to obtain a positive feedback realization, but the pair-history indistinguishability statement from section4 is not asserted under arbitrary such feedback.

### Order of discovery in the conditional fixture
There is no circular need to know the macro partition before obtaining the paired-response test. Use raw centered pair tables against a reference raw context first; their right factor is injective, so block-row equality finds the quotient without macro coordinates. Then sum raw outcomes over discovered blocks on both sides of each observed edge. This yields macro B and centered macro pair tables. Choose arbitrary local contrast bases on the discovered four-state alphabets and normalize context gains at a chosen reference. The matrix edge factors are then obtained in those local bases. Relabellings or basis changes modify the local matrices, not the existence of one shared gauge. The residual conditional law T is recovered, for the displayed family, by dividing the positive raw averaged row by its discovered macro row. The order is therefore raw conditional tables → discovered conditional quotient → learned macro response geometry → compatible shared-world fiber, rather than supplying the quotient to the discovery procedure.

## 10. Closing the noisy-readout pipeline: standalone numerical QA
`check_noisy_conditional_discovery.py` closes the calibration qualification for the specific conditional fixture numerically. It is standalone; its three-view spectral helper is copied and credited from the earlier hidden-patch discovery QA, not imported through an external workspace path.

**Oracle generation only:** construct two randomly relabelled eight-state modules at fixed input u=0, coupled through the same fresh five-valued source, and compute their actual positive64-state pair transition and nonuniform stationary distribution. Generate three independent unknown positive10×8 emission channels per module. Emit only (i) each module's current three-view observation tensor, (ii) a10⁴-entry tensor for one noisy sensor on each module at the current and next time, and (iii) each module's current sensor joint with a selected noisy taskbit. The taskbit has two unknown emission probabilities, not known latent state labels.

**Learner boundary:** infer rank8 and all three emission matrices from each current observation triple; use learned inverses to decode the temporal tensor into joint state moments; condition these statistical moments on old context; infer the averaged B rows and rank2 centered pair responses; recover the taskbit emission values and their level-set task partition from its observed joint table. Search task-preserving partitions using those learned B/D tables only. No true hidden coordinates, source response matrices, physical preparation of latent states, or repeated cloned trajectories are supplied to this stage.

**Outcome:** both modules give8→4 unique coarsest conditional quotients, with zero autonomous task quotients. The two noisy task-emission levels are recovered as0.15 and0.85. Three-view tensor reconstruction error is2.87×10⁻¹⁷; validation-only sensor column error4.40×10⁻¹⁵; validation-only full conditional pair-kernel error1.24×10⁻¹³. Minimum stationary old-context mass is0.003608; minimum pair-transition probability0.001124. True coordinates are consulted only after the learner finishes, to verify that its discovered quotient equals the intended core.

**Precise limit:** this demonstrates end-to-end recovery from exact stationary observation probabilities with unknown noisy sensor calibration, within the declared finite affine-source model; it is not a finite-sample stability theorem, a method for decoding individual noisy readings, or certification that an arbitrary physical environment satisfies the model class.
