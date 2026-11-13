# Frozen candidate: certifying a one-bit response factor from restricted contexts

Status: derived here for audit, no novelty claim. Fix m>=2, signs s in {−1,+1}^m, nonempty finite family H of nonempty coordinate subsets. Signs and H are fixed independently of certification observations; discovery/training cost is separate. S={s,−s}. A context query C chooses C in H and receives X_C from a fresh independent X~μ, where μ is one arbitrary unknown law on {−1,+1}^m. Choices may depend on earlier samples, but a trial is exactly one same-unit joint context sample; no further coordinates of that unit can be queried unless included in the chosen context.

For any root r, define R_r(x)= (x_r/s_r)s and q_r(μ)= (R_r)_#μ. This is the unique law supported on S with the same root marginal as μ. Exactly TV(μ,q_r(μ))=μ(S^c), independently of r. q_r need not equal q_r' as laws for a general μ, but both distances equal μ(S^c). For μ supported on S, q_r=μ.

For each nontrivial cut B⊂[m], C crosses B if C intersects both B and B^c. Cuts B and B^c are equivalent. Let

τ*=min Σ_C w_C subject to w_C>=0 and Σ_{C crosses B}w_C>=1 for every nontrivial B.

If infeasible, τ*=∞. If finite, τ*>=1. For optimal weights, choose contexts independently with p_C=w_C/τ* and reject if X_C is not in {s_C,−s_C}. For every μ with μ(S^c)>=ε, the rejection probability per trial is at least ε/τ*. Thus after

N = ceil[log(δ)/log(1−ε/τ*)]

trials, accepting iff no rejection has occurred has false-accept probability <=δ for every such μ, and accepts every μ supported on S with probability 1. Here 0<ε<1 and 0<δ<1/2. Define U_N=min{1,τ*(1−δ^(1/N))} if no rejection occurs and U_N=1 otherwise. The exact coverage claim is P_μ(μ(S^c)>U_N)<=δ for every μ; this is not a conditional probability claim given acceptance. This is a support-property tester and one-sided certificate, NOT a tolerant estimator; close alternatives need not be accepted. In particular N<=ceil[(τ*/ε)log(1/δ)]. The guarantee holds for both >ε and >=ε alternatives; at equality it is a size bound rather than a semantic assertion that accepting excludes equality.

Lower bound: consider ANY adaptive possibly sequential tester using the same raw context oracle. It stops almost surely, has finite expected query count under q0=Uniform(S), and has an acceptance event A such that P_q0(A)>=1−δ and P_μ(A)<=δ for every μ with μ(S^c)>=ε. (Completeness under this specified fair null alone suffices; completeness for all laws supported on S is stronger and is satisfied by the upper tester.) Then

E_q0[N]>= τ* kl(1−δ,δ)/[−log(1−ε)].

Proof: for each nontrivial B let x_B be s with the coordinates in B flipped, q_B=Uniform({x_B,−x_B}), and μ_B=(1−ε)q0+ε q_B. Its root marginal is fair for every r, so q_r(μ_B)=q0, and μ_B(S^c)=TV(μ_B,q0)=ε. If C does not cross B, q_B,C=q0,C exactly; if C crosses B, supports q_B,C and q0,C are disjoint, and KL(q0,C || μ_B,C)=−log(1−ε). The adaptive transcript KL identity and binary data processing give

Σ_{C crosses B} E_q0[N_C] [−log(1−ε)] >= kl(1−δ,δ).

Rescale counts into a feasible LP solution and sum. If signs are learned using extra data rather than supplied, this lower bound still applies to the certification subproblem with signs supplied, but does not by itself characterize full discovery complexity. The transcript KL argument requires only q0,C absolutely continuous with respect to μ_B,C, not reverse absolute continuity. It can be proved directly by likelihood ratios without importing a two-sided absolute-continuity assumption from a generic bandit lemma.

Therefore for 0<ε<=1/2 and 0<δ<=1/4, certification has Θ(τ*/ε log(1/δ)) query complexity in this exact interface, comparing a fixed-sample upper bound to a null-expected adaptive lower bound. No claim of matching exact constants for arbitrary ε,δ, tolerant estimation, or full joint density learning.

If τ*=∞, some cut is crossed by no context. q0 and q_B have exactly identical observable laws, although TV(q0,q_B)=1. No test can have δ<1/2 completeness/soundness for that alternative.

Examples: tree-edge contexts τ*=m−1 (each fundamental cut forces its edge weight>=1); all two-element contexts τ*=m/2; all k-element contexts τ*=m/k for 2<=k<=m; singleton-only contexts τ*=∞. For complete k-uniform H, summing singleton-cut inequalities gives k Σ_C w_C>=m. Uniform weights achieve the lower bound because the minimum number of k-subsets crossing a nontrivial cut occurs at a singleton cut.

Cost convention: N counts independent prepared units / context trials. A context of k protocols requires k individual response measurements. If those have equal physical cost and dominate reset/preparation, the m/k reduction in trials need not reduce total scalar observations. Exact same-unit joint access is essential; separately randomized interventions give only singleton marginals and make τ*=∞.

For a pure certificate whose asserted property is μ(S^c)<=ε and whose only required soundness is false certification when μ(S^c)>ε, run the lower-bound argument with alternatives μ_B,η at η>ε and let η decrease to ε. The same displayed lower bound follows by continuity, provided completeness at q0 is retained.
