# Independent audit: controlled two-layer training responses

Date: 2026-11-05. Status: algebraically verified, with an exact independent test script. This is not an originality certification.

## Precise setting

Real factors A in R^(m×r), B in R^(r×n), with m,n≥1 and arbitrary finite hidden width r. The represented output is the entire matrix F=AB. Each training step minimizes L_Y(A,B)=1/2 ||AB−Y||_F² by simultaneous Euclidean GD with the same known fixed real stepsize η≠0 in both layers. Targets can change between steps. The full matrix output is observed before training and after each step. States being compared can have different widths.

Write E=F−Y, P=AAᵀ, Q=BᵀB and

    C = [A; Bᵀ], H=CCᵀ=[[P,F],[Fᵀ,Q]],
    J=diag(I_m,−I_n), S_E=[[0,E],[Eᵀ,0]].

Every PSD H of this block size has a factor realization; its minimum realizing width is rank H. Fixed width r imposes rank H≤r. A feasible shifted state requires the full block matrix H+cJ to be PSD; separate positivity of its diagonal blocks is not sufficient.

## Exact closed equations

Simultaneous factor steps are A⁺=A−ηEBᵀ and B⁺=B−ηAᵀE. Consequently

    F⁺ = F−η(PE+EQ)+η²EFᵀE,
    P⁺ = P−η(EFᵀ+FEᵀ)+η²EQEᵀ,
    Q⁺ = Q−η(EᵀF+FᵀE)+η²EᵀPE.

Equivalently, C⁺=(I−ηS_E)C and H⁺=(I−ηS_E)H(I−ηS_E).

For continuous factor gradient flow,

    dot F=−PE−EQ,
    dot P=−EFᵀ−FEᵀ,
    dot Q=−EᵀF−FᵀE,
    dot H=−S_EH−HS_E.

These equations are direct algebra, independent of balancedness, full rank, width, or loss convergence.

## One-step and continuous equivalence

Suppose the initial F matrices agree. Equality of first-step outputs for every target is equivalent, because η≠0, to

    ΔP E + E ΔQ = 0 for every E in R^(m×n).

Testing E=e_i e_jᵀ shows first that every off-diagonal entry of ΔP and ΔQ vanishes, and then that ΔP_ii+ΔQ_jj=0 for every i,j. Hence

    ΔP=cI_m, ΔQ=−cI_n, or ΔH=cJ.

Conversely this condition cancels the first-step difference. The same derivative test is necessary for continuous all-target equivalence. It is sufficient for full continuous trajectories because S_EJ+JS_E=0 and the continuous closed equations are invariant under H↦H+cJ. Use common admissible target functions (for example, locally bounded piecewise-continuous functions) and standard ODE uniqueness on corresponding local existence intervals. A smooth shared feedback policy is also covered on intervals of unique solutions.

Thus continuous controlled output equivalence is exactly the feasible J-shift class. This is not hidden orthogonal gauge: nonzero shifts change H and can change its rank.

## Two-step classification for GD

Take two initially one-step-equivalent states with ΔH=cJ. After a first residual E their outputs still agree, and

    ΔP⁺ = c(I_m−η²EEᵀ),
    ΔQ⁺ = −c(I_n−η²EᵀE).

For any second residual Z their second output difference is therefore

    ΔF⁺⁺ = η³c(EEᵀZ−ZEᵀE).

If n≥2, choose E=e_1 e_1ᵀ and Z=e_1 e_2ᵀ, with the ambient rectangular sizes understood. Then EEᵀZ−ZEᵀE=Z≠0. If n=1 and m≥2, choose E=e_1 and Z=e_2; the expression is −Z≠0. Hence equality after every target pair forces c=0 whenever (m,n)≠(1,1).

Conversely equal H gives identical H updates and output histories for every target sequence. Therefore, for non-scalar input/output pairs, all of the following are equivalent:

1. Initial F and first two output responses agree under every target pair.
2. Initial H agrees, equivalently F,P,Q all agree.
3. Output histories agree under every finite or infinite target sequence whenever defined.

The statement is a bound on distinguishing-word depth, not a claim that a single run with two unknown target probes uniquely recovers all entries of H. Its premise quantifies over every target pair (or over a sufficient finite family of restarted experiments).

Adaptation is not necessary. If F₀ agrees, choose Y₀=F₀−E. Since F₁ then agrees, choose Y₁=F₁−Z; this is a common legitimate target pair. A feedback policy can implement the same experiment without knowing F₁ in advance.

## Scalar exception

For m=n=1 define f=F and s=P+Q. Every GD step closes as

    f⁺=(1+η²e²)f−ηes,
    s⁺=(1+η²e²)s−4ηef.

Therefore all GD histories depend only on (f,s). Equality of F and first-step responses already identifies exactly (f,s), not P and Q separately. The flow has the same observational quotient. Each feasible scalar response state satisfies s≥2|f| and has a width-one realization, apart from the all-zero state which admits width zero if allowed.

## Explicit 1×2 witness

State 1: A=[1], B=[0,0]. State 2: A=[0,0], B=I₂. Then F₀=0 and H₁−H₂=J. Use E=(1,0), Z=(0,1), which correspond to targets Y₀=(−1,0), Y₁=(−η,−1).

    Both F₁=(−η,0).
    State 1 F₂=(−η,−η).
    State 2 F₂=(−η,−η−η³).

Thus State 1 minus State 2 is η³(0,1), as claimed. No small-step assumption is used.

## A crucial counterexample to weaker target quantifiers

Take H₁=diag(I_m,0_n), H₂=diag(0_m,I_n), both with F₀=0. For every *fixed* target Y, held unchanged forever, these states have identical discrete output trajectories. To see this, use an SVD Y=U D Vᵀ and change input/output coordinates. Each paired singular direction is a scalar two-factor system initialized with the two factors swapped between states. Scalar output dynamics are invariant under that swap. Unpaired directions have zero target and never affect F.

Nevertheless switching targets distinguishes the same pair in two steps when m+n>2. Hence quantifying over every autonomous squared loss is strictly weaker than quantifying over target sequences. This audit does not establish any fixed-target identifiability theorem.

## Width and rank consequences

For nonscalar GD, the minimum hidden width among equivalent realizations is rank H, not rank F. The true raw hidden width cannot be identified because zero columns can be appended to C. Equal-H realizations differ only by hidden orthogonal transformations after zero-padding to a common width; this is the standard Gram-factor equivalence.

For flow, the minimum equivalent width is

    min {rank(H+cJ): H+cJ is PSD}.

The feasible c set is a nonempty compact interval (possibly a point), since positivity of principal blocks gives finite lower and upper bounds. The full PSD condition determines its actual endpoints. This formula need not equal rank H; the explicit 1×2 pair has widths one and two in one flow class.

At a common fixed hidden width r<max(m,n), a nonzero feasible shift between two admissible states is impossible: if c>0, the first state's P is positive definite and the second state's Q is positive definite, forcing r≥m and r≥n; c<0 is symmetric. Thus one-step response equality is already sufficient in that restricted-width class. At r≥max(m,n), the diagonal pair above is realizable and makes the two-step bound sharp. For arbitrary prescribed widths r₁,r₂, a nonzero shifted pair is possible exactly when (r₁≥m and r₂≥n) or (r₁≥n and r₂≥m).

## Boundaries of the result

- η=0 provides no training information beyond F₀. Unequal layer learning rates, alternating updates, momentum, weight decay and other optimizers require separate equations.
- Full-matrix target control and full-matrix observation matter. Restricted inputs, a single training sample, rank-deficient data, fixed targets or restricted residual subspaces can retain additional indistinguishability.
- No target boundedness, rank, balancedness or genericity restriction is needed for the discrete theorem. The separating E,Z can be scaled arbitrarily small; exact distinguishability then has correspondingly tiny signal.
- The difference is order η³, so exact identifiability says nothing by itself about robustness to measurement noise or finite precision.
- Arbitrarily large width does not create a larger closed state: H has dimension (m+n)(m+n+1)/2 regardless of r.
- No claim is made about practical learning benefit, optimization quality, statistical sample complexity, or scientific importance.

## Reproduction

Run `python verify.py` in this directory. The script verifies the concrete witness symbolically for arbitrary η, scalar closure symbolically, exact linear observation ranks for all m,n from 1 to 3, direct factor-vs-Gram updates numerically, J preservation under exponential flow, and the fixed-target counterexample for 120 steps in four rectangular/square dimensions. The proof above, rather than the finite tests, supplies the arbitrary-dimension statement.
