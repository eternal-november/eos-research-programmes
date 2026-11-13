# Two-sided linear evidence: complete mission-relative feedback criterion

Theorem and proof, 2026-10-30. This document establishes a complete criterion for the stated two-sided linear evidence class, including rank-one countermodels, an optional inverse-domain guard, and exact transport through known linear contexts. **No novelty or priority claim is made.** The result is a concrete static experimental interpretation theorem, not a complete multi-box/coupled-network acquisition theorem.

## 1. Evidence and mission, without model-product replacement

Finite-dimensional real spaces: input V=A⊕U, output Y⊕U. Let p:V→A and t:V→U be projections. The unknown box F:V→Y⊕U has evidence

    F|S = prescribed column/subspace data,
    HF = prescribed row data,

where S≤V and H:Y⊕U→E are known. Assume consistency, checked by solving the finite linear equations. Choose ANY completion F0. Put K=ker H with inclusion i_K, and q:V→V/S. Every and only evidence-consistent completion has unique form

    F_Z = F0 + i_K Z q,    Z:V/S→K arbitrary.

This follows because the difference vanishes on S and takes values in ker H. The SAME Z controls internal and observed output uncertainty. It is not replaced by independent BZ_1q and CZ_2q.

Fix mission readout h_m:Y⊕U→O and target J:A→O, and define

    L0=pr_U F0−t,       B=pr_U i_K,
    O0=h_m F0,         C=h_m i_K,
    E0=O0−Jp,
    L_Z=L0+BZq,        E_Z=E0+CZq.

The protocol is one fixed feedback wiring. The mission says:

(i) every a∈A has a fixed point z∈ker L_Z with pz=a;
(ii) every fixed point satisfies h_mF_Z z=Jpz.

This is exactly mission-relative kernel-image existence plus unique observed value, including all hidden fixed points. It is NOT the stronger inverse-domain contract. Hidden fixed-point witnesses may depend on F; the policy does not.

Let V_vert=ker p, W=S∩V_vert, R0=L0(W), and T=L0^{-1}(im B).

## 2. Complete certificate

**Theorem.** Every evidence-consistent completion satisfies the mission iff both F and O below hold.

FEASIBILITY:

    (F1) p(ker(L0|S))=A,
          OR
    (F2) im B⊆R0 and p(ker L0)=A.

OUTPUT:

    if T⊆S:       E0|ker L0=0;                         (O1)
    if T⊄S:       ∃D:U→O: DL0=E0 and DB=C.            (O2)

All these are subspace containments, rank conditions, or linear equation solves computed from the two-sided sample data and one completion. They do not require global-model QE or assumed exact projections.

### Feasibility sufficiency and explicit witnesses

In F1, choose a linear section Kobs:A→S∩ker L0 of p. It is a fixed-point section for EVERY completion because qKobs=0.

In F2, choose K0:A→ker L0 with pK0=id, and R:im B→W with L0R=id_imB. Then

    K_Z = K0 − R B Z q K0

satisfies pK_Z=id and L_Z K_Z=0. Indeed pR=qR=0, L0K0=0, and L0RB=B; the two BZqK0 terms cancel. This section may vary with Z and is only a mathematical existence witness, not a hidden-world-dependent controller.

### Feasibility necessity

If im B⊆R0, universal feasibility implies nominal feasibility at Z=0, hence F2. It remains to prove that im B⊄R0 forces F1.

Let λ∈U* annihilate R0 but satisfy λB≠0. Such λ exists. Since λL0 vanishes on W, its restriction to S factors through p(S). Choose α∈A* extending the resulting functional on p(S). Then

    αp−λL0

vanishes on S and so equals rq for some r∈(V/S)*. Choose kλ∈K with λBkλ=1, and set Z=kλ r. It follows that

    λL_Z=αp.

If α≠0, some mission input a has αa≠0, and no z over a can satisfy L_Zz=0. Thus robust feasibility forces α=0 for EVERY such choice.

First, p(S)=A: otherwise an extension α can be chosen nonzero on a complement of p(S). Second, λL0(S)=0 for every λ∈R0^⊥ with λB≠0. The set of these λ spans R0^⊥: fix μ∈R0^⊥ with μB≠0; any λ with λB=0 equals (λ+μ)−μ, a difference of two elements whose B-composites are nonzero. This works over any field. Therefore every λ∈R0^⊥ annihilates L0(S), giving L0(S)⊆R0. For each a choose s∈S over a, then w∈W with L0w=L0s. Now s−w∈S∩ker L0 projects to a. This is F1. END.

For A=0, F1 holds trivially, so no nonzero-α step is needed. For B=0, F2 reduces to nominal feasibility. Zero-dimensional spaces cause no exception.

### Output sufficiency

If T⊆S and L_Zz=0, then L0z=−BZqz∈im B, so z∈T⊆S. Thus qz=0, L0z=0, and E_Zz=E0z=0 by O1.

If O2 holds, then E_Z=D(L0+BZq)=DL_Z, so E_Z vanishes on ker L_Z.

### Output necessity

If T⊆S, then ker L0⊆T⊆S, so every z∈ker L0 is a fixed point in every completion. Its output forces E0z=0.

Suppose T⊄S. For any z∈T\S, choose k∈K with Bk=−L0z. Since qz≠0, there is a Z with Zqz=k. Then z is a fixed point, so universal mission output implies

    E0z+Ck=0                                             (*)

for EVERY k with that B-image. Vary k by ker B. We obtain C(ker B)=0, so C factors uniquely through B as Cbar:im B→O, Cbar(Bk)=Ck. Equation (*) becomes

    E0z=Cbar L0z  for z∈T\S.

Because T\S spans T whenever T⊄S, this equality holds on all T. In particular E0 kills ker L0. Thus D0:L0(V)→O, D0(L0z)=E0z, is well-defined. On L0(V)∩im B it agrees with Cbar, since such z lie in T. Define D on L0(V)+im B by gluing D0 and Cbar, then extend linearly to U. It obeys DL0=E0 and DB=C. END.

## 3. Rank-one adversaries suffice

**Corollary.** If the universal mission fails, some counterexample completion has Z of rank ≤1. Hence checking all rank-one perturbations (including zero) is semantically equivalent to checking all perturbations for this particular robust KI mission.

Feasibility: if F2's nominal condition fails, Z=0 witnesses failure. Otherwise the necessity proof produces Z=kλ r of rank ≤1 whenever F1/F2 both fail.

Output: if O1 fails, Z=0 suffices. If T⊄S and O2 fails, the necessity argument contrapositively yields z∈T\S and k with Bk=−L0z but E0z+Ck≠0. Choose ℓ∈(V/S)* with ℓ(qz)=1 and Z=kℓ. This rank-one completion makes z a bad fixed point. To make the contrapositive constructive: either C fails to kill ker B, in which case adjust k along ker B at any untested z∈T, or C factors and E0−Cbar L0 fails to vanish on T, in which case choose an untested z where it is nonzero (T\S spans T).

This corollary gives explicit, independently evaluable failure witnesses and not merely a proof-search rejection. A failure means incompatibility relative to the DECLARED exact two-sided completion class; it does not mean impossibility under additional true but unrecorded physical constraints.

## 4. Independence of F0 and refinement

Although the formulas use a chosen F0, their truth is independent of that choice because the theorem equates them to the same completion-family property. More concretely, replacing F0 by F0+i_K Z0q translates the free variable Z↦Z−Z0. Thus the represented completion set and universal mission do not change.

Evidence refinement that preserves the same spaces, wiring, readout and mission replaces the completion family by a nonempty subset. Universal success therefore survives. The old certificate can be checked against the old evidence constraints and retained alongside the refinement, or the new finite rank tests can be recomputed. Do NOT claim that the identical branch/multiplier D survives every change of evidence presentation. For example the new nominal representative, S, K, and quotient coordinates may differ. Semantically the comparison family restricts; syntactic witness transport needs the indicated embedding/coordinate maps.

Nonemptiness is essential: incompatible evidence is rejected as inconsistent, never certified by vacuity. Changing feedback doctrine, guards, port types, or mission readout is NOT mere evidence refinement.

## 5. Canonical section-change shear

For a fixed successful F let X_F=ker L_F and p_F=p|X_F. A fixed-point section K:A→X_F yields an honest factorization of the mission map:

    A --K--> X_F --h_m F|X_F--> O,
    (h_m F|X_F)K=J.

For any two sections K,K', define

    s_{K,K'}=id_X+(K'−K)p_F.

Then p_F(K'−K)=0; consequently s is invertible with inverse id_X−(K'−K)p_F. It fixes p_F and therefore the mission output Jp_F, and sK=K'. Moreover

    s_{K',K''} s_{K,K'} = s_{K,K''},
    s_{K,K}=id.

So arbitrary section choices are related by specified leg-compatible isomorphisms with exact cocycle coherence. After embedding into the declared free envelope, v2 supplies the actual M-left/E-right comparison spans and their unique compositors. This avoids forcing raw carriers to be identical across F.

**Typing/scope caveat:** this shear family is NOT by itself proof that a separately chosen section at every context is strictly natural over Prep×Test^op. For a supplied preparation restriction g:A'→A, use the induced section Kg into the pulled-back fixed-point carrier; readout restrictions compose the output leg. Independent section choices are then related by the above coherent shears. A full v2 context-family construction must state these actual context maps/pullbacks and include exactly the admission rectangles already verified. No additional physical feedback schedule receives admission from the shear or from a formal compact trace.

## 6. What is and is not now established

Established: an exact finite certificate derived from TWO-SIDED evidence, preserving the shared uncertainty in internal and observed rows; explicit positive witnesses; rank-one negative witnesses; coherent change of fixed-point realization; evidence-restriction semantics. Unlike the whole-column-only lemma, row information can make the mission true without full identification.

Scope beyond this two-sided theorem: sound-and-complete decomposition of arbitrary coupled multi-box experiments into this two-sided form; acquisition safety; preservation of this evidence class by network composition; separate state-safety guards. Optional original inverse-domain admission is established in Sections 8–9. Generic feedback composition usually maps affine matrix uncertainty to rational/nonlinear correlations, so class closure cannot be assumed. A hierarchy may retain joint parameter sharing rather than independently applying this rule at nodes. Any separate network construction requires its own structural hypotheses, proof, and prior-art assessment.

Closest verified source remains van Waarde et al., *Data informativity: a new perspective on data-driven analysis and control*, https://arxiv.org/html/1908.00468 . Its Theorems 16–17 already derive complete common-stabilizer certificates from samples without identifying the plant. This note is specifically an algebraic KI fixed-point mission criterion with two-sided evidence; no claim that this specialization or its rank-one witness property is unpublished.

## 7. Minimal correlated, non-identifying experimental example

Take A=U=Y=R, mission readout y and J=id. Observe the whole-column experiment F(1,1)=(1,1), so S=span{(1,1)}. Also measure the row H(y,v)=y−v on an input basis, obtaining

    HF(a,u)=a−u.

By linearity this row identity holds on V. These are finite experiments, not an assumed global mission verdict. The full evidence-consistent family is exactly

    F_z(a,u)=(a,u)+z(a−u)(1,1),   z∈R.

Choose F0=id. Then L0=0, E0=0, B=C=id under the natural coordinates, T=V, and the two certificates are F1 (observed diagonal fixed-point section a↦(a,a)) and O2 (D=id).

Every F_z has a fixed point u=a and every fixed point has y=a. At z=0 every u is a fixed point; at nonzero z the fixed point is unique. Original KI admission holds throughout; original inverse admission fails at z=0 and is not claimed. The unknown box is not identified.

This is a sampled conservation law: y−v=a−u plus the actual closure v=u forces y=a, while the diagonal sample independently supplies existence. If one replaces the common perturbation z by independent output/internal perturbations, the claim becomes false: internal perturbation zero and output perturbation one gives arbitrary hidden fixed points with y=2a−u. This explicitly tests the importance of preserving uncertainty correlations.

Across worlds, X_F=ker L_F changes dimension (two at z=0, one otherwise), so section-change shears cannot identify all raw carriers. They compare choices within one world; v2 yields a FAMILY of comparisons to the same mission-cylinder middle. Any claim of cross-world raw-carrier isomorphism would be false even in this example.

## 8. OPTIONAL stricter ORIGINAL inverse-domain admission

Use this section ONLY when the declared operational API or mission explicitly requires inverse-domain feedback. It is not added to the KI contract proved above.

Let i_U:U→V be the vertical inclusion, Q=q i_U, and

    D0=L0 i_U:U→U.

(The name D0 here denotes the residual internal block, not pr_U F0 i_U; their difference is the identity.) The residual block in completion Z is

    D_Z=D0+B Z Q.

**Inverse-guard theorem.** Every D_Z is invertible iff

    D0 is invertible,    Q D0^{-1} B=0.                 (I)

Equivalently, D0 is invertible and im B⊆L0(S∩ker p).

**Proof, necessity.** Z=0 forces D0 invertible. If T_inv=QD0^{-1}B is nonzero, choose k∈K with T_inv k≠0 and ℓ∈(V/S)* with ℓ(T_inv k)=1. Put Z=−kℓ, of rank one, and u=D0^{-1}Bk. This u is nonzero because Qu=T_inv k≠0. Then

    D_Zu=Bk+B Z T_inv k=Bk−Bk=0.

This is an explicit singular completion consistent with ALL two-sided evidence.

**Proof, sufficiency and inverse formula.** Under (I), N=D0^{-1}BZQ has N²=0. Thus

    D_Z^{-1}=D0^{-1}−D0^{-1}BZQD0^{-1}.

The subspace equivalence follows because QD0^{-1}B=0 says D0^{-1}(im B) lies in ker Q, which is precisely the vertical coordinate copy of S∩ker p. END.

This does not force full internal identification. For example D0=I_2, B:k→k e1 and Q:(u1,u2)→u2 give D_Z=I_2+z e1e2^T, invertible for every z despite an unidentified internal shear. In contrast, unrestricted im B=U forces Q=0 and hence the whole vertical input space to be sampled, recovering the earlier tomography boundary.

### Exact mission under the strict guard

Assume (I), and let K0:A→V be the unique nominal fixed-point section, pK0=id and L0K0=0. Define

    R=i_U D0^{-1}:U→V,
    K_Z=K0−RBZqK0.

Then pR=0, L0R=id, and qRB=0. Consequently K_Z is the unique fixed-point section for F_Z. Direct multiplication gives

    (O0+CZq)K_Z
      =O0K0+(C−O0RB)ZqK0.

The potentially quadratic term vanishes because qRB=0.

**Inverse-domain mission criterion.** Under (I), every completion has observed feedback value J iff

    O0K0=J,
    AND [ qK0=0  OR  C=O0RB ].                         (IM)

**Proof.** Z=0 gives the first equality. For the second, a bilinear family M Z N vanishes for every Z iff M=0 or N=0: if both are nonzero choose a with Na≠0, k with Mk≠0, and a rank-one Z mapping Na to k. Apply this to M=C−O0RB and N=qK0. Conversely either factor being zero makes the uncertain term vanish. END.

Thus failure of the optional strict guard or of its exact-output criterion again has a rank-at-most-one countermodel (nominal failure uses rank zero). All witnesses are for the same fixed feedback protocol; internal sections are proof witnesses, not distinct controllers.

## 9. The actual data-derived interface and comparison family

For either the KI criterion or the optional stricter criterion, the finite sample certificate constructs, for EVERY evidence-consistent F, the actual linear fixed-point space

    X_F=ker L_F,

with a section K_F:A→X_F and output leg o_F=h_mF|X_F satisfying

    p_F K_F=id,       o_F=Jp_F,       o_F K_F=J.

These equations, with the explicit observed/nominal-correction section formulas above, are the operational interpretation. No full F is identified, and no exact intermediate projection oracle is assumed. The family is described by the measured affine equations and the proved certificate; obtaining the unknown internal witness experimentally is a separate task.

Let I_J=im J in finite-dimensional vector spaces, with e_J:A→I_J and m_J:I_J→O. It is an honest, entirely data/mission-described realization of the same arrow J. There is a leg-compatible map f_F:X_F→I_J given by the corestriction of Jp_F, with f_F K_F=e_J and m_J f_F=o_F.

**Important CFS typing distinction.** I_J is the usual vector-space image middle. After embedding in the free Isbell envelope, it need NOT equal the envelope's canonical cylinder middle R_J. Apply v2 to the honest realization X_F and also to the honest realization I_J to obtain their M-left/E-right comparison spans to R_J. Do not silently assert that the embedding preserves the original image factorization, or that the comparison's target is literally the embedded I_J. If one explicitly works only with the original finite-arrow epi/mono factorization, I_J is its canonical middle; this is a different claim from a full free-envelope CFS statement.

Within a fixed F, the section-change shears in Section 5 are actual leg-compatible isomorphisms with strict cocycle coherence. Across F, retain the entire family; raw X_F can change dimension. Evidence refinement restricts that family. Context restrictions use the actual induced pullbacks/readout composites discussed in Section 5; v2 then supplies its comparison-family coherence on the verified mission rectangles. No cross-world raw-carrier isomorphism is needed.

Finally, the evidence class need NOT be closed under feedback to certify this ONE specified loop. Nonclosure limits recursively repeating the SAME extraction rule on arbitrary networks; it does not undermine the one-loop theorem. Complete correlation-preserving extraction across a network remains an additional theorem-level obligation, as do other operational schedules and safety guards. No novelty claim is made for the present algebraic criterion or its CFS interpretation.

## 10. Exact transport through KNOWN linear contexts

This section gives a genuine exact interface-transport law without claiming closure under two-unknown-box composition.

Let an evidence family of boxes F:V→Y be

    F=F0+i_K Z q_S,    Z:V/S→K arbitrary,

where i_K:K→Y is the inclusion. (Here Y denotes the complete output space, including internal outputs when applicable.) Let P:V'→V and G:Y→Y' be fixed KNOWN linear maps. Put

    S_ctx=P^{-1}(S)=ker(q_S P),
    K_ctx=G(K)≤Y',
    F_ctx,0=GF0P.

**Known-context transport theorem.** The image family is EXACTLY

    {GFP : F consistent with the original evidence}
      = F_ctx,0 + i_Kctx Hom(V'/S_ctx,K_ctx) q_Sctx.

This is equality of supported box families, not an overapproximation obtained by forgetting covariance.

**Proof and explicit lift.** There are canonical maps

    ebar:V'/S_ctx→V/S,      ebar q_Sctx=q_S P,
    gbar:K→K_ctx,           i_Kctx gbar=G i_K.

By construction ebar is injective and gbar is surjective. Every original parameter Z induces the transformed parameter

    Z_ctx=gbar Z ebar.

Conversely choose a linear retraction r:V/S→V'/S_ctx of ebar and a linear section s:K_ctx→K of gbar. For any proposed transformed parameter Z_ctx, set

    Z=s Z_ctx r.

Then gbar Z ebar=Z_ctx. Thus every transformed completion has an actual original completion, proving exactness. These are mathematical lifts of models, NOT hidden-world-dependent operational choices or controller policies. Finite-dimensional linear algebra supplies r and s, including the zero-dimensional cases. END.

The transformed data can be expressed again as two-sided evidence: specify the restriction to S_ctx from F_ctx,0 and take H_ctx:Y'→Y'/K_ctx to be the quotient, with known row H_ctx F_ctx,0. The resulting exact completion family is the displayed one.

For successive known contexts P1,G1 and P2,G2,

    P2^{-1}(P1^{-1}(S))=(P1P2)^{-1}(S),
    G2(G1(K))=(G2G1)(K),

and the baseline maps compose associatively. The parameter maps also compose: gbar_2(gbar_1 Z ebar_1)ebar_2=(gbar_2 gbar_1)Z(ebar_1 ebar_2), under the canonical quotient/image identifications. Lift choices r,s need not compose canonically; the exact image family and forward parameter map do. Do not confuse a chosen lift with canonical physical alignment.

### Mission consequence, with no new operational admission inferred

If Y' and V' have the required output/internal and external/internal decompositions, the COMPLETE KI criterion from Sections 1–2 can be applied to this transformed two-sided evidence. Because the image family is exact and every transformed member lifts, its success is equivalent to the fixed mission holding for GFP for every original F. The optional inverse-domain guard must still be checked when required. Arbitrary known P,G need not preserve a previously proved feedback guard or mission: they define a transformed protocol, whose actual guard/readout is checked anew.

This theorem covers known feedforward linear contexts with their declared types. It does not use formal cups/caps to admit additional operational feedback, and does not turn multiple unknown uses of F into independent parameters.

## 11. Exact evidence-refinement embedding and coherent witness restriction

Keep the same ports, feedback protocol, readout and target J. Let old evidence be (F0,S,K) and stronger consistent evidence be (F1,S1,K1), where

    S⊆S1,   K1⊆K,   F1 belongs to the old family.

These conditions ensure that the new completion family is a subset of the old one. Let κ:K1→K be inclusion and ρ:V/S→V/S1 the canonical quotient. The baseline difference has a unique parameter Z0 with

    F1=F0+i_K Z0 q_S.

Then the new parameter Z1 embeds in the old parameters by the affine formula

    j(Z1)=Z0+κ Z1 ρ.                                  (R)

Indeed q_S1=ρq_S and i_K1=i_Kκ, giving

    F1+i_K1 Z1 q_S1=F0+i_K j(Z1)q_S.

This embedding is injective because κ is injective and ρ surjective. It retains all shared output/internal covariance and does not replace the refined family by its marginals. For iterated refinements the affine offsets, inclusions and quotient maps compose exactly; expanding (R) gives the same represented F, and uniqueness of its old parameter identifies the composites.

If the old certificate succeeded, restrict its actual section family by j:

    K_old,j(Z1):A→X_F.

This is still an honest fixed-point section with output J in the refined world. A separately recomputed successful new certificate gives another section K_new,Z1 of the SAME p_F:X_F→A. They are related by the canonical shear

    id_XF+(K_new,Z1−K_old,j(Z1))p_F.

This shear preserves both labelled mission legs, carries the old preparation section to the new one, and obeys the exact cocycle law of Section 5. Thus successive evidence refinements and certificate rechoices give actual coherent realization comparisons, not merely implication between mission predicates. After the stated embedding, v2 supplies their M/E comparison-family compositors to R_J. Raw carriers are kept at their actual world and never identified across different F.

Inconsistent refinements are reported as inconsistent, not certified by empty-family truth. More general refinements may also be handled whenever an explicit exact parameter embedding is supplied, but the theorem here proves (R) for the stated two-sided evidence refinements rather than assuming it for arbitrary evidence languages.

## 12. Why this is NOT unknown-composition closure

Two exact counterexamples separate the proved transport from an unproved general network rule.

1. **Shared unknown scalar.** One unknown scalar a∈R used twice serially has composite a². The primitive/shared family is affine and its correlation is completely explicit, but its composite-value set is [0,∞), not an affine subspace or affine coset. Replacing the two uses by independent a,b changes the supported family and is invalid.

2. **Even independently unknown boxes.** Let v:R²→R be an arbitrary row and u:R→R² an arbitrary column, with their joint family explicitly declared to be the full product. Both primitive completion classes have S=0 and unrestricted K. The composite uv ranges exactly over 2×2 matrices of rank at most one. This set contains diag(1,0) and diag(0,1), but not their sum I_2, so it is not an affine subspace (it contains zero). Thus even genuine independence does not give closure of this evidence class under arbitrary unknown-box composition.

These failures do not diminish the one-loop certificate or exact known-context transport. They identify the next obligation: a richer correlation-preserving evidence/interface representation, with a proved complete extraction/transport rule for the chosen unknown network operations. No efficiency advantage or novelty claim follows from the present results.
