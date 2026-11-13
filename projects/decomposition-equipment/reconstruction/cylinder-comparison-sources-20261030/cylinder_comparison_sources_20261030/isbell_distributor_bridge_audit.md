# Audit: Isbell fixed points versus actual distributor cuts

**Outcome:** the two requested papers do not close the horizontal-wiring bridge. Their functoriality concerns morphisms **between contexts/distributors**, with distributors as objects. It must not be read as preservation of their ordinary horizontal composition. This is a precise scope limitation, not a claim that a suitably decorated reconstruction can never compose.

## Primary theorem and variance checks

Write c_phi = phi^down phi_up and M(phi)=Fix(c_phi).

**Shen–Zhang (2013).** Definition 2.12 specifies an infomorphism (F,G):phi→psi by F:A→A', G:B'→B and phi(a,Gb')=psi(Fa,b'). Proposition 4.5 supplies F_! c_phi ≤ c_psi F_!. The functor immediately after Corollary 4.7 is M:Q-Info→Q-CCat_skel, covariant: its left-adjoint map is c_psi F_!:M(phi)→M(psi). Theorem 4.16 characterizes M(phi) by sup-/inf-dense boundary maps F:A→X, G:B→X with phi(a,b)=X(Fa,Gb). These are not a horizontal-composition theorem. [Primary §2, §4](https://arxiv.org/html/1307.5625).

**Shen–Tao–Zhang (2015).** Sections 2.2–2.3 define Chu connections (zeta,eta):phi→psi by phi ↙ zeta = eta ↘ psi, where zeta:A⇝A', eta:B⇝B'. Proposition 3.3.1 gives the full quantaloid homomorphism

    M:ChuCon(Q-Dist)^op → Q-CCat,
    M(zeta,eta)(mu') = c_phi(mu' ∘ zeta): M(psi)→M(phi).

Lemma 3.3.2 is zeta* c_psi ≤ c_phi zeta*, with zeta*(mu')=mu'∘zeta. Theorem 3.3.3 is a retract statement; Theorem 3.3.5 gives B(Q-Dist)^op ≃ Q-CCat. The quotient identifies connections having the same back diagonal. Its nucleus is on ChuCon(Q-Dist), not on horizontal distributor composition. Bonds b:phi→psi have underlying type A'⇝B; their composition is b'•b=(psi↙b)↘b', not ordinary distributor composition. [Primary §§2.2–2.3, 3.2–3.3](https://math.mickeylili.com/files/preprints/Chu_connections_and_back_diagonals_between_Q-distributors.pdf).

Here f↙u denotes right extension and v↘g right lifting. Infomorphism covariance and Chu-connection contravariance are compatible: the passage from infomorphisms to connections reverses direction.

## Type-level reason this is not the desired cut theorem

The actual cut has input phi:A⇝B and psi:B⇝C and output psi∘phi:A⇝C. In ChuCon(Q-Dist), phi and psi are objects, not composable arrows. A connection between them would additionally require zeta:A⇝B and eta:B⇝C satisfying a residual equality; horizontal composability imposes no such equality. The quoted equivalence consequently supplies no operation M(psi) ⋆_B M(phi), no comparison with M(psi∘phi), and no proof that such a comparison is invertible. Bond composition does not fix this typing mismatch: its intermediate object is an entire context, not merely the shared wire B.

“Completion” must therefore be specified. The back-diagonal quotient completion and the fixed-point completion are genuine constructions, but neither cited functoriality theorem asserts that closing local reconstructions commutes with existential wire gluing.

## Independent Boolean check: identical extent nuclei, different cut nuclei

Work in 2-Dist on discrete sets, i.e. relations. For R⊂A×B use

    R_up(U)={b : ∀a∈U, aRb},
    R_down(V)={a : ∀b∈V, aRb},
    c_R(U)=R_down(R_up(U)).

Let A={a}, B={0,1}, C={c}; let R_i={(a,i)} and S={(0,c)}. Direct calculation gives:

| Relation | Closed extents / fixed points |
|---|---|
| R_0 | ∅, {a} |
| R_1 | ∅, {a} |
| S | {0}, {0,1} |
| S∘R_0={(a,c)} | {a} |
| S∘R_1=∅ | ∅, {a} |

Indeed c_R0=c_R1=id on P(A), while the two composite nuclei differ. Thus no rule depending only on these local extent nuclei (or only their abstract fixed-point lattices) can recover the fixed-point lattice of every actual horizontal composite, even with boundary sets fixed. The one- versus two-element outputs are not isomorphic.

**Important qualification:** the decorated two-sided reconstructions are not identical. Their labelled intent/boundary maps distinguish 0 from 1. This example does not refute composition retaining those maps or full incidence. In particular, if preparation/test legs are already part of the user’s given realization, retaining them is part of that construction, not an optional extra assumption or a modification of its goal. It refutes silently forgetting that data and invoking fixed-point functoriality afterward. Nor does it refute unspecified lax comparisons, for which a target operation and compatibility conditions would first be needed.

## Exact surviving construction with retained boundary incidence

For any finite Boolean relation R, define its concept-lattice boundary maps

    alpha_R(a)=c_R({a}),    beta_R(b)={a : aRb}.

The latter is closed. Since beta_R(b) is closed,

    alpha_R(a) ⊆ beta_R(b)  iff  aRb.

Consequently the fully labelled local reconstructions compute the actual composite without an externally supplied global table:

    (S∘R)(a,c)
      iff ∃b∈B [alpha_R(a)⊆beta_R(b)
                 and alpha_S(b)⊆beta_S(c)].

This is an elementary derivation from the retained primitive incidence. One can then apply the Isbell closure to this computed relation. It is exact, but is “reconstruct incidence, glue, then close,” not a proved smaller intrinsic composition of bare nuclei. It retains the shared label b and hence the witness-alignment information isolated in joint_comparison_bridge.md. For multiport nodes, the input must remain their actual joint relation, not independent marginals.

## Consequence for the current CFS goal

No finalized proof needs revision. The existing common-refinement/mixed-corner comparisons remain valid in their stated doctrines. The missing general bridge remains a construction linking actual wiring to sufficiently decorated reconstructed objects, with a proved comparison law. The inspected papers provide vertical comparison machinery and dense boundary representations, not that horizontal law. These enriched fixed-point categories are also not identified here with Garner's free Isbell/CFS construction. No theorem transporting this Boolean computation to arbitrary CFS, physical realization, or feedback is claimed.
