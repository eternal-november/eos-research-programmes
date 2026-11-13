# Exact shared-frame gluing on an arbitrary observation graph

## Abstract

Pair experiments can reveal how two modules share a disturbance without revealing either module's individual response to that disturbance. The pair descriptions are not independent: following them around a cycle may lead to a contradiction. This theorem gives a constructive cycle test and describes every surviving common explanation. A new pair observation can remove a specific ambiguity, but even all pair observations can leave different higher-order joint behaviors.

The mathematical mechanism is standard matrix factorization/synchronization. Its role is an exact shared-world certificate inside the positive nonlinear mechanism family in `stress/Matrix_Gauge_Family.md`; it is not a general architecture-discovery theorem.

## 1. Data and goal

G=(V,E) is connected. Each undirected edge supplies an invertible real d×d matrix C_ij, with C_ji=C_ij^T. Seek invertible local frames A_i with
C_ij=A_i A_j^T.
These matrices are projected, centered conditional pair-response tables, not arbitrary graph adjacency entries. The source covariance has been normalized in the declared model family.

Choose a root r and spanning tree T. Color each vertex even/odd by its tree distance from r, and set L_r=I. Along a tree edge from known i to unknown j set
L_j=C_ij^T L_i^(-T).
Thus L_i L_j^T=C_ij on every tree edge.

## 2. Complete classification theorem

All common frame solutions, if any, have the form
A_i=L_i H for even i,
A_i=L_i H^(-T) for odd i,
where H is one invertible matrix shared by ALL vertices.

Every non-tree edge imposes one of the following conditions:

1. Opposite parity: C_ij=L_i L_j^T. This condition is independent of H.
2. Both even: D_ij:=L_i^(-1) C_ij L_j^(-T)=S.
3. Both odd: D_ij:=L_i^(-1) C_ij L_j^(-T)=S^(-1).

Here S=HH^T must be symmetric positive definite (SPD).

Consequently:
- If every graph edge has opposite tree parity, G is bipartite. A solution exists iff every opposite-parity chord identity holds. Then H is arbitrary in GL(d).
- Otherwise G has an odd cycle. A solution exists iff every opposite-parity identity holds and all same-parity chords agree with ONE SPD matrix S by the rules above. Then every solution is H=S^(1/2) O, O orthogonal.

**Proof.** The root factor is H. Given A_i, an edge uniquely forces A_j=C_ij^T A_i^(-T). Induction along T yields the two stated parity formulas. Substitution gives each chord rule. Conversely these rules make every edge equation true. The factorizations HH^T=S are exactly S^(1/2)O. QED.

This is an exact algebraic feasibility test. A failure has a concrete certificate: one violated chord identity, a nonsymmetric/nonpositive candidate S, or two incompatible same-parity chord matrices. Matrix dimensions are fixed locally; no exponentially large whole-state transition table is constructed.

## 3. Positive stochastic realization is an additional coupled condition

For each i the discovered baseline/gain mechanism is
K_i^H(y|c,z)=B_i(y|c)+s_i(c)[U_i A_i(H) z]_y.
Require zero-sum U_i columns and stochastic B_i. Retain only H for which every local row is nonnegative (or exceeds a declared positivity floor), for EVERY admitted c,y,z. Let Φ denote this common gauge set.

Algebraic frame feasibility does not guarantee Φ nonempty. Conversely every H∈Φ defines the normalized positive common transition
P_H(x'|x,u)=sum_z π(z) product_i K_i^H(x_i'|c_i,z).
The same Z is used by every factor and one fixed H is used for the entire run. This is the constructive positive joint witness, not merely a statement that some unknown global marginal might exist.

The set Φ couples ALL local contexts and all modules. Replacing it by independent marginal projections of Φ can admit mechanisms that violate the measured pair equations or positivity elsewhere. Global source/distribution uncertainty must likewise be retained as one common parameter/process rather than chosen independently for each edge.

For the autonomous local-state dynamics in the stress family, summing all outside next states proves that each observed pair has exactly the supplied pair transition kernel. Therefore all pair histories agree under any controller restricted to that pair's own history, provided the initial pair law agrees. Fixed-input stationary pair initialization also agrees because the positive pair kernel has a unique stationary law. This statement does not extend to a controller switching observation masks or selecting pair inputs from unobserved global states.

## 4. What an extra edge does

In a bipartite cover, a new opposite-side edge is a consistency test but does not restrict H if it passes. A new same-side full-rank edge determines S and reduces the GL(d) ambiguity to orthogonal ambiguity, subject to positivity. Thus the edge's parity precisely describes whether it only checks a predicted relation or removes a common scale/shear ambiguity.

In a nonbipartite cover S is already determined. Further pair edges can reject inconsistent descriptions but cannot resolve the remaining common orthogonal orientation.

Orthogonal freedom is NOT automatically a harmless hidden-label gauge. It is harmless only when the entire source law and all source dynamics are invariant under that transformation, or when these are transported as part of a genuine coordinate isomorphism. For a fixed finite axis-supported source, signed coordinate permutations are symmetries; a generic rotation changes higher-order moments while preserving covariance. Hence all pair tables can agree while a four-module experiment separates the worlds, exactly as in the stress example.

## 5. Local chart covariance and private labels

A local change of contrast basis U_i'=U_i T_i^(-1), T_i invertible, transforms
A_i'=T_i A_i,
C_ij'=T_i C_ij T_j^T.
The existence of a common frame solution and every physical stochastic row are unchanged. Thus local coordinate conventions may be arbitrary, PROVIDED the same T_i is used consistently on every incident edge and every local context. Independent relabeling of separate appearances of one module can create a false compatibility certificate.

This handles ordinary invertible local chart choices. It does not identify arbitrary non-bijective hidden-state presentations, nor does it prove that observational equivalence is always a coordinate transformation.

## 6. Refinement and timing

To regroup modules, retain the shared Z occurrence and all primitive conditional rows, then sum internal record coordinates after multiplying conditional rows. Both regrouping orders produce the same P_H. If a shared source is duplicated and independently sampled in the two refined branches, this equality fails.

Evidence refinement replaces Φ by a subset satisfying the new edge or higher-moment constraint. The record-level assembly diagrams still commute for every surviving H. No pathwise switching among gauges is authorized by set refinement.

All local input/context values are fixed before Z and fresh outputs are sampled. Current-time output feedback must be delayed or given a separately normalized simultaneous kernel. This construction does not justify products around an instantaneous causal loop.

## 7. Limits

This theorem verifies and reconstructs common response frames after conditional pair matrices have been learned. It does not discover arbitrary sensor patch boundaries, infer the source universe from data, certify the completeness of physical probes, supply finite-sample guarantees, or make positive-gauge feasibility automatically easy. It is stronger than independent local fitting and weaker than general unknown-architecture discovery. Its useful contribution to the program is the exact preservation of shared ambiguity through positive assembly and a computable obstruction/query structure.
