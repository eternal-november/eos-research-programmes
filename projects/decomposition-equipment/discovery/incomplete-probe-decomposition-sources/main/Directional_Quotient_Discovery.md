# Directional discovery from incomplete shared-effect observations

## Statement and scope
This structured route discovers robust task components without reconstructing the amplitude or distribution of a shared exterior influence. Local nonlinear kernels and within-patch task partitions are unknown. Joint pair readouts identify the *direction* of the hidden response. Whether a proposed quotient deletes that direction is invariant under the unresolved scale. Remaining scale choices are tied by shared pair data, not independently chosen per component.

This is not unrestricted system identification. It assumes an affine, scalar shared-effect response, adequate local context coverage, and at least one observed nonzero response partner for every affected patch. The local state/input dependence can be arbitrary nonlinear. The hidden effect must be centered with common nonzero variance conditional on the challenged pre-update contexts. Fresh source noise independent of the past supplies this condition. Persistent sources generally do not, without a separate aligned experimental protocol.

## 1. Observation universe
There are finitely many instrumented patches i with latent finite alphabets X_i. Sensor calibration and patch alphabets can be learned via the existing three-view theorem; that step is not new and requires independent full-column-rank sensor channels and aligned samples. A local challenge context c=(x,u) contains current patch state and a finite bank of candidate observed input-history symbols. Correct inputs and local state quotient are not supplied. Challenge coverage includes the Cartesian pairs of contexts needed below. If contexts cannot be independently set, only the physically supported restricted statement is available; artificial Cartesian coverage cannot be inferred from marginal coverage.

For a shared effect W, local next-state response is

  K_i(y|c,W)=B_i(y|c)+a_i d_i(y|c) W.

Here B_i is a stochastic row, sum_y d_i(y|c)=0, and every displayed row is nonnegative for admitted W. Coefficients a_i are nonzero on affected patches. Normalize each flattened nonzero d_i to Euclidean norm one with a fixed sign convention; a_i is then signed. W has conditional mean0 and variance1 independently of challenged contexts. This unit-variance convention fixes only a scale gauge; it does not identify W's law. Given W and old contexts, local fresh innovations at different patches are independent. Local B_i,d_i are arbitrary nonlinear functions of c.

Pair observations on an undirected graph E supply full conditional next-patch joint laws J_ij(y,y'|c,d). Singles give B_i. Define flattened residual matrix

  D_ij[(c,y),(d,y')] = J_ij(y,y'|c,d)-B_i(y|c)B_j(y'|d).

Then D_ij = (a_i a_j) d_i d_j^T. No intervention changes W's distribution; one regime suffices. In particular no regime-by-hidden-effect matrix has full-column-rank information about W.

Coverage/relevance promise: every patch whose exterior response is nonzero is incident to an observed nonzero D edge (or has a valid same-mode self-replica). Zero incident matrices without this promise do not certify absence of hidden response. This is a substantive but sharply narrower assumption than perturbing every admitted exterior influence: only directions affecting instrumented patches need an observed response partner.

## 2. Readout recovery of response directions
Each nonzero D_ij has rank1. Its column space is span(d_i), its row space span(d_j). Hence exact pair laws identify every covered d_i up to scalar, regardless of the unidentifiable amplitudes a_i or law of W. Incident edges must give the same one-dimensional space at each vertex; incompatible spaces reject this declared one-shared-effect family.

After fixed normalization and sign conventions, extract lambda_ij=d_i^T D_ij d_j. These numbers satisfy lambda_ij=a_i a_j. They are part of the global compatibility certificate. The data do NOT permit separate independent intervals for each a_i.

Computational recovery uses matrix rank/singular vectors and no hidden-mode reconstruction. Near-zero singular values require relevance/conditioning margins; exact rank is not uniformly testable from finite samples. Unknown sensor inverse errors must precede this calculation.

## 3. Coarsest exterior-independent task quotient
Fix a nonconstant task h_i:X_i->T_i. A partition P is admissible if it preserves h_i and there exists an open response table Q(B|[x]_P,u) satisfying

  sum_(y in B) K_i(y|x,u,w) = Q(B|[x]_P,u)

for every block B, old x,u, and admitted w. The admitted W distribution has positive variance, so this is equivalent to TWO conditions:

  (direction cancellation) sum_(y in B) d_i(y|x,u)=0;
  (controlled lumpability) sum_(y in B) B_i(y|x,u)
       is identical for x in the same P block.

Neither condition depends on a_i. Both are inferred from readouts, although the whole response mechanism remains unidentified.

Algorithm: begin with P0 equal task signatures. At stage j, test direction cancellation on every current block and context. If any fails, report NO exterior-independent task-preserving quotient. Otherwise split each old block according to the vectors of B_i next-block probabilities over every observed input history. Continue until stable.

**Theorem.** Under the declared universe and observation assumptions, failure is a valid obstruction to every deterministic task-preserving exterior-independent quotient. Otherwise the algorithm terminates after at most |X_i|-|P0| strict refinements at the unique coarsest such quotient.

Proof: Let R be any valid quotient. Inductively R refines the current partition Pj. A failure of direction cancellation for Pj block B contradicts validity of R because B is a union of R blocks and the sum of their zero direction terms must vanish. If cancellation succeeds and x~R x', R-lumpability implies equality of B_i responses to every Pj block by summing R blocks; hence R refines the next split. At termination cancellation and B-lumpability give validity. Thus the output is coarsest and all reported failures exclude every valid R. QED.

This is not merely fitting an averaged quotient. A quotient of B_i alone may pass while its d_i block sum is nonzero. The extra direction test is exactly what prevents that false discovery.

## 4. Discovering the observed boundary
For the discovered P*, compare its autonomous Q(.|s,u) rows. Input histories u,v are equivalent when these rows agree for every s. Refine this equivalence to a congruence under the actual finite-history update map tau(u,a). The fixed point is the coarsest recursively maintainable deterministic boundary preserving Q.

A subset of input wires is sufficient precisely when Q is invariant to all changes of omitted coordinates on the declared admissible support. This is checked from response rows, not assumed from the probe. Exhaustive candidate-subset search is permitted and may be exponential. The result does not assert a joint state/communication optimum.

The output boundary is physically executable only for actually accessible input symbols and charged initialization. Noisy latent symbols give a generative boundary, not exact controller knowledge.

## 5. Shared amplitude compatibility
For one connected nonzero-edge graph, suppose at least one amplitude solution exists. If a and b are two solutions, r_i=b_i/a_i obey r_i r_j=1 on every edge.

- On a connected bipartite graph with parts L,R, all solutions have b_i=t a_i on L and b_j=t^(-1) a_j on R for a common nonzero t, subject to positivity of every local response row.
- On a graph with an odd cycle, t=t^(-1), hence t=+1 or -1. The remaining global sign is the W->-W gauge.

Proof: propagate r from a root along edges; even distance gives t, odd distance t^-1. An odd cycle forces equality t=t^-1. QED.

Cycle consistency and positivity provide joint compatibility tests. On bipartite cycles, alternating products of lambda values must agree. For a triangle, a_i^2=lambda_ij lambda_ik/lambda_jk must be positive and consistent. Amplitude choices can each fit one local marginal yet violate these edge equations. They cannot be assembled into one shared-effect world.

This graph algebra identifies residual uncertainty, not component membership by movement connectivity: the sought within-patch state quotient is found from full nonlinear response directions and controlled transition refinement. Nevertheless the shared-effect graph itself is supplied as an observation schedule, and the affine one-source class remains a favorable structural universe.

## 6. Positive whole realization and residual ambiguity
For each globally compatible amplitude vector and a positive source law for W satisfying normalization and positivity, draw ONE W per shared source occurrence and then conditionally independent patch next states from K_i. This yields a positive whole transition law. Using independent W_i per patch loses the observed D_ij and is invalid.

Different source distributions with the same first two moments give the same singles/pairs but can give different higher joint laws. For fixed amplitudes, a k-patch simultaneous outcome probability is a polynomial in moments E[W^r], r<=k. Thus triple or higher aligned experiments may be needed to distinguish remaining source laws; one cannot independently choose each degree's moment without a positive representing measure.

If W is fresh IID, the displayed transition law and initial patch law determine a trajectory law. If a larger universe admits source memory, the conditional centering/variance and independence conditions must be re-established given the contexts used for inference, and one globally coherent source process must be retained. One-time moment matching alone does not establish temporal equivalence. This theorem does not invent that extension.

For the discovered autonomous quotient Q, summing K_i over quotient fibers gives Q for every admitted W. The unresolved remainder can be conditionally disintegrated given the quotient update to preserve exact correlations. Such a dependent realization does not certify a physically restricted outward boundary: full quotient messages, residual state, and any access to private old state must be charged. Refinement-order equality follows from pushforward of ONE retained joint execution, not independent resampling of each factor.

## 7. Scope and relation to other candidate theorem
The paired-response Gram theorem in the companion note handles arbitrary response functions and nonidentified hidden effect spaces, but assumes stronger same-mode replica/challenge access. The rank-one cross-patch route above handles genuinely interacting nonlinear local mechanisms with ordinary simultaneous distinct-patch responses, but assumes affine one-source dependence and partner relevance. Neither route solves arbitrary passive decomposition discovery. Their common point is substantive: response equalities needed to discover useful quotients can be identifiable even when the underlying positive mechanism is not.
