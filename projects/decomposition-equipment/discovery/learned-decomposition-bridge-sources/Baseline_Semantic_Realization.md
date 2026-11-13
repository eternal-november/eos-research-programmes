# Semantic realization of the learned mechanism sparsity model

28 October 2026

## Status

This is an author level mathematical translation of the actual positive models returned by the source model class. It is standard kernel construction, not a new discovery result or an independently accepted contract theorem. Source identifiability is imported only with the exact hypotheses recorded in `Baseline_Translation.md`. No actual positive frame is supplied to the original learner: the frame below is its fitted output. We condition on a fitted model to explain what that output already witnesses.

This interpretation is in measurable stochastic mechanisms with retained event occurrences. It is **not** an assertion that the finite set span equipment previously constructed already represents arbitrary real valued kernels, their conditional probabilities, or all crossing factorization witnesses.

## Proposition B1

Fix a finite horizon (T), latent count (m), known auxiliary spaces and two learned parent masks (G^z,G^a). For each mechanism occurrence ((i,t)), let

\[
K_{i,t}:\prod_{j\in\operatorname{Pa}^z_i}\mathbb R^{t-1}
\times\prod_{\ell\in\operatorname{Pa}^a_i}\mathcal A_\ell^{t}
\rightsquigarrow\mathbb R
\]

be the normalized Borel probability kernel furnished by a valid fitted S26 model, restricted to the admissible joint auxiliary domain if its coordinates do not form a product. The argument for a valid S22 model is the same on its given supports. Let (E_t:\mathbb R^m\rightsquigarrow\mathbb R^{d_x}) be its Gaussian or zero noise Dirac emission kernel. These kernels can be time varying and can depend on whole parent histories.

Then the model has a positive, occurrence sensitive, typed hidden component realization with the following properties.

1. Mechanism (i) has a local history state (s_i^t=z_i^{1:t}). Its input ports are precisely its parent latent histories and parent auxiliary histories. Its state update samples (z_i^t) through (K_{i,t}) and appends that value.
2. Every incoming latent port is identified with the actual history produced by its parent; all uses of one producer agree. Auxiliary ports retain the same externally supplied auxiliary history across uses.
3. The emission occurrence at time (t) receives (z^t) and samples the readout through (E_t). It need not be a local sensor of any single latent component.
4. There is a normalized measure on whole latent and observed histories with exactly these conditional mechanisms. Its restrictions to earlier times or overlapping sets of occurrences agree on all common retained values.
5. Its observation marginal is exactly the fitted model's observation law. If the fitted model meets the source theorem's exact observation matching premise, that marginal equals the true observation law on the declared horizon and auxiliary domain.
6. None of these assertions requires the learner or a controller to observe the local hidden histories.

### Proof

Fix an admissible auxiliary history (a^{0:T-1}). Inductively construct a measure on the first (t) steps. At (t=1), use the learned conditional initialization kernel

\[
K_1(dz^1\mid a^0)=\bigotimes_{i=1}^mK_{i,1}(dz_i^1\mid a^0_{\operatorname{Pa}^a_i}),
\]

and then (E_1(dx^1\mid z^1)). This is the source's product conditional initialization; we have not substituted an arbitrary correlated law.

Given a history through time (t-1), define

\[
K_t(dz^t\mid z^{<t},a^{<t})=
\bigotimes_iK_{i,t}(dz_i^t\mid z_{\operatorname{Pa}^z_i}^{<t},a_{\operatorname{Pa}^a_i}^{<t}).
\]

This is a probability kernel because it is a finite product of normalized probability kernels on distinct current coordinate spaces. Compose it with (E_t(dx^t\mid z^t)). Iterating these kernels gives

\[
\mathsf W^a(dz^{1:T},dx^{1:T})
=\prod_{t=1}^T K_t(dz^t\mid z^{<t},a^{<t})E_t(dx^t\mid z^t).
\]

All measures are nonnegative. Integrating (x^T), then (z^T), gives one conditionally on the previous history, so integrating them out returns the previously constructed measure. Induction establishes normalization and time prefix consistency. The observation marginal is obtained by integrating the latent trajectory and is, by definition, the source generative observation law.

Take the witness space to be the trajectory space equipped with this measure. Its state maps are coordinate history projections; the latent input map at occurrence ((i,t)) is the corresponding parent history projection. Local event witnesses retain ((i,t)), these inputs, the old own history and new latent value. Port equalities hold pointwise because both sides are projections of the same actual trajectory. Identical parameter functions at different occurrences are not identified. Restrictions to sets of occurrences commute, hence shared values and their joint distributions agree on overlaps.

Deterministic port equalities or deterministic state append maps can produce singular joint measures. They do not need a positive density with respect to a product Lebesgue measure. It is the stochastic kernel that must be nonnegative and normalized; a zero measure diagonal under an unrelated product reference measure is not an obstruction. This also handles zero measurement noise through a Dirac emission.

All latent projections belong to the internal generative witness. Observation access is limited to the stipulated (X,A); no step of the construction returns (z^t) to a learner/controller. This proves all claims. ∎

### Exactly what the proposition does not say

The measure gives compatible restrictions of **one** learned construction. It does not say that arbitrary separately fitted marginal mechanisms glue, that any prescribed finite interfaces can carry the needed histories, or that overlap equality is a full coherent cut/2 Segal theorem.

Real valued history state has no finite digital precision bound, and its length grows with (t). At horizon (T) the displayed representation uses at most (mT) latent real coordinates, not a bound on their encoded bits. More economical finite sufficient states may exist, but need proof. Fixed parameter description, preprocessing cost, and dynamic memory are distinct charges. A global nonlinear (f) may require a global readout node; its existence is not a free distributed implementation.

The finite horizon identification premise provides no identification of kernels after (T). If a coherent family of kernels is independently supplied for every (t\ge1), the same construction yields compatible finite prefixes and the standard countable process extension; that extension is a fact about the supplied generative model, not new data supported identifiability.

## Corollary B2 on representation transport

Suppose two source models have the common image and transition transport relation (D) of `Baseline_Translation.md`, with (v=f^{-1}\circ\hat f). Apply (v) to each learned latent vector, leaving all actions and observations unchanged. Then this map pushes the learned trajectory measure to the true trajectory measure on the declared horizon.

**Proof.** At each step the change of variables formula (D) pushes the learned conditional latent kernel to the true conditional kernel at the transformed history. The equality (f\circ v=\hat f) makes the emission kernels identical after this substitution. Induction in (t), including the (t=1) kernel, proves the measure identity. ∎

This is a semantic measure transport. If (v) is a componentwise diffeomorphism after permutation, it also transports individual component event/state values after relabeling. If (v) mixes coordinates, it need not be a local map for a particular distributed realization. Neither observation equivalence nor this corollary ensures preservation of an arbitrary memory/message/precision type. A resource sensitive equivalence must be separately defined and proved. Transporting **all** physical allocation, readout, task, primitive language, and cost metadata along a coordinate change preserves the represented operational feasibility; a mixing map can fail a locality test only relative to separately fixed, untransported implementation constraints. Gauge ambiguity is not itself an intrinsic physical obstruction.

## Lemma B3 on a common permutation

This lemma makes explicit the consistent orientation used when combining the action and temporal conclusions of S26. It also avoids silently relying on the inconsistent transpose convention printed in Definition 36 of its HTML, Definition 15 of its PDF.

Let (v) be a diffeomorphism. Suppose

\[
\hat G^a=P_aG^a,\quad v=c_a\circ P_a^\top,
\qquad
\hat G^z=P_zG^zP_z^\top,\quad v=c_z\circ P_z^\top,
\]

where (c_a) is (G^a)-preserving and (c_z) is both (G^z)- and \((G^z)^\top\)-preserving, in S26's sense. There exists a single permutation (Q) and a diffeomorphism (c) preserving all three patterns such that

\[
\hat G^a=QG^a,\quad\hat G^z=QG^zQ^\top,\quad v=c\circ Q^\top.
\]

### Proof

At any point, (Dv) is invertible. A nonzero term in its determinant supplies a permutation (Q) with the support of (Q^\top) contained in that of (Dv), hence in the dependency pattern (V) of (v).

For either decomposition (v=c_b\circ P_b^\top), write (C_b) for the dependency pattern of (c_b). Then (V=C_bP_b^\top), so (Q^\top P_b\subseteq C_b). Every subpattern of a (G)-preserving pattern is (G)-preserving. Thus the permutation (Q^\top P_b), and its inverse (P_b^\top Q), preserve each of the patterns preserved by (c_b). Closure under composition now shows that

\[
c:=v\circ Q=c_b\circ(P_b^\top Q)
\]

preserves that same pattern. Using (b=a,z) establishes all three requirements.

For a (G)-preserving permutation (R), (R^\top\mathbb R_G\subseteq\mathbb R_G). Both subspaces have the same finite dimension, so equality holds. Their coordinate supports are equal, giving (R^\top G=G) and therefore (RG=G). Take (R=P_a^\top Q) to get (QG^a=P_aG^a=\hat G^a). Take (R=P_z^\top Q); preserving both (G^z) and \((G^z)^\top\) gives (RG^z=G^z) and (G^zR^\top=G^z), hence (QG^zQ^\top=P_zG^zP_z^\top=\hat G^z). Finally (v=c\circ Q^\top) by construction. ∎

This is the conventional alignment argument underlying S26 Appendix A.4.1, not a new scientific contribution. The graphical criterion then forces the common preserving map to be componentwise, exactly as in the source complete disentanglement result.

## Evidence boundaries

These statements establish the semantic positive witness inherited from actual source output and the allowed representation transport. The independent implementation, uncertainty, and structural comparison workers must add their claimed guarantees without pretending that B1 already establishes them. No finite state learner, universal short witness, algorithmic normalization test for arbitrary smooth functions, exact runtime decoder, or independent package acceptance is derived here.
