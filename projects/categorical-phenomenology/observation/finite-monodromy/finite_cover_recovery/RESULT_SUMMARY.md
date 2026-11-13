# Finite cover recovery: reviewed mathematical deliverable

Source: `finite_cover_recovery.tex`.
Rendered proof: `finite_cover_recovery.pdf` (7 pages; visually checked).

## Main theorem

For an exact continuously varying held IID p-component mixture on a known oriented circle, assume known atom separation δ, minimum component weight w0, and lifted-profile Lipschitz bound L. Query a cyclic mesh of V vertices with consecutive arc lengths h satisfying Lh ≤ δ/8. At each vertex independently restart N trajectories of length n, where

- N = ceil[w0^(-1) log(2Vp/α)]
- n = ceil[32δ^(-2) log(4VNd/α)]

Cluster their empirical frequency vectors using threshold δ/2, average clusters, and match neighboring estimates using the same threshold. With probability at least 1−α, this recovers every atom within δ/8 and the entire monodromy permutation up to conjugacy. It uses VN restarts and VNn symbols. Unknown p is supported using floor(1/w0) as the supplied upper bound. All full-law, separation, weight, regularity and access assumptions are prior promises, not certified from these data.

The deterministic core only requires local atom errors r and Lh+2r<δ/2, so it can consume any suitable local estimator. In particular, a ≤p-atom measure with W1∞ error <w0r has unique atom matching within r. Fan–Li's established short-snapshot mixture recovery is explicitly acknowledged; no novel or optimal local-estimation claim is made.

## Periodic extension

For period m, use full residue profiles and a lower bound on *rotation-averaged phase mass*, not on initially nonexistent phases. At every restart independently draw U uniformly from {0,…,m−1}, observe U+mt original-law outputs, discard U, and compute the retained empirical residue profile. Choose

t = ceil[32δ^(-2) log(4VNmd/α)].

The same confidence guarantee recovers full phase monodromy and the exact rotation permutation τ. Total symbols are at most VN(mt+m−1). The proof establishes independence and the averaged mass law explicitly.

## Lower bounds and limitations

An explicit fixed-p=3 family with trivial versus transposition monodromy gives, for any adaptive experiment design with at most S restarts and B symbols,

- worst-case error α ≥ (1/2)(1−2w)^S;
- α ≥ (1/4) exp(−64wδ²B).

Each experiment's parameter and length must be chosen before its own outputs. This implies an unavoidable rare-component restart budget and a (wδ²)^(-1) symbol scale, not optimality of all upper-bound logarithms or V dependence.

A hidden half-turn in an unsampled circle arc shows exact-word observations at finitely many prescribed parameters are insufficient without a quantitative modulus. For 0<δ≤√2/8 and L>0, an unqueried arc of length at least πδ/(√2L) can hide a Lipschitz-compatible twist.

Combined with the existing arbitrary-native circle theorem, recovered monodromy gives stochastic width p for identity monodromy and p+1 otherwise; normalized signed width p for even monodromy and p+1 for odd. This is conditional recovery of the target's invariant, not a claim to exclude an arbitrarily oscillatory competitor from finite vertex agreement.

## Review status

Independent mathematical audit of source SHA256 137724f0f1c29d3a84180513282ead25567df6281a564ff6b4424c37f59132d2 found no remaining theorem blocker after two scope corrections and a heading-only correction clarifying that randomized offsets are sufficient rather than necessary (the feasible δ range and L>0 in the mesh lower bound). The reviewer verified the confidence constants, unknown-p bound, closing-edge conjugacy, randomized-offset mixture law, phase intertwining, adaptive testing bounds, and primary-source attribution. The independent numerical/adversarial checker also reports no counterexample under the hypotheses: all good-event trials succeed; the periodic fixture includes zero initial phase weights; and an adversarial offset/latent dependence control confirms that marginally uniform offsets alone are insufficient. Reproducible checks are in `checks/`. The bounded-corruption statement is IID-only; a periodic version would require per-residue error control. Compilation has no undefined references or overfull warnings. `build_pdf.sh` documents the environment-specific font/format invocation.
