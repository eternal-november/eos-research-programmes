# Independent mathematical review

Reviewed source: `observable_exchangeable_width.tex`

SHA-256: `018330812e922cc0e2564be4cb605cc0386ddbb794ac73e3fa6de1078854ab03`

Review date: 3 November 2026, UTC.

## Finding

No unresolved mathematical defect was identified in the reviewed proof. This is a proof review, not formal proof-assistant verification or a novelty certification.

The assumptions remain essential: a compact parameter space, continuous consistent all-word laws, exchangeability at every horizon, and constant finite Hankel rank. No claim identifies these all-word assumptions from finitely many samples.

## Checked arguments

- Finite-rank exchangeable laws determine finite atomic directing measures, continuous local component labels, positive weights, and the component cover.
- Continuous finite-block classifiers give the two-block factorization for arbitrary native HMMs, including transient, unreachable, and redundant states, without hidden stationarity.
- The quantitative classifier bound, diagonal bound 6/7, exact-splitting denominator 3/28, and buffered disjoint-support denominator 1/2 are correct.
- The explicit threshold constructions establish both directions of the native-width/cover-section criterion without assuming a continuous decoder for a prescribed disjoint-support matrix.
- The uniform finite-horizon total-variation obstruction w_*/64 follows with the stated constants.
- Both ordinary state-emitting timing conventions retain the same width. The exact matrix identity is T diag(E_y)=L D_y Q; the reverse product has the same observable law by its intertwiner, and need not equal that matrix on unused rows.
- The signed lower bound embeds the centered predictive bundle in the fixed zero-sum native hyperplane; the normalized signed upper construction is compatible with the fixed terminal vector.
- D_{3,4}/S_3 is K4. The two-dimensional factorization criterion works for arbitrary monodromy image, not only surjective S_3 monodromy.
- The elementary D_{3,5} connectivity argument and the Moore-space Euler/Bockstein, stabilization, positive-emission, and 3/4/5-width arguments are sound.

## Additional explicit construction certificate

A separate 22-step edge-path contraction fills the exact triple of the one-spare C3 permutation path in D_{3,5}. It uses eleven square cells, eight triangle cells, and three backtrack folds. Its dependency-free verifier was rerun successfully. Applying the manuscript's buffered decoder formula turns that disk into a continuous five-state native construction. The finite check certifies this cell filling; it does not replace the mathematical proof of arbitrary-native necessity.

## Source boundary

Classical realization, exchangeability, stochastic-factorization topology, and configuration-space results have substantial prior art. The reviewed source makes this explicit. The review does not establish priority or rule out a pre-existing equivalent family-level theorem.

## Final source-only correction

The final report has SHA-256 `6ab7011c6be13c529017e68660e5e2892fa85a749c81c94c502a1642f543399a`. The only change from the source reviewed above is insertion of “rank-size” in the Mond–Smith–van Straten source-comparison paragraph. Reversing that insertion restores the exact previously reviewed hash. The final source was independently rechecked, with no mathematical blocker. The source/proof audit in `sources/prior_art_audit.md` records the final hash.
