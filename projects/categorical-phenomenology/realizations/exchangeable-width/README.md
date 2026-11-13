# Observable exchangeable realization: source package

Date: 3 November 2026.

## Main result

`report.tex` proves an observable-first classification for continuous exchangeable word-law families of constant finite Hankel rank on a compact parameter space. It derives the component cover, predictive bundle, dynamics, and intrinsic positive cone from the laws. Arbitrary continuous stochastic realizations of width k exist exactly when the component-frame cover maps equivariantly to Hom(K_p,K_k). No retained local stochastic interface is assumed of the competing model.

The proof includes an explicit two-block extraction, a same-width exact-splitting repair, a uniform finite-horizon approximation obstruction, normalized signed width, and a four-output Moore-space example with pointwise width 3, normalized signed width 4, and stochastic width 5. Both ordinary state-emitting timing conventions have the same stochastic width in this class.

The exchangeability and all-word rank assumptions are essential. This is not a general classification of nonexchangeable temporal dynamics, not a finite-data identification guarantee, and not a novelty certification.

## Contents

- `report.tex`: final mathematical report.
- `reviews/final_mathematical_review.md`: independent review of the final source and constants.
- `reviews/native_bridge.md`: independent derivation of the arbitrary-native bridge.
- `reviews/moore_space.md`: independent topology and signed-width audit.
- `reviews/split_space_topology.md`: separate topological analysis of stochastic split pairs.
- `sources/prior_art_audit.md`: primary-source comparisons, exact theorem scope, and retrieval limits.
- `checks/five_slot_disk/`: explicit finite disk-filling certificate for the three-cycle using five native slots, explanation, and checker.
- `SHA256SUMS`: exact content hashes for all other files.

The independent derivation notes are supporting technical work. Where their formulas or numerical constants differ from the report, they are alternative valid choices, not replacements for the final report. The final report governs the theorem statements.

## Exact finite check

From this directory run:

    python checks/five_slot_disk/verify.py
    python -O checks/five_slot_disk/verify.py

Both commands were run and produced byte-identical output. The checker uses explicit exceptions rather than assertions, and also rejects a deliberately corrupted certificate. It checks a 22-step contraction consisting of 19 nondegenerate two-cells (11 squares and 8 triangles) and 3 backtrack folds. This finite check supplies an explicit filling of the relevant boundary in D_{3,5}. It does not establish the universal native-width lower bounds, the characteristic-class calculations, or novelty. Those claims depend on the mathematical arguments and cited topology.

## Build status

No PDF is included or claimed. Compilation was attempted, but this environment lacks the `pdflatex.fmt` format. The report is ordinary LaTeX source using standard AMS packages and `hyperref`; compile with a complete LaTeX installation if a rendered document is desired.

## Source discipline

The report explicitly credits classical exchangeability and moment reconstruction, positive realization, parameterized vector bundles, stochastic-factorization topology, and Hom-complex results. A targeted source search did not locate the exact family theorem, but this is not evidence sufficient to claim priority.
