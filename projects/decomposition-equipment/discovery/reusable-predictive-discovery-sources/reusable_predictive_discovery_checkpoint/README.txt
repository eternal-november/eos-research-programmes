Reusable predictive discovery source checkpoint
29 October 2026 UTC

Start with the report and its plain-language abstract. The main theory proves the weighted prediction bound, robust positive synthesis, finite program discovery, persistent uncertainty-family comparison and two certificate formulations. Supporting positive-source results are explicitly distinguished from the new evidence-to-interface construction.

The principal finite-data example is examples/Finite_Evidence_Weighted_Discovery.md. It represents 10.24 million synthetic IID episodes as 4096 histogram counts, not physical observations. Both the full episode count and H=2 limitation matter. The 1.024-billion-episode and exact-population files are intermediate calibration baselines, not the headline result.

Python 3.12.14, NumPy 2.3.5 and SciPy 1.17.0 were used; requirements.txt records dependencies. Scripts use exact rational/integer arithmetic for certificate calculations. NumPy generates compressed synthetic counts; the independent SciPy LP check is numerical corroboration rather than an exact proof. Published histograms are included, so the independent LP checker can inspect them without repeating sample generation. Reproducing seeded samples with another library version need not give identical bytes.

Run the nine checkers in this order from the checkpoint directory:
  python3 examples/check_service_interfaces.py
  python3 examples/check_finite_episode_discovery.py
  python3 examples/check_sampled_episode_discovery.py
  python3 examples/check_weighted_episode_discovery.py
  python3 tests/review_predictive_quantifiers.py
  python3 tests/review_service_and_sources.py
  python3 tests/review_weighted_predictive_bound.py
  python3 tests/review_weighted_episode_lp.py
  python3 tests/review_bounded_source.py

The billion-episode sampled baseline is optional for the headline result; it generates a compressed histogram without materializing those episodes. The first finite-episode script generates the rational source histogram used by the weighted sampler. Each checker prints JSON; generated result/data files are written beside the applicable example scripts. reproduction contains the portable rerun stdout and environment versions. Overlapping check counts must not be summed as independent evidence.

The exact/ideal-source certificate is J <= 0.043613. The bounded twenty-fair-bit driver has the slightly larger J <= 0.043653; both imply the same respective path-TV bound and pass the 0.05 threshold. A lower bound on J for a cheaper interface is not automatically the same lower bound on path TV. Random-source delivery, counter/state storage and acquisition assumptions are separate resources.

Two predecessor safety-representation proof notes are preserved unchanged under references/safety_representation for source semantics and evidence background. No original C5 generation or physical component identification is implied. Independent review is AI review, not Lean or human verification. No physical experiment or hardware installation was performed.

MANIFEST.json records byte sizes and SHA256 hashes for all other checkpoint files. The report is also delivered separately with identical bytes.
