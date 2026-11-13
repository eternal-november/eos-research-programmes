Evidence efficient discovery source checkpoint
29 October 2026 UTC

Start with the TXT report and its plain-language abstract. The final protocol is examples/Final_Operational_Discovery.md and the monitor_service_* files. The sparse_service_* and joint_time_service_* files are explicitly separate development runs. No physical experiments were performed.

The final model was trained on 10,000 episodes and validated unchanged on 200,000 fresh episodes (50,000 per controller). Its prescribed one-pass workflow therefore uses210,000 episodes. The complete investigation used500,000 unique synthetic episodes including both development protocols. The saved monitor_service_training.npz repeats the same training records as the second development run; it is not an additional acquisition. Reproducing a fixed seeded sample is not new independent evidence.

The final guarantee is operational monitor-law accuracy, not full-trajectory TV or arbitrary-controller coverage. It covers84 fixed-index triples of joint readout times and4 maximum-run laws under4 specified controllers, with separate observed warmup initialization. Arbitrary conjunctions of monitor outputs, within-episode adaptive time selection and untested controllers are not automatically covered.

Exact/numerical-predictor bound:0.040428 outward. The bounded twenty-fair-bit generative implementation adds a deterministic approximation allowance and has bound0.040589. Both use the same evidence/confidence event; no new data were collected for the implementation adapter. Hardware capabilities and physical hazard semantics remain separate assumptions.

Python3.12.14 and NumPy2.3.5 were used (requirements.txt). Standard-library rational/integer arithmetic checks the certificates and model probabilities. NumPy supplies synthetic data and raw-array inspection. NPZ files preserve the actual raw samples. Reproduction across different RNG library versions is not guaranteed byte-identical; the included data permit independent checking without regenerating samples.

Full reproduction order:
  python3 examples/check_sparse_service_discovery.py
  python3 examples/check_joint_time_service_discovery.py
  python3 examples/check_monitor_service_discovery.py
  python3 examples/check_compiled_predictor.py
  python3 tests/review_operational_certificate.py
  python3 tests/review_final_monitor_certificate.py
  python3 review/independent_raw_review.py
  python3 review/independent_bounded_sampler.py

The first two commands reproduce separately labeled development protocols; the third is the final protocol. The independent review scripts inspect stored records and probabilities separately from the author implementations. reproduction contains stdout from the verified portable run. Overlapping counts should not be added into a total of independent proof evidence. Review means independent AI review, not Lean, human or physical validation.

All source files needed for this checkpoint's calculations are included. MANIFEST.json gives byte sizes and SHA256 hashes for every other checkpoint file. The separately delivered report has identical bytes to its archived copy.
