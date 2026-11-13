INCOMPLETE-PROBE DECOMPOSITION DISCOVERY — 28 October 2026

Start with Incomplete probe decomposition results.txt, which includes a lay abstract.
The principal proofs are main/Vector_Directional_Theorem.md and gluing/Matrix_Atlas_Classification.md. The scalar directional note supports the principal result. Paired_Response_Discovery.md and Gram_Certified_Family_Gluing.md use stronger response-replication access and are optional routes, not assumptions silently added to the main theorem. Shared_Response_Algebra.md records supporting composition obstructions.

Scope: supplied candidate measurement patches; affine shared hidden effects; nonlinear local dynamics; conditional moment, rank, coverage, and positivity promises. Unknown noisy sensor calibration is exercised using exact observation probabilities, not sampled records. Finite-data local recovery bounds are proved; an end-to-end sampled-data implementation and finite-data global compatibility certification remain open. No unrestricted physical architecture recovery or original research-contract discharge is claimed.

Verification: independent AI proof review, seven reproducible Python checks, no Lean or external human verification. Python 3.12.14 and NumPy 2.3.5 were used. Run from this directory with OPENBLAS_NUM_THREADS=1:

python main/check_directional_refinement.py
python gluing/check_matrix_atlas.py
python gluing/check_shared_algebra.py
python stress/check_matrix_gauge.py
python stress/check_discovered_core.py
python stress/check_conditional_core.py
python stress/check_noisy_conditional_discovery.py --multiseed

JSON outputs and reproduction logs record the checks. The final script includes five sensor-calibration seeds. Review_Incomplete_Probe.md documents qualifications and corrections. audit/Baselines_and_Acceptance_Gates.md distinguishes standard ingredients from the integrated target. SHA256SUMS lists the exact packaged source bytes.
