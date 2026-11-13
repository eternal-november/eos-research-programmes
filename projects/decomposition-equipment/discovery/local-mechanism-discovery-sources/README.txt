Local mechanism discovery source checkpoint
28 October 2026

Start with Local mechanism discovery results.txt, which includes a plain-language abstract. The main proof is main/Dynamic_Product_Atlas_Discovery.md. The complementary local-to-global and unresolved-realization theorem is gluing/Positive_Atlas_Gluing.md. Product_Factor_Rigidity.md gives a self-contained proof of a classical tensor-preserver specialization, with attribution.

The milestone discovers unknown finite local state factors, aligns their observation patches, infers nonlinear delayed mechanisms, and constructs deterministic recursive boundary summaries within an explicit stochastic model universe. It also retains unresolved patch-compatible atlases and gives local checks implying global positive transition equality. The finite-sample wrapper uses fixed conditioning and separation assumptions and a proved-finite calibration constant that has not been numerically evaluated.

The assumptions are substantial: supplied independent three-view sensor bundles with full-column-rank channels, full coverage by bounded latent patches, positive independent fresh updates conditional on bounded past dependencies, aligned stationary data, and stated separation or ambiguity handling. Identified latent states do not become physically available sensor readings. This is not an arbitrary-world membership or safety guarantee, a production implementation, a new Lean formalization, or discharge of the original research contract.

Proof and review files

- main/Dynamic_Product_Atlas_Discovery.md: exact discovery, deterministic interface refinement, finite-data stability and sampling theorem.
- gluing/Positive_Atlas_Gluing.md: coherent atlases, exact and approximate positive gluing, finite constraint families, delayed initialization, and crossing-summary examples.
- Product_Factor_Rigidity.md: finite product-preserving recodings, generic separation and robustness.
- stress/Growing_Hidden_Patch_Family.md: nonlinear growing family, private-factor discovery, delayed mechanisms and surviving ambiguities.
- Review_Dynamic_Discovery.md: independent AI mathematical review, including corrected empirical-parent selection and calibration proof.
- audit/: strongest inspected prior-art baselines and target-fidelity review. No priority claim is established.

Reproduction

Verified with Python 3.12.14 and NumPy 2.3.5. The scripts use the Python standard library and NumPy. From the extracted archive directory run:

python check_product_rigidity.py
python stress/check_hidden_patch_discovery.py
python stress/check_private_complement_discovery.py
python stress/check_growing_private_cycle.py
python gluing/check_positive_atlas_gluing.py
python main/check_recursive_boundary.py
python main/check_local_error_transfer.py

All seven scripts passed in the final regression run. Saved output is under reproduction/; several scripts also produce adjacent QA JSON files. Small full-state models occur only in test-data generators and independent verification. The local discovery routines consume bounded observable probability tensors. The tests use exact-law numerical fixtures, not sampled finite datasets or a complete implementation of the calibration optimizer or unresolved-atlas constraint solver. Exact integer/rational checks are explicitly identified where used.

The growing numerical cycle uses immediate coupling; the analytical growing family includes an additional delay. Its raw table bound is therefore different, as documented. Sixteen fair private charts pass a local product test, but a tighter global parent budget can reject some. Recursive and crossing state-count lower bounds apply to the stated deterministic retained-state contracts, not all output timings or stochastic machines.

manifest.sha256 records the packaged source bytes. Reproduction verifies the executable examples, not the general mathematical proofs. The latter have independent AI review, not external human peer review or formal proof-assistant certification.
