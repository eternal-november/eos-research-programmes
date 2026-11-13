# Partial experiments and response factors

This package asks when incomplete joint measurements justify a small response model. It contains complete elementary proofs, a sharp restricted-context testing theorem, an affine-code extension, primary-source comparisons, and reproducible finite checks. The work is a checked synthesis, not a novelty claim.

## Read first

- `world.md`: main report, from marginal ambiguity to a certified one-bit response factor, with the affine extension summarized in Section 8.1.
- `world_code_extension.md`: general affine response factors. Certifying their support and identifying their internal probability law require different conditions.
- `world_theorem_frozen.md`: compact exact repetition-code theorem.
- `world_final_review.md`: final mathematical review, assumptions, qualifications, and verification scope.
- `world_sources.md`: direct primary-source links for the extension. The main report has the broader comparison bibliography.
- `world_review.md` and `world_review_checks.json`: earlier detailed repetition-code review and its recorded exact diagnostics.

## Main conclusions

Local pointwise parity equations must span the full dual code to certify the proposed support uniformly. To identify a probability law inside that support, observations must cover every quotient character individually. Merely generating those characters by multiplication does not identify their expectations. Neither criterion implies the other.

The statistical theorem counts one context observation per fresh independent unit. It does not permit returning to that unit for further probes. The sampling contract, independently fixed candidate, uniform-null lower bound, and non-tolerant testing objective are essential. Exact identifiability is not a finite-sample stability guarantee.

## Reproduce

Python 3.10 or newer is needed for the scripts. The numerical checks also need NumPy and SciPy; install them in your chosen environment with `python -m pip install -r requirements.txt`. The recorded run used Python 3.12.14, NumPy 2.3.5, and SciPy 1.17.0. The check scripts themselves require no network access.

1. Run `python check_manifest.py` to verify the downloaded snapshot.
2. Run `python run_all_checks.py` to replay all four check scripts. Each writes its corresponding JSON result next to the script.

Individual commands are `python world_checks.py`, `python world_code_checks.py`, `python world_code_exhaustive.py`, and `python world_code_review_checks.py`.

The exhaustive script covers all affine codes and all context families through dimension three. Its 6,622 affine rank checks and finite nonvacuous LP optima use exact rational certificates; SciPy only finds candidate optima. The separate stopped-transcript script uses only the Python standard library and verifies 5,185 exact terminal likelihood ratios for 870 bounded adaptive policies.

The numerical results and proofs have different roles. Finite diagnostics supplement the general arguments; they are not a formal proof assistant or a physical experiment. `sha256.json` describes this delivered snapshot, including its recorded results. A rerun may alter floating-point formatting across dependency versions and hence result-file hashes without changing the mathematical assertions.

## Files and results

- `world_checks_results.json`: repetition-code, marginal, cut-LP, and sample-count diagnostics.
- `world_code_checks_results.json`: randomized affine-code, projected-coset KL, and retraction diagnostics.
- `world_code_exhaustive_results.json`: exact small-dimension classifications and witnesses.
- `world_code_review_checks_results.json`: independent rational adaptive-transcript and opposite-example checks.
- `requirements.txt`: numerical dependencies.
- `run_all_checks.py`: complete replay entry point.
- `check_manifest.py` and `sha256.json`: snapshot integrity check.

No third-party paper PDFs or private notes are included.
