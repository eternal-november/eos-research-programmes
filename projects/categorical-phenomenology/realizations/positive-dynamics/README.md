# Positive dynamics beyond a trivial predictive bundle

This package supplies a self-contained mathematical note and deterministic numerical regression checks. It contains no uploaded or externally hosted deliverable.

## Main result

For x in [0, 1/4], a binary renewal-law family with q=1/4, r=1−x², and θ=π/2+x is real analytic, full support, and of constant Hankel rank three. It has a normalized signed three-state realization with a fixed terminal vector. Every individual law has a finite positive realization. Its minimum positive width is four at x=0, but is Θ(1/x) as x decreases to zero through positive values. Hence pointwise positive realizability does not imply a locally bounded finite native state budget, even over a contractible compact base with trivial predictive bundle.

The note also proves the undamped clock's rational-denominator width formula, fixed-width finite-horizon exclusion, and finite-horizon realization at larger widths.

## Files

- `Positive_Dynamics_Obstruction.tex`: theorem statements, proofs, normalization, limitations, and bibliography.
- `check_positive_dynamics.py`: deterministic regression checks using NumPy.
- `checks_output.txt`: output from the recorded successful run.
- `requirements.txt`: exact numerical dependency used for that run.
- `environment.json`: Python and NumPy versions for reproducibility.
- `PROVENANCE.md`: inspected mathematical sources and verification scope.
- `SHA256SUMS`: hashes of all other package files.

## Reproduce the checks

From a Python environment containing the stated NumPy version, run:

    python check_positive_dynamics.py

The recorded run passed 20,347 checks. Maximum numerical residual was 1.19e−14. The minimum singular value of the sampled observable Hankel blocks was 0.00636328. Small platform-dependent floating-point changes in the last digits are harmless; assertions use an absolute tolerance of 1e−11.

The checks cover probability normalization, renewal word formulas, fixed-terminal signed coordinates, stationary initial distributions, rational finite-state lifts, explicitly constructed polygon lifts, finite-age truncations, and sampled spectral bounds. They do not prove the impossibility theorems or compute the exact optimal width of the damped cases. Those statements depend on the supplied proofs and cited matrix theory.

## Build the note

In a standard LaTeX installation containing the packages listed in the source, run twice:

    pdflatex -interaction=nonstopmode -halt-on-error Positive_Dynamics_Obstruction.tex

No PDF is included: the available TeX installation lacked its `pdflatex.fmt` format file. The source has not received a rendered-page layout inspection.

## Conventions and boundaries

Native models are time-homogeneous, outcome-labelled nonnegative kernels whose sum is stochastic. Exact state counts are not asserted for a stricter state-emission factorization convention. The external parameter remains fixed throughout each experiment. The default law starts after a reset; the note separately describes its stationary version, whose initial row varies while the coordinate matrix and terminal normalization remain fixed.

The probability-clock mechanism, polyhedral-cone criterion, and nonnegative-matrix spectral constraints are classical. The package claims no novelty certification for the analytic interval assembly. See `PROVENANCE.md`.
