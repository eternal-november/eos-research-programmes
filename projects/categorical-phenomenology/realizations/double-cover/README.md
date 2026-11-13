# Stochastic interfaces and exact rank two realization widths

This portable package contains a standalone technical report, detailed derivation notes, a numerical formula regression, an independent mathematical review, and SHA-256 checksums.

## Start here

Read `double_cover_split.tex` for the polished technical report. The main claims are:

1. The stochastic split-pair space is equivariantly homotopy equivalent to Hom(K_r,K_k), by an explicit buffered decoder construction.
2. For an everywhere observable rank-two, time-homogeneous stochastic family over a double cover, minimum continuous stochastic and normalized signed widths both equal g(ell)+1.
3. Necessity applies to arbitrary native competitors with fixed terminal vector, already from one- and two-letter probabilities; an explicit uniform robustness bound follows.

The report distinguishes split-interface classification from arbitrary higher-rank native realization. Global constructed models are nonnegative, not necessarily strictly positive. The topological and pointwise stochastic antecedents are cited; no novelty clearance is claimed.

## Files

- `double_cover_split.tex`: standalone editable LaTeX report, including bibliography links.
- `double_cover_split.md`: detailed derivation notes.
- `check_double_cover_split.py`: deterministic NumPy regression.
- `double_cover_split_checks.txt`: captured regression result.
- `double_cover_split_exact_review.md`: independent review tied to the report hash.
- `SHA256SUMS`: checksums of package contents other than the manifest itself.

## Build the report

With a standard TeX Live or MiKTeX installation containing AMS packages, Latin Modern, geometry, microtype, enumitem and hyperref:

    pdflatex -interaction=nonstopmode -halt-on-error double_cover_split.tex
    pdflatex -interaction=nonstopmode -halt-on-error double_cover_split.tex

Run a third pass if LaTeX requests it. No external bibliography file, image file, custom class or private path is required.

## Run the regression

Use Python 3 with NumPy installed:

    python check_double_cover_split.py

The captured run passed with maximum residual 8.88e-16. Different platforms may vary slightly in floating-point residuals. These checks validate formulas, not the topological proofs or novelty.

## Verify integrity

On systems with GNU coreutils:

    sha256sum -c SHA256SUMS

The LaTeX source is the primary report. The archive intentionally omits an unreviewed PDF and temporary build files.
