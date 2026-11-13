# Continuous stochastic realization over a parameter circle

Research source package · 3 November 2026

## Main result

For a continuous circle family of uniform mixtures of p distinct categorical IID component laws, hold the chosen component fixed throughout each experiment. Continuing the component labels once around the circle produces a permutation σ. With continuous, globally fixed state labels:

- Each individual law has minimum stochastic and real width p.
- The minimum global stochastic width is p when σ is the identity, and p+1 otherwise.
- The minimum global normalized real-signed width is p when σ is even, and p+1 when σ is odd.

Both stochastic and normalized signed models use the fixed terminal vector of ones and normalized initial data. Signed means real coefficients; the parity obstruction is not a statement about complex coefficients. For p=1 every width is one.

The explicit rotating three-component example therefore needs four stochastic states but only three normalized signed states. Its finite rank-three Hankel block is constant and invertible. This distinguishes the component-label cover from the observable vector bundle. One spare stochastic state gives the exact upper bound, with continuous or smooth constructions. The proof also provides a finite-horizon uniform approximation obstruction, a sufficiently small primitive-transition extension, and a smooth finite-query impossibility result without quantitative regularity.

## Start here

- **Monodromy_Research_Report.html**: complete reading copy with offline MathML equations, proofs, bibliography, and linked references. Open in a modern browser.
- **Monodromy_Research_Report.md**: the same content in Markdown with LaTeX mathematics.
- **monodromy_native_report.tex**: canonical, byte-identical reviewed source. SHA256: `069b02aa54d0763bf5c1298d11078ef36a584bd1011d72b400eb2983a331590b`.
- **topology_monodromy_review.md** and **monodromy_finite_audit.md**: mathematical reviews, including explicit final-hash acceptance. Earlier revision comments are preserved and labeled; the final addenda control.
- **monodromy_native_checks.py** and its recorded result: triangle formula regression.
- **supplements/**: contextual static-bundle, temporal, finite-observation, source-audit, and numerical material. These are explicitly marked supplemental snapshots, not exact-hash-certified by the final circle review. See SOURCE_STATUS.md.

**TeX is supplied uncompiled in this package. No PDF is included.** No TeX compilation or PDF layout verification was performed for this delivery. The HTML/Markdown copies were converted from the canonical source; equation references use stable names rather than typeset equation numbers. The canonical TeX resolves any formatting ambiguity. The HTML conversion was checked for preserved equations, proofs, citations, and internal links; it has not undergone visual layout QA.

## Evidence and limitations

This is a research report with mathematical arguments and independent mathematical reviews, not a formal proof-assistant verification. No novelty clearance, priority claim, or exhaustive literature search is supplied. Hankel realization, finite-mixture identification, covering spaces, spare-slot configuration topology, and stochastic factorization geometry have substantial prior art. The report and accompanying source audits explicitly identify these antecedents.

The exact classification assumes distinct atoms and the stated held-mixture family over a known circle. It is not a theorem about arbitrary stochastic processes or arbitrary parameter bases. The parameter stays fixed within a word; no hidden-state transport across changing parameters is specified.

Word probabilities through length 2p−1 give the finite-moment lower bound; the linearly independent triangle needs only length three. The reconstruction criterion constructs a compatible mixture, but finite moments alone do not identify an unrestricted true all-word process. The approximation gap κ is existential, not numerically evaluated. A finite-net exclusion test needs a separately certified lower bound for κ and quantitative truth/candidate moduli. Its fit error e must include a valid simultaneous measurement-error bound.

The primitive extension holds for sufficiently small perturbations. Strictly positive local kernels do not imply a globally strictly positive spare-state lift: that construction retains structural zeros. Smoothness is established for the positive lift, not analyticity. The smooth moving-seam result permits increasingly large derivatives and does not establish an analogous randomized exact-oracle impossibility for analytic alternatives.

The companion sphere example separates varying-terminal real models from fixed-terminal normalized models. It does not by itself isolate positivity. The circle example does isolate positivity under matching normalization conventions.

## Reproduce the checks

Requirements: Python 3.12 and NumPy/SciPy. The included requirements.txt records the exact versions used in the clean-extraction run (Python 3.12.14, NumPy 2.3.5, SciPy 1.17.0). In your own virtual environment:

```
python -m pip install -r requirements.txt
python run_checks.py --output-dir run_results
python run_checks.py --include-supplements --output-dir all_results
```

The first command runs the canonical triangle regression. The second also runs nine supplemental regressions. The runner copies scripts into an isolated temporary directory, captures their assertions and JSON output, and leaves the source/results shipped here unchanged. Running an individual script directly writes its named result beside that script; the runner avoids that mutation. The two example scripts report JSON on standard output.

The triangle check samples 287 parameters, including move endpoints. It tests QL=I, stochastic row sums, endpoint gluing, the constant Hankel block, signed normalization, ordinary transition-then-emission HMM form, hold/cycle/refresh comparisons, and seven-step words. These are finite floating-point checks, not proofs of the covering obstruction. Supplemental finite-certificate scripts likewise do not implement rigorous interval arithmetic, even where result-field names contain “certified.”

**verification/summary.json** records the clean-extraction run, with individual outputs alongside it. **MANIFEST.json** and **SHA256SUMS** identify packaged files. **PROVENANCE.json** records original input hashes and copy-only portability/editorial changes. No reviewed original was modified.

## Sources

The report contains a 12-entry linked bibliography. Key direct antecedents include [Anderson on HMM realization](https://doi.org/10.1007/PL00009846), [Monràs and Winter on positive realization](https://arxiv.org/abs/1412.3634), [Allman, Matias, and Rhodes on mixture identifiability](https://jarhodesuaf.github.io/papers/Latent.pdf), [Vandermeulen and Scott on grouped mixtures](https://arxiv.org/abs/1607.00071), [Hazewinkel on parameterized realization](https://ir.cwi.nl/pub/10022/10022D.pdf), and [Abrams, Gay, and Hower on discretized configurations](https://arxiv.org/abs/1009.2935).

The linked UTD Vidyasagar manuscript may redirect. Detailed theorem references in the report are tied to the inspected 23 March 2009 manuscript, not automatically to the [published 2011 article](https://doi.org/10.1007/s00498-011-0066-7). The supplemental finite-data material identifies [Scoccola and Perea](https://arxiv.org/abs/2104.07563) as direct preceding work. Source-access and search-scope limitations remain in the audits.
