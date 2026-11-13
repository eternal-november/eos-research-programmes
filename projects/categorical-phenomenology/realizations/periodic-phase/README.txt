Observable periodic phase realization
Research source and verification package, 4 November 2026

Start with Periodic_Phase_Realization_Report_20261104.txt for the result and its boundaries. The complete proof is periodic_phase_observable_theorem.tex.

Frozen proof source SHA256
1098741a19d81f52f1371eed6b0a391b9f65e3302f7ba11e0409452b5af1eab3

Reproduce computational checks
Python 3.10 or newer is sufficient; both scripts use only the standard library.

  python3 check_periodic_phase.py
  python3 periodic_checks/verify.py

The saved outputs are periodic_phase_checks.json and periodic_checks/results.json. The second script reads the adjacent manuscript to report its hash. Exact checks use rational arithmetic. Its classifier and contamination calculations use deterministic floating-point binomial sums, not Monte Carlo. Python version fields can differ across machines; numerical fields may vary slightly with the math library. See periodic_checks/README.md for coverage and limits.

Verify package bytes
Run this from the package root before running scripts that write output files:

  sha256sum -c MANIFEST.sha256

Compile the proof if desired
In a normally configured TeX Live installation with standard AMS, geometry, enumitem, hyperref, and Latin Modern packages:

  pdflatex -interaction=nonstopmode -halt-on-error periodic_phase_observable_theorem.tex
  pdflatex -interaction=nonstopmode -halt-on-error periodic_phase_observable_theorem.tex

The proof source was compiled successfully in the research environment with no undefined references, overfull boxes, or LaTeX warnings. No PDF is included in this source package.

Contents
- Main TeX proof and readable result report.
- Two independently written formula/example verification scripts and saved outputs.
- reviews/: mathematical, reconstruction, stationary-block, and source-comparison reviews. Final-source approval is identified by the frozen hash; historical review hashes are retained to distinguish corrections.
- background/: the earlier exchangeable theorem and the separate probability-clock obstruction, included for context. The latter is not an input to the periodic proof.
- MANIFEST.sha256: hashes of all other files.

What is and is not verified
The mathematical reviews check the proof, including the arbitrary-native lower bound, initial zero phase weights, correct ordinary HMM emission conventions, finite-horizon obstruction, temporal Moore example, and classical dimensional corollary. Computational checks test finite algebraic identities and examples. They do not prove infinite-law representation, bundle topology, section existence or nonexistence, or uniform control over all parameter points.

The exact period, infinite symmetry, constant ordinary Hankel rank, and access to parameterized word laws are structural assumptions. This is not a finite-data inference algorithm or a classification of arbitrary HMM dynamics. Prior ingredients are explicitly credited; no priority or novelty certificate is supplied.
