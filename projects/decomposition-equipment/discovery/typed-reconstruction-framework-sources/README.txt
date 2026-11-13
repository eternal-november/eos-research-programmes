TYPED RECONSTRUCTION FRAMEWORK
29 October 2026

Start with Typed reconstruction framework results.txt and its plain-language abstract.

New proof notes
- main/Typed_Cover_Descent.md: view reconstruction on typed operation fibres; quotient refinement versus actual endpoint lifting; retained witness/equation fibres; cut/transport admissibility.
- main/Mixed_Presentation_Criterion.md: sufficient local domain/residual checks for all finite contexts. Forward descent does not imply reverse lifting.
- main/Affine_Descent_Model.md: positive-arity unit-affine application, modular views, normalized cuts, derived internal gauges, shared overlapping intervals, exact refinement lifts and fibre counts.

Scope
Profiles, occurrence order and root types remain supplied anchors. The results reconstruct operation witnesses, not unknown physical architectures or types. Chinese-remainder and quotient-square lifting mechanisms are established mathematics. The affine model is not nullary, does not silently exchange occurrences, and its root normalization is not compatible with every degeneracy insertion. No unital 2-Segal claim is made for its unrestricted factorization structure. The original C5/F3/I4/I5 obligations remain open as detailed in the report and contract audit.

Reproduction
All four checkers use only the Python standard library. Python 3.12.14 was used. Run from this folder:

python tests/check_reconstruction_boundaries.py
python tests/check_affine_descent.py
python review/check_hereditary_crt.py
python review/check_affine_review.py

The author affine checker records 78,114 exact finite tests, including fixed-seed sampled cases and exhaustive subchecks. The independent checkers cover all 3,375 equivalence triples on four points, 24,576 affine transport cases and 32 candidate section lifts. The separate boundary checker covers 711 permutable triples and 610 finite factor-map cases. These are overlapping verification suites, not independent population counts to add together. Unbounded claims rely on the written proofs.

reproduction/ contains final run output. review/ contains independent AI mathematical and scope reviews. No new Lean verification or external human peer review was performed.

Historical references
references/ contains selected previously delivered proof notes and contract texts for the non-retread audit. They are reference material, not new results or a re-verification of their entire old build. Historical acceptance ledgers, complete code archives and older report-only sources named by the audit remain in their earlier source packages; they are not all copied here. New audit source locators were made portable without changing their mathematical assessment. Historical proof reference bytes are otherwise unchanged.

SHA256SUMS records every packaged file except itself. The report and source archive were checked after saving.
