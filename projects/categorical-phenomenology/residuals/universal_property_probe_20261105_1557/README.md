# Controlled training response note

Final standalone source: `Controlled_training_responses.tex`. It is intentionally uncompiled. The note states and proves the exact discrete/continuous Gram response classification, scalar and fixed-width boundaries, target-switching requirement, minimum-width consequence, reset access, global controlled-flow existence, and sharp bounded-depth adversarial-noise threshold.

The source identifies the result as a corollary-level refinement of existing covariance, mobility and conservation-defect identities. It makes no historical novelty, new general universal property, optimization, or empirical-benefit claim. The closest primary sources, Zhang–Peyré and Tao, are explicitly compared alongside Marcotte et al., Kunin et al., and Pang et al.

## Verification

- `python check_gram_behavior.py` runs the original exact rational/symbolic checks; output is `check_results.json`.
- `python independent_audit/verify.py` runs the separate audit's exact observation-rank and symbolic checks plus numerical regressions; output is `independent_audit/results.json`.
- `python check_tex_source.py` checks source braces, environments, references and bibliography without compiling; output is `source_integrity.json`.

These tests are regression evidence. The note's proofs establish the arbitrary-dimensional statements. No proof-assistant or visual-layout verification is claimed.

## Preserved history and sources

- `Controlled_training_responses_draft_v1.tex` is the initial TeX draft, preserved unchanged.
- `gram_behavioral_theorem.md`, `prior_art_and_scope.md` and `README_before_tex.md` preserve the original exploration. Their source audit predates discovery of the closest Zhang–Peyré and Tao papers and must not supersede the final note or the later audit.
- `independent_audit/proof.md` and `independent_audit/priority_audit.md` retain the separate verification and current primary-source comparison.
- `SHA256SUMS.txt` records final file hashes, excluding itself.

The earlier `universal_property_probe_checkpoint_20261105.zip` is preserved separately. This expanded note is a new checkpoint, not a replacement for it.
