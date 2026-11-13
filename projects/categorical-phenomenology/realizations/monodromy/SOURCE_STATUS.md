# Source status and precedence

## Canonical circle report

monodromy_native_report.tex is copied byte for byte, SHA256 069b02aa54d0763bf5c1298d11078ef36a584bd1011d72b400eb2983a331590b. The final sections of both circle audits explicitly verify this revision. Earlier references to 4cb0e2a3dadcf102cf2a0c6dab1c1638b699f7d4489c12bfdafddb2be367922d concern the superseded revision, not a different hash of this final file.

The final report controls over earlier seed or review wording. In particular:

- It proves the arbitrary-p held-mixture circle classification and the sufficiently small primitive-transition extension. Older seed §7 roadmap language saying these remain unproved is historical.
- Its ordinary HMM convention is transition then emission, with the matrix identity on every slot. An earlier review discusses a different emission-first adjustment whose identity was restricted to reachable slots.
- The final source includes the fundamental-interval seam, stopped-query padding, and analytic differing-word/separating-vector qualifications.
- Finite measurement error must be included in e in any attempted numerical application of the net bound. The report does not compute κ.

## Supplemental snapshots

The final circle review does not certify all claims or exact current bytes of the companion documents. They are retained for context, proofs, source comparisons, and reproducible numerical examples; they are not a second exact-hash-reviewed final deliverable.

The source topology_finite.md has SHA256 c0229b28d90ee5f5f2ea70158263a5d964db8293e2073f5e7f3e0754f55f92ac. Its historical review records f9155a35170658255e9b3cd07c1dbc885af810fcf1cff9432d719579c7d3c9b0. The earlier snapshot was unavailable for an exact diff. Thus the historical review must not be represented as exact-current hash certification. Adding a supplement-status banner changes the packaged copy's hash; both original and packaged hashes are recorded separately.

The source topological_native_seed.md has SHA256 3fb00f319ccad203cb2ef99733bc3989a6fd27fd353c14cf546bed52ef583894. The source monodromy_native_seed.md has SHA256 2229667c1f407b6fb47344cb4cccd4b7e43c325510d4877c3b753a8f441868c4. See PROVENANCE.json for all input hashes and copy edits.

Supplemental source audits have bounded scope. In particular, a source not found in a targeted search is not evidence of novelty. Floating-point regressions do not certify strict inequalities under rounding error and do not validate every literature attribution.

## Packaging changes

No mathematical formula or proof in the canonical TeX was edited. Copied scripts with absolute output paths now write beside themselves; their mathematical calculations and assertions are unchanged. Copied research notes remove machine-specific paths and incidental development narration, distinguish historical revisions, and add supplement-status notices. Original inputs remain untouched.

The HTML and Markdown are full derivative reading copies. Citations are linked to individual bibliography entries, labels are preserved, and theorem numbering follows the TeX section counters. The HTML uses built-in MathML rather than external JavaScript or downloaded fonts. No PDF is bundled.
