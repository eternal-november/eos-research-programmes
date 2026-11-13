# Prior-theory audit: explanatory revision binding

Reviewer: `/root/review_integrated_comparison_target`, 25 October 2026.
This addendum preserves the original audit at SHA256
`8ad93c3bda1578df70120c53d7cda308ce216293b689e080bca063f37b513a60`.

I compared the preserved pre-provenance proof drafts with their revisions:

* `proof/Semantics_Transport_Factorization.md`, now SHA256
  `dbbf64f3c2cb49301d03df01ed5cddca2b8dcbad3efe8a701d2f5f852f462c84`;
  prior hash `b18b9ade4b0cab8a44a4c6e2d41a4f9b3d86563cda4d36784605daaec28c6c43`.
* `proof/Completion_Comparison.md`, now SHA256
  `27f4754cf81822034b0fd4f2268af75075e28de2110b66c6c53b0b6db37e6e1d`;
  prior hash `5c2351e22a3f19c27520a81c94d3c5b5899e6c314bcf37818fda3ae12b5f8fd8`.

The semantic revision only adds explicit provenance for the small-N extension
of the inherited principal N≥6 quotient adapter. The completion revision adds
that provenance and corrects the scope of Mimram's Lemma 3.23: its stated
setting is a presented groupoid, whereas Comp has noninvertible grafts. The
normal-object equivalence for Comp uses the elementary full-subcategory
argument with chosen isomorphic representatives, not literal application of
the groupoid-only lemma. The direct published O application is unchanged.

These changes do not alter the product/pullback baseline, mixed-basis
comparison, or prior-theory verdict. The original audit's conclusions apply
to these revised bytes. This is not a substitute for the separate full P
correctness review, and it establishes no scientific novelty or new phase
acceptance.
