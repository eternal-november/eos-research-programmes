# Focused prior-art audit: compact-boundary CFS wiring

**Verdict (2026-10-30).** The displayed compact-boundary wiring theorem is best presented as an explicit derived corollary of standard compact trace and CFS orthogonality, not as a new categorical principle. Its value here is that it closes the honest-joint-realization gap with independently stated, checkable hypotheses. The proposed traced–Isbell completion needs a separate monoidal-construction proof; ordinary free-CFS freeness is not joint monoidal+CFS freeness.

## Nearest primary results, not merely similar terminology

1. **Joyal–Street–Verity, *Traced monoidal categories* (1996), Proposition 3.1.** The canonical trace is cup, followed by `f⊗1`, followed by cap. Substituting `f=m e` and cutting this composite between `e⊗1` and `m⊗1` gives exactly the carrier `M⊗H*`. Propositions 4.1, 4.2, 5.1 establish the fully faithful traced strong-monoidal embedding into Int; Proposition 5.2 gives its biuniversal property. [Published article](https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/abs/traced-monoidal-categories/2BE85628D269D9FABAB41B6364E117C8); [full paper](https://octocurious.com/papers/joyal1994-traced-monoidal-categories.pdf).

2. **Garner, *The Isbell monad* (2015), Lemma 2.3 and Theorem 3.3.** Lemma 2.3 gives unique isomorphisms between CFS factorizations. Theorem 3.3 identifies the Isbell envelope as the free CFS on a category. Its proof constructs functors and proves their laws by the same unique-diagonal-filler argument used for normalized substitution coherence here. Section 2 also identifies the underlying arrow factorization system. [Full paper](https://arxiv.org/pdf/1410.7108); [publication](https://doi.org/10.1016/j.aim.2015.01.015).

3. **Shulman, *\*-Autonomous Envelopes and Conservativity* (2021).** This is the closest additional completion technique found: enhanced Hyland envelopes, a polycategorical Day-convolution construction, and fully faithful structure-preserving embeddings. Theorem 5.2 recalls the Hyland envelope embedding; Remark 5.3 relates it to the Isbell envelope. It is a useful comparison for the completion proof, not a citation establishing CFS compatibility or compactness of arbitrary reconstructed middles. [Paper and publication DOI](https://arxiv.org/abs/2004.08487), [published proceedings](https://doi.org/10.4204/EPTCS.353.9).

## Exact coverage of the proposed theorem

- **Honest global carrier:** elementary cutting of the canonical trace. Only the traced wire H needs a dual. The absence of duals for M is already visible in the standard formula, not a separate new weakening.
- **Finite graph reduction:** tensor the local e-legs and m-legs, apply the declared permutation of fixed ports, and close internal wires. The graph-level statement packages these familiar operations; preserving the identical internal witness is essential for correctness but is exactly what cups/caps do.
- **Comparison span:** once the honest factorization `D→Z→T` exists, factor the preparation cocone and then the restricted observation cone. This is a short application of the CFS axioms. No tensor stability of E or M enters because tensor is used before, not through, normalization.
- **Normalized coherence:** equal interpreted cylinders have uniquely isomorphic normalized factorizations; composites of leg-preserving comparison isomorphisms are equal by uniqueness. This is routine uniqueness-implies-coherence, conditional on correct port typing and compatible reindexings. It does not establish a tensor operation on bare middle objects.
- **Raw flattening:** associativity/symmetry and coherent dual identifications account for it. Identity insertion can change raw carriers, as the draft correctly states.

These bullets are direct mathematical deductions from the proposed formulas and the cited machinery, not claims that a paper states the entire packaged theorem verbatim.

## Completion: do not overstate the universal property

The chain `C→Int(C)→I(Int(C))` is faithful on underlying categories by the two established embeddings. To use the last category as the ambient wiring doctrine, separately establish:

1. a symmetric monoidal structure on the full Isbell envelope, including the correctly varianced copresheaf component;
2. that its Yoneda embedding is strong monoidal;
3. hence that representable wire objects inherit their chosen duals, with preserved trace on the original language;
4. the selected universe/small-cylinder convention.

Garner's theorem is about the forgetful functor `CFS→CAT`; it does not supply these monoidal assertions. Even after proving them, say **free CFS on the underlying category Int(C), equipped with a compatible monoidal structure and designated dualizable representables**. Do not say **free monoidal CFS with designated duals** unless a new structured universal property has actually been proved. Nor should all envelope objects be called dualizable.

## Recommended positioning

“An explicit compact-boundary assembly lemma, combining canonical trace with cylinder factorization: local two-sided realizations yield an honest global realization, and canonical normalization is coherent without tensor preservation of the factorization classes.”

For the completion: “A conservative semantic realization obtained by composing Int with a monoidal realization of the Isbell envelope,” once the latter is proved. The remaining potentially substantive item is that precise compatible completion construction/universal property, not the cup–cap carrier itself. This audit found no primary result stating the full package exactly; that is not evidence of novelty.
