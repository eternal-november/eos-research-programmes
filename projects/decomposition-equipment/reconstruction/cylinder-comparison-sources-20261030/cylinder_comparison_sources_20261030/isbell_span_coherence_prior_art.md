# Focused audit: Isbell comparison-span coherence

**Verdict.** This is a genuine strengthening of the previous result: it identifies actual compatible comparison spans, not just their final middle objects. The safest framing is a **specific coherent-normalization theorem derived from established Isbell and adequate-span machinery**. Neither “a new relational calculus” nor “already exactly a published Chu theorem” is supported by this audit.

## Closest additional primary source

Haugseng–Hebestreit–Linskens–Nuiten, *Two-variable fibrations, factorisation systems and ∞-categories of spans*, **Forum of Mathematics, Sigma 11 (2023), e111**, is directly pertinent:

- Definition 4.2: orthogonal adequate triples combine an OFS with existence of mixed pullbacks and the assertion that every mixed square is cartesian.
- Remark 4.3: preserving the two classes then automatically suffices for preserving these pullbacks.
- Definition 2.12 / Theorem 2.13: the span construction is functorial and coherently composes by pullback.

[Published paper](https://doi.org/10.1017/fms.2023.107), [full text with numbered results](https://arxiv.org/html/2011.11042), [author PDF](https://www.math.univ-toulouse.fr/~jnuiten/Writing/Spans.pdf).

**Orientation matters:** their egressives E are the left OFS class and ingressives M the right; their spans are E-left/M-right. The draft's M-left/E-right spans are the opposite span category, obtained by reversing each span. Do not assert a reverse OFS (M,E).

Thus the draft's mixed-square/pullback-preservation mechanism has a precise published structural home; it is not merely reminiscent of generic Chu duality.

## What remains specific to this proof

Garner's *The Isbell monad*, Proposition 3.1, gives the projection-described CFS; Lemma 2.3 gives uniqueness of cylinder factorizations. The singleton projection description yields E₀=positive-isomorphism and M₀=negative-isomorphism. [Paper](https://arxiv.org/pdf/1410.7108), [publication](https://doi.org/10.1016/j.aim.2015.01.015).

The following assessment is a deduction from the audited proof, not a claim that the sources state these exact results:

1. **Span-cell rigidity:** the two exterior triangle equations determine the positive and negative components separately and force both invertible. This is an elementary but useful extra feature of the Isbell signed-component presentation; it is stronger than merely having an arbitrary adequate triple.
2. **Canonical fixed-cylinder comparison:** CFS orthogonality produces the apex map from the generated part G_X into any compatible polarized span X⇝R. Rigidity makes that map an isomorphism. This is the task-specific substantive lemma: compatibility with the same preparation/test cylinder supplies the map whose existence generic span calculus does not guarantee.
3. **Network substitution:** once the previously proved tensor preserves E₀/M₀, adequate-span functoriality handles pullback composition; the cup/cap equations handle preservation of the actual realization legs. Combining these with (2) gives the displayed invertible comparison compositor. Coherence then follows from local uniqueness.
4. **Changing raw source carriers:** explicit identity-insertion maps/spans remain necessary. Generic coherence does not identify spans with different endpoints. The draft correctly retains these boundary changes.

## Recommended statement

“Within the monoidal free Isbell envelope, canonical normalization of realizations of a fixed actual cylinder is coherently compatible, as polarized comparison spans, with the declared typed network assembly. The proof uses the signed-component Isbell factorization, the standard adequate-span calculus, and compact-boundary realization maps.”

This formulation records a real closure of the stronger comparison obligation without implying a new universal categorical calculus. I did not locate the exact fixed-cylinder normalization-and-wiring statement in a primary publication; that absence is not a novelty argument. The trace/partial-trace completion route enlarges the supply of semantic models but does not itself establish operational admission or a joint free monoidal-CFS universal property. No claim about changing actual cylinders or arbitrary intervention contexts follows without the specified bridge.

