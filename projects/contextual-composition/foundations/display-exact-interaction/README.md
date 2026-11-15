# Display-exact native interaction and continuous unfolding

This is a **general categorical construction**, with semantic realizations and examples deliberately kept separate.

## Independent inputs, derived interaction

[Display-exact native interaction](Display_Exact_Native_Interaction_Criterion.tex) starts with:

- a pullback category and a pullback/composition-stable display class;
- the resulting display-map contextad, retaining all native slice arrows;
- a Cartesian monad preserving admitted displays;
- an independently valid contentad with compatible occurrence display, Cartesian grade transport and canonical Beck–Chevalley exactness.

The theorem constructs the native crossing, verifies pure-middle balance, derives its four comparisons and checks all ten coherence equations. The mixed crossing is **not** one of the inputs. The resulting relative multiplication acts on the literal retained comma family.

Compared with the original independent O1 criterion, this allows an arbitrary pullback base and Cartesian monad without a finite polynomial presentation. It instead restricts contexts to actual display maps. Thus it is complementary, not a strict generalization of every rig-coefficient context. Display-map distributive-law machinery has established precedents; no novelty claim is made.

## Continuous completion from primitive conditions

[Continuous completion and recurrent unfolding](Continuous_Completion_of_Display_Interaction.tex) imposes explicit inverse-limit conditions on the independent primitive categories and functors. It then proves continuity of the **derived** crossing, without interchanging relative coends and limits.

There is an actual recursive construction: a content grade Q over A with a supplied recurrent-boundary display r : dQ → A induces the endofunctor

`(E → A) ↦ (dQ ×_(SA) SE → dQ → A)`

on the context fibre. This is crossing followed by display accumulation. Under the stated continuity conditions its final sequence has a final unfolding context, and native content maps preserving r induce directed maps of those unfoldings. The proof uses standard final-coalgebra machinery, applied to the constructed categorical operation.

## Exact boundaries

The return arrow r and continuity hypotheses are genuine extra inputs. This does not establish a total trace, an arbitrary guarded-delay calculus or every infinite effect law. A pointwise occurrence monad need not commute with diagrammatic delay: their initial stages are S1 and 1. A shared-boundary display does not alone establish that arbitrary physical interference or dependence has been modeled correctly.

Infinite objects are formed in the specified presentation categories, not by silently replacing semantic data with bare underlying sets. There is no blanket claim that arbitrary comma fibres have terminal objects or final coalgebras.

## Verification and literature

Both written proofs were independently reviewed, including native maps, pure balance, all structural equations, typed inverse-limit domains and the recurrent-context endofunctor. They are not mechanized certifications. TeX compilation is unnecessary for this source delivery and was not run.

The manuscripts identify their relationship to the original O1 dossier, von Glehn's display-map distributive laws and standard final-sequence/guarded-domain literature. Verify exact source integrity with `sha256sum -c MANIFEST.sha256`.
