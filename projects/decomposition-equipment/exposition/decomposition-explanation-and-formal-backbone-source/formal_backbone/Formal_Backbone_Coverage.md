# Formal backbone coverage and limits

2 November 2026. This package extends the recovered Lean backbone rather than
starting a second syntax or counting restated background as new mathematics.

## Recovered foundation freshly checked

The exact original WitnessedDecompositions sources, the three-interface
size-at-most-six graph representative, Lean 4.35.0 (commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), and mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679` are used. The pinned
lake-manifest is byte-identical to the recovered original. Only the working
lakefile adds a DecompositionBackbone library/default target; archived originals
remain unchanged. GraphCoordinates and GraphCutFragment are exact source copies
at the package root so Lake can build their imports without external paths. The public library
and refinement modules were freshly rebuilt. FreshCoreAxiomAudit.lean prints
all 60 previously indexed principal declarations successfully. Their closures
contain only the ordinary foundational axioms printed by Lean, not sorryAx or
new postulates. This is a fresh check of this precise slice, not a replay of
every historical script or a mechanization of all 36 obligations.

## New connected chain

1. JointArrayLifting formalizes one shared edge assignment and root-to-final
   word products. For all covered finite incidence diagrams, source-fixed
   lifting is equivalent to injectivity and factor-closed image of the monoid
   map. Necessity uses three literal finite probes: a zero-edge path, a
   two-factor path, and two paths with one shared parent. Sufficiency constructs
   a single inverse for every shared edge and proves uniqueness. Empty words
   remain observable. This is the algebraic repaired criterion, not a novelty
   claim and not an assertion that arbitrary cuts are CULF maps.
2. TreeArrayBridge constructs InputEdge and leafPath directly from the existing
   dependent Tree Signature API. It proves the nonerasing active-edge coverage
   lemma from an independent active-signature condition. Full generator labels,
   interfaces, ordered occurrence slots and empty branches stay in the original
   tree. Active-only edge arrays are equivalent to total arrays with inactive
   edges fixed to the monoid unit. Source equations are imposed only at active
   final leaves. The literal Tree.leaf case supplies the identity boundary;
   at an inactive colour there is no source coefficient.
3. GraphCoefficientBridge proves the activity condition for the actual recovered
   graph-cut signature and obtains source-fixed coefficient lifting for every
   finite tree in that representative. Its graph colours have at most six
   vertices; there is no depth bound on the typed trees. The general incidence
   iff is NOT advertised as a formalized iff for the full graph calculus:
   realization of all necessity probes in that calculus remains an explicit
   bridge debt. Ordinary interface or geometric lifting is not inferred from
   coefficient lifting.
4. JointQuotientDecoder formalizes the exact whole-record image equation and its
   equivalence to source-fixed soundness/lifting. Generated typed Boolean,
   deterministic and joint-cut tests are preserved by one synchronized record,
   not independent marginal witnesses; zero-factor records are included.
   JointArrayDecoderBridge instantiates the condition using the proved lifting
   theorem. TreeJointDecoderBridge supplies the active-only original-tree
   instantiation. These are preservation theorems, not free-standing assumptions
   that the desired decoder is exact.
5. RankSensitiveCompression and ActiveRankSensitiveCompression prove a proper
   profile-dependent group compression. ObsEq keeps a coefficient vector exact
   when its active occurrence type is subsingleton and otherwise retains its
   coordinatewise image under an arbitrary group homomorphism. A nontrivial
   C4-to-C2 two-coordinate example proves proper compression. The shared-parent
   root_lift theorem is iterated by active_all_tree_lift on the original Tree:
   every tree and every source representative receives one whole compatible
   decoration, including arbitrary inactive positions, nullary vertices and
   vertex-free trees. active_evaluate_congr supplies forward soundness;
   active_exact_tree_decoder combines both directions. Actual source and whole
   decoration setoids are constructed, and active_quotient_exact instantiates
   the generic ExactDecoder theorem rather than assuming exactness. No
   surjectivity assumption on the group homomorphism is needed for its image
   quotient. The ActiveSignature nonerasing assumption is explicit.
6. ActiveDecorationBridge proves inverse conversions between those recursive
   positive-model decorations and the same inactive-unit-extended InputEdge
   arrays used by the lifting modules. activeEvaluate_eq_path proves equality
   of their evaluations at every active final occurrence. Its
   graph_active_exact_decoder specializes to the actual recovered graph-cut
   signature. Thus the proper positive compression and the uniform-map no-go
   concern distinct representations on the same typed tree machinery, rather
   than unrelated examples. This formalizes decoder existence and soundness,
   not the manuscript's coarsestness or optimal state-count theorem. The quotient
   carriers and exact decoders are fixed-tree source/whole-factor setoids with
   the proved graft congruence; an assembled quotient multicategory universal
   property is not claimed by these modules.

## Deliberate boundaries

The generic all-incidence theorem is stronger in its indexing class than the
finite tree specialization, but does not manufacture a geometric realization
of an arbitrary diagram as a graph cut. Conversely the concrete graph bridge
is sufficient, not the formalized necessity direction of the original full
old-graph theorem. The word-based naturality lemma applies to specified
word/contraction maps; it is not by itself an all-equipment interchange theorem.

This tranche does not formalize the universal virtual-equipment construction,
ordinary-equipment completion, all-degree simplicial recognition, incidence
coalgebras, full observational minimality/stabilization theorems, or every
original scope claim. These remain written mathematics. It supplies a reusable
core through the most consequential corrected source-fixed lifting boundary,
an exact joint decoder, and a positive compression route.

## Regression boundary found while building the bridge

An empty final occurrence may lie below an active ancestor. Its path product
need not be the monoid unit, although it has no source coefficient. Therefore
extending inactive *source* leaves by a unit equation is invalid. The actual
graph example nestedEmpty has an inactive retained leaf whose path product is
2 in the multiplicative natural-number monoid. The formal bridge uses only
active final leaves and proves this counterexample. This correction changes
neither the older theorem nor its allowed empty positions; it prevents a false
new formal encoding. Inactive input edges, by contrast, do have the legitimate
canonical unit extension.

All files use kernel proofs rather than `sorry`, new axioms, or finite numerical
extrapolation. Official precompiled mathlib dependencies are used and disclosed;
project theorem sources are freshly compiled. The strict verify_backbone.sh entrypoint invokes the default Lake build, which
includes every new module, then checks the recovered 60 principal declarations
and all 83 new theorem declarations with Lean axiom reports. No optional file
existence guard silently skips a required proof. The final clean-copy package
replay supplies the independent executable evidence.
