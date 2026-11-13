# Formal Isbell/wiring theorem: independent product cylinders

Status: direct derivation from Garner's free-CFS theorem plus Kan-extension/Fubini calculations. No novelty claim; no assertion that it reconstructs a physical joint cylinder from local observations. This note does establish a concrete formal R/W comparison, not merely assume class preservation.

Primary source: Garner, [The Isbell monad](https://arxiv.org/pdf/1410.7108), Proposition 3.1 and Theorem 3.3. The source constructs the free cylinder-factorized category IC and characterizes its classes via the positive/negative projections. The external-product consequence below is derived here; this precise statement has not been located as a named published theorem.

## 1. Variance and explicit action

For clarity take small C initially and use suitable universes/small presheaves for iteration. An object X of IC is (X+,X−,ξ), with X+:C^op→Set, X−:C→Set, and

    ξ_ab : X−(b) × X+(a) → C(a,b).

A morphism X→Y consists of X+→Y+ and Y−→X− preserving the pairing. Thus the negative projection lands in [C,Set]^op.

For F:C→D, define IF by

    (IF X)+(d) = ∫^a D(d,Fa) × X+(a),
    (IF X)−(e) = ∫^b D(Fb,e) × X−(b).

These are respectively Lan_(F^op) X+ and covariant Lan_F X−; the latter is regarded oppositely when forming arrows. Their pairing sends representatives

    d --u--> Fa --Fξ(x−,x+)--> Fb --v--> e

to their composite. Naturality makes this well-defined on the coends. Both projections preserve the relevant colimits, so this construction preserves E and M, and extends F on Yoneda objects. Garner's free property therefore identifies it canonically with the pseudofunctor action IF. In particular the tempting use of RIGHT Kan extension on the negative Set-valued functor is incorrect here.

## 2. External products are genuinely constructed

For a finite list C₁,...,Cₙ define

    ext : product_i I(C_i) → I(product_i C_i)

by (ext X)+((a_i))=product_i X_i+(a_i), similarly on the negative side, and componentwise Hom pairing. Empty products give the Yoneda object of the terminal category.

Finite products in Set preserve small colimits separately in each variable. Consequently ext preserves E-cocones and M-cones **separately in each argument**, using the explicit classes in IC. This is a proof of the preservation property for this particular formal construction, not an assumption about physical wiring.

For any actual functor W:product_i C_i→D define

    W_I = I(W) ext : product_i I(C_i)→I(D).

It extends W on tuples of Yoneda objects. It has an explicit coend description, with W replacing F above and product_i X_i± as the weights.

## 3. Exact free-reconstruction comparison

Let r_i:D_i⇒T_i be small cylinders in C_i, with preparation index A_i and test index B_i. Write R_free(r_i) for the canonical middle of the Yoneda-image cylinder in IC_i. Its projections are

    R_free(r_i)+ = colim_(a∈A_i) C_i(−,D_i a),
    R_free(r_i)− = colim_(b∈B_i^op) C_i(T_i b,−),

and its pairing is induced by the entries of r_i and composition.

Define the product-indexed wired cylinder W(r_i) with preparations indexed by product_i A_i, tests indexed by product_i B_i, objects W(D_i a_i), W(T_i b_i), and entries W(r_i(a_i,b_i)).

**Theorem.** There is a canonical isomorphism of paired Isbell objects

    R_free(W(r_i)) ≅ W_I(R_free(r_1),...,R_free(r_n)).

**Proof.** For the positive projection, move the separate colimits through the finite external product and then through Lan_(W^op). The co-Yoneda lemma identifies Lan_(W^op) applied to the external product of representables with D(−,W(D_i a_i)). This is exactly the displayed positive projection of the left side. Apply the same calculation to covariant representables and the B_i^op colimits for the negative projection. On generators both pairings are W(r_i) composed with the outside arrows; hence these projection isomorphisms preserve the pairing. END PROOF.

This is a constructed formal R(W)≅W_I(R) statement for independent product cylinders. No CFS structure on the original C_i or D is required.

## 4. Unit, substitution and Isbell multiplication coherence

The external-product isomorphisms respect permutations and reassociation; Kan-extension Fubini gives

    (V∘(W₁,...,Wₖ))_I ≅ V_I∘(W₁,I,...,Wₖ,I)

when the inner functors use disjoint groups of input variables. The identity comparison is the co-Yoneda isomorphism. Their coherence follows because all maps act identically on the same coend representatives.

There is also a conceptual verification: iterating Garner's full-faithfulness result yields a multivariable free-extension uniqueness theorem for functors preserving E and M separately. The comparison isomorphisms above are the unique extensions of the corresponding maps on tuples of Yoneda objects. All coherence diagrams agree there, so agree everywhere.

The unit Y is compatible with ext because external products of representables are representable. Compatibility with Isbell multiplication μ can be checked by comparing

    ext_C (product_i μ_Ci)

and

    μ_(product C_i) · I(ext_C) · ext_(IC_i)

as functors product_i IIC_i→I(product_i C_i). Both preserve E and M separately. On tuples Y_ICi(X_i), both reduce canonically to ext_C(X_i), using μY≅1 and pseudonaturality of Y. Multivariable free-extension uniqueness supplies the comparison and its coherence. Thus the external products are compatible with the Isbell pseudomonad, not only its underlying action on objects.

This verifies the needed structure for lifting independent symmetric-monoidal/operadic operations to free Isbell envelopes. Packaging the whole construction as a pseudodistributive law for the free symmetric-monoidal-category pseudomonad requires choosing that pseudomonad and its strictification conventions; the operation-level result and μ compatibility above do not depend on that packaging. Do not label it a law for an unspecified 'all wiring' monad.

## 5. Sharing/correlation is a real boundary

Repeated-variable/cartesian substitution is NOT covered by the disjoint-slot theorem. Generally

    I(Δ_C)(X) ≄ ext(X,X).

The first positive presheaf at (c,d) is ∫^a C(c,a)×C(d,a)×X+(a), while the second is X+(c)×X+(d). For C=1, take X+=(a two-element set), X−=1 and the unique pairing into Hom=1. The first has two positive elements, the second four. They cannot be isomorphic as formal Isbell presentations. However, ALL scalar observations in this terminal-category example coincide. This proves only failure of formal cartesian/diagonal compatibility, NOT operational mission loss. R_free retains presentation structure and is not biextensional collapse or an arbitrary chosen CFS realization algebra. The first retains a shared formal choice; the second admits independent formal choices.

Consequently physical joint preparations, correlations, sharing, discarding, feedback and new cross-interface tests cannot be silently identified with the product-indexed formal cylinder. They require specified context-index maps, observation-compatible relations, or additional structural hypotheses.

If an actual cylinder is related to the product-indexed one by final reindexing of preparations and initial reindexing of tests, Garner's Lemma 2.7 gives a sufficient comparison route. Such final/initial properties must be proved from the context language; they are not guaranteed by the existence of local tables. More general noncofinal enlargement may change the reconstructed object and should retain a directed/span/relational comparison.

Only admitted finite cut composition is asserted. Guarded feedback may be handled through its declared finite unrollings; no trace theorem or infinite-limit interchange is supplied here.

## 6. Relation to actual/positive realization

Suppose D already has a chosen CFS with reconstruction algebra A:ID→D. Applying A to the formal theorem computes the canonical middle of the product-indexed wired cylinder. Comparing it with W(A_i X_i) in the physical category is a NEW step: A·W_I and W·product A_i need not be isomorphic. Garner's one-sided morphism theorem supplies comparisons if suitable properties are established, and the general honest-realization span lemma applies when a behavior-preserving realization has been derived.

Thus distinguish three questions: (1) semantic correctness for the actual declared joint observations and contexts; (2) representability or implementation in a chosen original/positive category, only when the mission requires it; (3) finite or budgeted constructibility. A formal Isbell object may itself be a perfectly legitimate phenomenological model once (1) is established. It need not recover a true hidden mechanism or lift back into C. The free theorem alone does not establish (1) for extra joint preparations/tests, nor finite constructibility.


## 7. Deterministic wiring versus joint horizontal interaction

Known double-category machinery distinguishes these roles without requiring ext to be cartesian. In the equipment Rel(Set), objects are sets, vertical arrows are functions, horizontal arrows are relations, and a square over functions f:X→X', g:Y→Y' asserts that (x,y)∈R implies (f(x),g(y))∈S. Horizontal composition is existential relational composition; restriction is inverse image along f×g. Thus an actual joint preparation is an arbitrary relation 1⇝X×Y, not automatically the external product of its marginals. Deterministic copying uses the graph of Δ_X and sends a preparation to a diagonal-correlated relation. Independent preparation uses external product instead. These are correctly DIFFERENT constructions.

Primary confirmation: Michael Lambert, [Double Categories of Relations](https://www.tac.mta.ca/tac/volumes/38/33/38-33abs.html), characterizes relational double categories as particular cartesian equipments. Shulman's [Framed bicategories and monoidal fibrations](https://arxiv.org/pdf/0706.1286) supplies the general vertical/base-change versus horizontal-interaction framework. No new completion is needed merely to carry correlation.

For probabilistic rather than support semantics, FinStoch already distinguishes Δ_*p from p⊗p: for a fair bit the former has masses 1/2 on 00,11, while the latter has mass 1/4 on all four pairs. The equality test distinguishes them with probabilities 1 versus 1/2. This is a genuine contextual observation distinction, unlike the terminal-category formal example above. [Fritz et al., Representable Markov categories and comparison of statistical experiments](https://strathprints.strath.ac.uk/85547/1/Fritz_etal_TCS_2023_Representable_Markov_categories_and_comparison_of_statistical_experiments.pdf) explicitly identifies copying with the diagonal Dirac kernel. Do not call FinStoch itself a full proarrow equipment without further construction: the necessary reverse/restriction operations need not remain normalized stochastic.

Double/poly-Chu likewise carries arbitrary joint pairings at a joint boundary profile and keeps covariant vertical maps separate from horizontal multivariable adjoint interactions. It does not force the joint profile to be represented by a tensor of local pairing objects. Its quotient cells then compare reconstructed pairings while retaining actual joint contexts.

The next precise gap is not “make the completion cartesian.” It is: specify the joint preparation/test object and actual horizontal interaction, construct an observation-compatible cell connecting local/formal data to that joint object, and prove those cells respect the admitted finite cuts. In a chosen equipment this may use restrictions/extensions and mates; their existence and exactness must be checked for the selected semantics. An ordinary functor W:C^n→C alone does not model every form of sharing, nonfunctional interaction or feedback.
