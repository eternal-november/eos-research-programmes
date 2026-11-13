# 10 — Relation-first dynamics, allegories, Kleisli categories, and effects

**Origin:** chat L920–946, L1239–1351, and L1682–1742. **Status:** distinctions corrected; formal comparison expanded.

The valuable move here is refusing to assume that every physical or computational transition is a single-valued function. There are **several** ways to relax that assumption, and they preserve different information.

## Bare relations

A transition \(R\subseteq X\times Y\) relates one input to zero, one, or several outputs. Composition is existential elimination:

\[
(x,z)\in S\circ R\iff \exists y:\ (x,y)\in R\land(y,z)\in S.
\]

Relational converse \(R^\circ\subseteq Y\times X\) reverses pairs. **Converse is not inverse:** a many-to-one law remains multivalued backward. Bare relations provide no probability, duration, optimality, or distinction between deadlock and a failed precondition.

## Allegories

An allegory is a locally ordered relation-like category with hom-set binary meets, an identity-on-objects contravariant involution \((-)^\circ\), and the **modular law**. For composable \(R:X\to Y\), \(S:Y\to Z\), and \(T:X\to Z\), its relational form is

\[
(S\circ R)\wedge T\ \le\ S\circ(R\wedge S^\circ\circ T).
\]

This is real extra algebra, not just “a category with converse and intersection.” \(\mathbf{Rel}\), with inclusion as order and intersection as meet, is the motivating example. When physical laws are implicit constraints, allegories support useful equational/inequational reasoning. They do not by themselves make constraint-solving executable. [Definition and modular law](https://ncatlab.org/nlab/show/allegory).

## Kleisli categories and typed effects

For a monad \(T\) on a suitable base category, Kleisli arrows \(X\to Y\) are base arrows \(X\to T(Y)\). Specific monads give different effects: powerset for nondeterminism; finite distributions for discrete probability; a subprobability construction for termination/mass loss; exceptions for typed errors; writer monads for accumulated monoid-valued logs or costs. Continuous-state stochastic kernels need measurable structure, not the naive finite-distribution monad.

The phrase **“Kleisli bicategories of relations/probability”** in the transcript does not specify one construction. To be meaningful, it needs a base bicategory or equipment, the appropriate higher monad/extension, 2-cells, and compatible composition laws. It should remain a *reserve research candidate* rather than a fully defined theory.

## Effect combinations are not free

If a computation has both nondeterminism and probability, its semantic type and resolution order matter: probability over sets of outputs, sets of distributions, probabilistic choice before/after adversarial choice, and mixtures of these are inequivalent. Composing effects can require a distributive law or a bespoke monad; such a law may fail to exist.

Likewise, an arbitrary nondeterministic relation equipped with “restriction = identity on existential domain” violates a restriction axiom; see [08](08-restriction-categories.md). Do not impose restriction semantics on a Kleisli or relational category without checking the axioms.

## Quantaloids and weighted relations

A quantaloid has ordered homs admitting arbitrary joins, with composition preserving joins in each argument. Relations form an example. Weighted matrices and enriched categories can represent costs, similarities, or reachability under an appropriate quantale. **One must choose the order and semiring/quantale convention:** minimum-cost algebra is not automatically probability algebra, nor is a “value of a path” necessarily a physical law.

**Use when:** the observed phenomenon is an admissibility relation, constraint network, nondeterministic protocol, weighted route problem, or genuinely stochastic transition. The choice turns on which multiplicities, measures, and compositions must survive.

**Related notes:** [05](05-coalgebra-and-behavior.md), [08](08-restriction-categories.md), [19](19-exceptions-and-replanning.md).
