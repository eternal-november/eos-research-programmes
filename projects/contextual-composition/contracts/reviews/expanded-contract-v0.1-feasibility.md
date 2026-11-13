# Expanded contract v0.1: feasibility review

> Review of the early contract proposal, not a current completion assessment or an adopted amendment. Its recommendations and unresolved-status language apply to the proposal being evaluated; consult the integrated treatment for subsequent results.

# Evaluation: Expanded Research Contract v0.1

Conditional approval for scoping only

Overall judgment: The document is a technically serious research specification with unusually explicit proof obligations, scope controls, and safeguards against false completion. Its central weakness is not mathematical incoherence. It is that the mandatory programme commits to a substantial conjunction of results whose joint attainability has not yet been established.

The contract is suitable as a proposal for a scoped feasibility investigation (O0/G1). It is not yet suitable as a frozen commitment to deliver O1–O8.

Three distinctions govern this assessment:

- Specification quality: High. The document generally distinguishes inherited results, conjectural extensions, structural hypotheses, semantic obligations, and acceptance conditions.
- Mathematical feasibility: Unresolved. The main positive compatibility theorem, its two contrasting instantiations, and the semantic integration are precisely the results that must be discovered.
- Research management: Good change control, but insufficient separation between a successful research investigation and a successful proof of the originally desired theorem package.

The review below evaluates the uploaded 867-line LaTeX source, with selected comparisons against the referenced inherited manuscript and relevant published categorical-probability literature. It does not certify the inherited proofs or establish that the proposed new theorems exist.

## 1. What the contract gets right

### It identifies the actual missing mathematical result

O1 (lines 299–349) correctly distinguishes the following problems:

\\[ \text{Given a coherent interaction, construct the composite} \\]

and

\\[ \text{Given independent input structures, derive a coherent interaction.} \\]

The first is conditional algebraic construction. The second is the genuine compatibility problem.

The inherited manuscript already presents a mixed-composition theorem conditional on a pseudodistributive law, plus an explicit probability/list instance. The contract does not misrepresent those as a general existence theorem.&#x20;

One_relative_construction_for_context_content_and_effects.tex



The refusal to accept a lifting that merely repackages the desired law is especially important. Classical pseudodistributive-law theory contains equivalences among law data, liftings, and compatible structures. Those equivalences are valuable, but they do not automatically provide independent, easily verified existence criteria.&#x20;

[image](https://www.google.com/s2/favicons?domain=https://studylib.net\&sz=32)

Studylib



### It preserves mathematically significant distinctions

The requirements concerning noninvertible grade maps, changing-endpoint squares, pure-middle balance, and full coherence are appropriate to the inherited construction.

In particular, a theorem about objects of \\(H(A,B)\\) does not automatically establish a theorem about the category \\(H(A,B)\\). A formula for composing representatives can fail to descend through the pseudocoend even when the formula appears associative.

The contract correctly treats that descent as a separate proof obligation.

Its distinctions among structural equivalence, observational equivalence, local reflection, and lax forgetting are also necessary. The representation-comparison component would be materially weaker without them.

### The language requirements confront real semantic problems

O4–O5 contain several substantive constraints: latent witnesses cannot automatically be inspected; predicted transitions do not confer execution capabilities; randomness may be reused or freshly generated; and compensation is not assumed to invert execution.

These are not decorative distinctions. Each can change contextual equivalence.

The higher-order discriminator is particularly useful because it exposes a failure that ordinary input/output semantics can conceal. The contract also correctly refuses to infer full abstraction from contextual soundness.

Assessment: These aspects should be retained in essentially their present form.

## 2. Principal weakness: the contract specifies desired discoveries as guaranteed deliverables

O1 requires a noncircular positive compatibility theorem, bounded recognition or necessity, and applicability to contrasting families. O2 adds compatible strength and representation invariance. O3–O5 add multiple interpretations, higher-order behavior, and contextual soundness. O7 requires a connected new obstruction with a proved positive repair.

This is not merely an extensive list of proof tasks.

The central propositions are currently unknown, and several depend on one another. It remains possible that the appropriate general compatibility criterion excludes one proposed application, that the desired two-model comparison requires a different ambient, or that retaining the required cells conflicts with the strongest observational quotient.

The contract acknowledges these possibilities. Its pause and rescope rules are reasonable. Nevertheless, the acceptance structure treats an unsuccessful positive theorem search as incomplete, even if the research discovers a decisive structural obstruction.

That creates two distinct completion notions that should not be merged.

Research closure means that the authorized investigation has produced a defensible result: an established positive theorem, a verified obstruction, or an explicitly bounded unresolved problem with the remaining obligations identified.

Target achievement means that every mandatory mathematical result in O1–O8 has been proved at the frozen scope.

A research investigation can reach legitimate closure without achieving its initially conjectured target. Conversely, a dossier that merely catalogues failed attempts has not necessarily reached research closure.

The present contract correctly prevents negative results from being passed off as positive results, but it does not sufficiently distinguish these two statuses.

Required revision: Establish separate research-closure and target-achievement criteria. Retain full O1–O8 acceptance for the latter, but do not make successful mathematical research definitionally dependent on the truth of its original conjectures.

## 3. The O1 generality requirement needs a stronger nonvacuity test

The central displayed theorem is still schematic:

\\[ D\in\mathcal S,\quad P_1(D),\ldots,P_r(D) \quad\Longrightarrow\quad \tau_D:N_D\odot_C M_D\Rightarrow M_D\odot_C N_D. \\]

That is appropriate in a proposal. However, the choice of \\(\mathcal S\\) and \\(P_i\\) largely determines whether the eventual theorem is significant.

There are two potential loopholes.

First, structural generality can be manufactured through disjoint cases. A criterion could encompass the probability example and a capability example by explicitly encoding two unrelated constructions as separate admissible cases. Both applications would technically instantiate one theorem, without revealing a common compatibility mechanism.

The document's demand for one connected construction discourages this, but does not decisively exclude it.

A meaningful criterion should derive the crossings from a common structural operation, universal property, or compositional principle. The existence of multiple instances is not itself evidence of such a mechanism.

Second, the required increment beyond the inherited result is not indexed finely enough.

The inherited probability/list example has nontrivial context-grade categories but terminal content-grade fibres, with \\(d_B(\*)=\operatorname{List}B\\).&#x20;

One_relative_construction_for_context_content_and_effects.tex



A theorem generalizing that example to another content monad or larger context spaces could be genuinely useful. But it would not necessarily establish compatibility for independently varying nonthin context and content grades.

The contract explicitly makes arbitrary two-sided nonthin content optional. That is a defensible scope choice, but its significance must be understood.

G1 should therefore freeze whether the intended contribution is a structural family of contextads interacting with fixed content effects, or a criterion genuinely accommodating two independently graded sides. Either can be substantive; they are different research achievements.

The nonvacuity test should also require a common construction of \\(\tau_D\\), not merely a theorem whose input class is a union of individually solved families.

## 4. The categorical-to-semantic bridge is under-specified

This is a technical issue of direct relevance to O2–O3.

The structural core retains categories \\(H(A,B)\\) with potentially nonidentity, noninvertible morphisms. An ordinary Markov category, viewed as a locally discrete bicategory, does not carry comparable nontrivial 2-cells.

If an interpretation sends the realized bicategory \\(B_H\\) directly into that locally discrete target, any source 2-cell

\\[ \alpha:h\Rightarrow h' \\]

can be interpreted only when the corresponding target 1-cells are equal, since a locally discrete category has only identity 2-cells.

It follows that such an interpretation must collapse all distinctions witnessed by its mapped 2-cells. It cannot retain those cells faithfully.

This is not a proof that QBS-based stochastic semantics is unsuitable. It identifies a missing decision about the type of semantic interpretation.

The possibilities include a categorified stochastic target retaining grade morphisms, a decorated or indexed interpretation whose underlying Markov category is only one component, or an explicitly information-forgetting comparison into ordinary kernels.

The contract permits information loss, but O3 needs to classify which of these structures is actually being requested. Otherwise a model may be described as an interpretation of the full relative construction when it only interprets a one-dimensional observational shadow.

The same issue affects O5. If a noninvertible structural cell is interpreted as kernel equality, the resulting semantic judgment is not automatically the intended contextual refinement order.

Required revision: Freeze a distinction between full structural interpretations and observational-shadow interpretations, including the precise cell-loss obligations for the latter.

## 5. The QBS benchmark omits a known, relevant obstruction

The document correctly declines to assume that all deterministic QBS-based Markov morphisms arise from the selected pure embedding. It also correctly avoids assuming disintegration or arbitrary random-function reification.

One further distinction deserves explicit inclusion.

The Markov category associated with the usual quasi-Borel probability monad is not positive in the categorical sense. Fritz, Gonda, Houghton-Larsen, Lorenzin, Perrone, and Stein demonstrate this failure and relate it to information hiding through probabilistic name generation.&#x20;

[image](https://www.google.com/s2/favicons?domain=https://www.cambridge.org\&sz=32)

Cambridge Core



This does not mean that QBS probabilities have negative numerical weights. Categorical positivity is an additional information-flow property, not merely numerical nonnegativity.

The distinction matters because the proposed programme explicitly concerns hidden witnesses, observations, changing resources, and preservation of information under representation changes.

The QBS benchmark should therefore test whether its intended observational and refinement arguments require categorical positivity, causality, or related information-flow properties. A theorem valid for standard Borel kernels need not transport unrestrictedly to QBStoch.

Restricting the admitted QBS fragment may solve a particular problem, but that restriction must then be tested against the higher-order features that motivated QBS in the first place.

This is a specific existing boundary, not a speculative concern.

## 6. A missing invariant: what makes the programme about world models?

The title and purpose promise a mathematical account of open world-modeling computations. O4 distinguishes models of transitions, evidence, capabilities, and actual execution.

But the mandatory requirements do not clearly force an explicit model representation and model-revision operation.

A system could conceivably satisfy the core by providing an effectful indexed language with observations, callbacks, and resources, yet never represent an uncertain model of its environment or revise that model in response to evidence.

That would be an interesting open-effect calculus. It would not establish everything suggested by the term world-modeling.

A possible minimum is a typed interface separating a model of available transitions, an observation produced by an interaction, and a bounded revision of admissible models under that observation.

This need not be Bayesian conditioning. A deterministic evidence-filtering operation could serve the nonstochastic application, while probabilistic model revision could be a separately justified extension.

The essential obligation is that evidence changes an explicitly represented model state or its justified predictions, rather than only changing the next executable resource.

There are two legitimate choices: add this bounded model-revision requirement, or narrow the advertised subject to open dependent computation with observations and capabilities.

Neither choice requires the optional general feedback, recursion, or epistemic-logic programmes.

## 7. A concrete discriminator that should be frozen at G1

The higher-order comparison admits an elementary test that exposes real information loss.

Let \\(A=B=\\{0,1\\}\\). Consider two distributions on functions \\(A\to B\\).

The first chooses, with equal probability, between the constant-zero and constant-one functions. The second chooses, with equal probability, between the identity and Boolean-negation functions.

For every individual input \\(a\\), both induce the same kernel:

\\[ k(a)=\operatorname{Bernoulli}(1/2). \\]

But under a client that retains one sampled function and evaluates it at both inputs:

\\[ \begin{aligned} \Pr\_{\mathrm{constant}}\bigl(F(0)=F(1)\bigr)&=1,\\\ \Pr\_{\mathrm{identity/negation}}\bigl(F(0)=F(1)\bigr)&=0. \end{aligned} \\]

This is an exact counterexample to the injectivity of the map from distributions on functions to their pointwise output kernels.

It establishes that a representation discarding cross-call correlations cannot support equivalence under all repeated-query contexts. A suitably state-augmented kernel model may recover the joint behavior, but that is a different interface and must be compared as such.

The contract anticipates this distinction conceptually. Freezing an explicit witness would convert it into a testable obligation for O3–O5.

A second early discriminator should exercise dependent interface change: one result branch grants a resource unavailable in the other, followed by a noninvertible grade or base map. The crossing must respect the associated pure-middle balance and native cells. This test should precede any large semantic integration.

Together, these would test different obstructions: structural descent versus observational information loss.

## 8. Two further acceptance risks

Resource-sensitive strength, O2. The proposed frame action

\\[ \operatorname{st}\_X:H(A,B)\to H(X\otimes A,X\otimes B) \\]

is reasonable as a schematic target, but it may require freshness, resource separation, equivariance, or other frame conditions that differ significantly between probability and deployment semantics. The G1 specification must identify the allowable \\(X\\) and prove that framing does not introduce invalid copying or resource interference. This is more than checking associativity of the displayed action.

Obstruction and repair, O7. The present acceptance clause could arguably be satisfied by dropping a hypothesis, proving failure, and reinstating the original hypothesis to recover the positive theorem. That would establish a boundary but might contribute little new understanding. A stronger O7 should require a minimally informative necessity result or a repair with demonstrably different expressive or preservation properties—not merely restoration of every original assumption.

Neither problem requires abandoning O2 or O7. Both require sharper acceptance tests.

## 9. Recommended revision to the programme structure

The existing stages are serviceable, but the initial gate should be a genuine feasibility gate rather than only a charter-freezing exercise.

The most useful revision is to make G1 deliver a conditional theorem specification and a small set of deliberately difficult structural examples, then have G2 demonstrate that one common positive mechanism survives those examples before committing to the full semantic package.

In particular, G1 should establish an explicit choice of generality for O1, a declared structural-versus-observational interpretation interface, an identified model-revision obligation if world modeling remains the goal, and a fixed set of distinguishing contexts for repeated randomness and capability changes.

O3–O5 could then develop against an actual positive family rather than a conjectured interface. The language's syntax may still be specified in O0, as the contract sensibly requires.

The default application pair—adaptive sensing and typed capability allocation—should be retained as a feasibility pair, not yet certified as a pair of instances of one theorem. Their contrasting mechanisms provide a useful test of whether the proposed abstraction is genuine.

If the common theorem succeeds for only one family, that is evidence about the generality of the abstraction, not justification for disguising two mechanisms as one.

## 10. Final assessment

| Dimension                                   | Assessment                            |
| ------------------------------------------- | ------------------------------------- |
| Mathematical problem formulation            | Strong                                |
| Attention to cells, typing, and coherence   | Strong                                |
| Distinction between inherited and new work  | Strong, subject to source audit       |
| Nonvacuity of proposed generality           | Needs tighter criteria                |
| Structural/semantic interface specification | Incomplete                            |
| World-modeling-specific semantics           | Under-specified                       |
| Feasibility of mandatory conjunction        | Unestablished                         |
| Scope and change governance                 | Strong, with completion-status defect |

The main research direction is worth retaining. The contract has identified a substantive gap between possessing a coherent mixed law and deriving that law from independent structural data, and it has chosen meaningful semantic tests of that gap.

However, three changes are prerequisites for freezing the full programme.

The generality target must be made nonvacuous. A common theorem should reflect a common mechanism, with the intended extent of genuinely two-sided grading settled explicitly.

The semantic bridge must be typed more precisely. A category-valued structure and an ordinary Markov category cannot be identified without accounting for what happens to the former's nontrivial cells.

The intended scientific outcome must be separated from the outcome of the research investigation. Unknown existence theorems cannot be made true by contractual acceptance conditions.

The QBS positivity boundary and the missing model-revision requirement should also be addressed at G1, since each could materially change the choice of semantic target.

Decision: Approve the document as the basis for O0 and a strengthened G1 feasibility audit. Do not yet adopt O1–O8 as an unconditional deliverable package. The appropriate next commitment is to determine whether the proposed common compatibility mechanism survives the two contrasting applications and the specified information-loss tests.