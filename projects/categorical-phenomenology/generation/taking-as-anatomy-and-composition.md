# Taking-as anatomy and composition

Status: exploratory comparison, `probe`; proposed generalizations are nonbinding. The local derivations are `derived`, with first-pass hand checks and executable checks of the exhibited finite examples. No general apprehension theory, minimal signature, or novelty result is established.

The lens and causal profiles have concrete realizations in [lens-and-causal-enrichments.md](lens-and-causal-enrichments.md), with kernel-checked laws and forgetful maps. That construction discharges their base-realization question in specified strict regimes; the remaining profiles and broader variants stay exploratory.

The governing project already makes laws optional layers over a weak base (I3), uses separation axioms to distinguish regimes rather than exclude weaker instances (D2), and anticipates additional capabilities. The examples below are candidate enrichment profiles within that program. They identify data and laws useful for particular operations; they do not show that the base must contain those features or that the current formulation cannot support them.

The comparison covers serial observation, interpretation of theories, intervention transport, bidirectional update, feedback, analogical correspondence, and joint realization. These are neither exhaustive kinds nor primitive mode tags. Their local calculations stand on their own assumptions. The linked lens/causal construction identifies their standard serial compositions with canonical re-grounding; no translation identifies every operation below with that product. Consequently, differences from that product are not counterexamples to its laws.

## What an enrichment must retain for its intended use

For a particular enriched regime and intended operation, a presentation is adequate if it retains distinctions needed to determine the outcomes of the combinations under consideration. Let \(a(r)\) be a proposed representation of a relationship \(r\), and let \(K[-]\) be an allowed continuation or assembly context. A necessary condition is that

\[
a(r)=a(r')\quad\Longrightarrow\quad
J(K[r])\simeq J(K[r'])
\]

for the judgment \(J\) relevant to that use. Here \(J\) may concern existence of a realization, the resulting reading, preserved claims, possible updates, or a discrepancy bound; \(\simeq\) must be fixed accordingly. The condition is a task-indexed retention test, not a definition that computes a smallest anatomy. A counterexample identifies information that must remain recoverable, possibly through a sufficient equivalent rather than a new primitive field.

Three questions must stay distinguishable: can a combination be expressed, does it have a realization, and does that realization preserve what this use requires? A channel can compose while losing a desired distinction. A system of feedback equations can be formed while having no solution. A theory translation can preserve truth at every translated model while failing to reflect all consequences. Collapsing these into one `Supported` predicate conceals what explains the result.

The setting and intended preservation law constrain the comparison. A declared taking-as can also be mistaken, unwarranted, or untested. Its content and provenance should therefore remain representable separately from the certificates that validate it. Unknown existence is distinct from a proved obstruction, and a proposed preservation law is distinct from an accepted one.

## Observation and information reduction

Take a finite state set \(S\), an observation \(a:S\to V\), and a query \(q:S\to O\). Exact availability of the query through the observation means that some \(\bar q:a(S)\to O\) satisfies \(q=\bar q\circ a\). Equivalently,

\[
a(s)=a(s')\Longrightarrow q(s)=q(s').
\]

The implication is necessary by applying \(\bar q\); it is sufficient because \(q\) then has a well-defined common value on each observation fibre. Working on \(a(S)\) deliberately omits arbitrary extrapolation to observations that never occur in this setting. If those values can become reachable later, that omission must be revisited.

For another observation \(b:V\to W\), the serial readout is \(b\circ a\), with ordinary associativity inherited from functions. Yet query recovery through \(a\) need not survive \(b\): identity observation on a bit preserves that bit, while a subsequent constant map loses it. The serial composite exists; its adequacy for this query fails. Exact recovery can survive precisely when the new identifications made by \(b\circ a\) respect \(q\).

This gives two operations with different judgments. Forward observation constructs \(b\circ a\). Re-grounding a fixed query asks whether \(q\) factors through it. The current workspace product principally addresses the latter. Treating it as all composition would erase the former distinction.

For stochastic observations, use the channel and experiment compatibility rather than a sampled value alone; the Blackwell example in [displayed-categories-comparison.md](displayed-categories-comparison.md) supplies absent and nonunique factorizations. A single observed token does not determine which questions would be recoverable on other allowed states. The retained anatomy therefore includes an observation mechanism or an adequate description of its fibres, a query class, and the domain over which the claim is made. None of these has to be a separately stored field if the others determine it.

This profile covers information availability under passive observation. It does not license interventions, propagate edits, or supply a joint distribution for multiple observers.

## Interpreting a theory

Taking a system as a model of a theory concerns the relation between statements and their interpretations. The institution tradition provides the relevant contrast: sentence translation and model translation run in opposite directions, with satisfaction required to agree. Goguen's [author exposition of institutions](https://cseweb.ucsd.edu/~goguen/projs/inst.html), §2, verifies that organizing principle [✓]. The profile below is deliberately smaller than a full institution; its explicitly typed equation fixes the directions, which are inconsistent in the exposition's displayed satisfaction formula.

Let \(T,U\) have sentence sets and model classes. Take

\[
t:\operatorname{Sen}(T)\to\operatorname{Sen}(U),\qquad
r:\operatorname{Mod}(U)\to\operatorname{Mod}(T),
\]

with the independently interpreted satisfaction law

\[
M\models_U t(\varphi)\quad\Longleftrightarrow\quad r(M)\models_T\varphi.
\]

For a second pair \(s:\operatorname{Sen}(U)\to\operatorname{Sen}(V)\), \(q:\operatorname{Mod}(V)\to\operatorname{Mod}(U)\), composition is \((s\circ t,r\circ q)\). The preservation proof is the chain

\[
N\models_V s(t(\varphi))
\Longleftrightarrow q(N)\models_U t(\varphi)
\Longleftrightarrow r(q(N))\models_T\varphi.
\]

The opposite variance is doing explanatory work: translating a sentence forward is tested by interpreting a model backward. The result follows from the actual satisfaction laws, not from declaring all compatible syntax maps to be good interpretations. Associativity of these composed maps follows from function associativity. Executable proof translation is an additional obligation; semantic preservation alone does not construct a procedure on proofs.

Preservation must also be distinguished from reflection of theory entailment. Let \(T\) be propositional logic with one proposition \(P\) and no additional axiom; let \(U\) add \(P\). Sentence translation is the identity, and reduct includes the \(P\)-true valuations among all valuations. Satisfaction agrees at every \(U\)-model. Nevertheless \(U\models P\) and \(T\not\models P\). The same syntax has acquired a narrower class of admissible models. If every \(T\)-model instead had a \(U\)-expansion with the required reduct, the displayed satisfaction equation would imply reflection of semantic consequences: apply the target consequence to an expansion of each source model.

Retain the translated vocabulary, interpretation of statements, admissible models or assumptions, and the direction and strength of the preservation claim. A syntax string or a generic occurrence of a theory inside another does not determine these. Empty target model classes also make universal satisfaction conditions vacuous; whether such inconsistency is excluded depends on the intended use and should be checked separately.

This is substitution and preservation of judgments, not merely transmission of observations. The example is semantic and propositional; richer logics, resource-sensitive proof use, and proof identity require additional structure.

## Causal representation and intervention

Observational agreement can fail to determine the behavior needed for acting on a representation. To isolate that issue, take deterministic response models

\[
R_M:U_M\times I_M\to S_M,\qquad
R_N:U_N\times I_N\to S_N,
\]

where \(U\) contains external contexts, \(I\) interventions, and \(S\) resulting states. A representation supplies state, context, and intervention maps \(\alpha,\beta,\omega\) with corresponding domains and codomains, and requires

\[
\alpha(R_M(u,i))=R_N(\beta(u),\omega(i))
\]

for the declared contexts and interventions. This compatibility equation is verified as part of Beckers–Halpern's treatment in [*Abstracting Causal Models*](https://www.cs.cornell.edu/info/people/halpern/papers/abstraction.pdf), Definition 3.7 [✓]. Their full abstraction definitions impose further conditions; those are not imported here.

Two such exact compatible triples compose componentwise. If the second triple is \((\alpha',\beta',\omega')\), substitution in the two equations gives the same law for \((\alpha'\circ\alpha,\beta'\circ\beta,\omega'\circ\omega)\). When intervention translation is partial, its composite domain contains exactly those permitted inputs for which both stages of intervention translation are defined, with the corresponding context and model assumptions also respected. Preservation on passive observations alone cannot discharge this calculation.

A finite obstruction makes the missing data visible. Let \(U\) be a fair bit and compare

\[
M_1:\ X=U,\ Y=X;
\qquad
M_2:\ X=U,\ Y=U.
\]

Both produce exactly the same passive observations \((0,0)\) and \((1,1)\), with the same probabilities. Under \(\operatorname{do}(X=0)\), \(M_1\) has \(Y=0\), whereas \(M_2\) keeps \(Y=U\). In context \(U=1\), their resulting states are \((0,0)\) and \((0,1)\). Thus identical observed distributions cannot stand in for an intervention-preserving relationship. This is a constructed causal-model counterexample, not an empirical causal inference from data.

Retain an intervention family, the map of interventions, context correspondence, and the response semantics that the commutation law tests. Choosing an intervention family is substantive: a representation can be adequate for passive prediction and inadequate for the intended action. This does not make prediction invalid; it blocks that stronger transfer.

## A view that can be edited

A view may also be an interface for changing its source. The total set-based lens profile has

\[
g:S\to V,\qquad p:S\times V\to S,
\]

with

\[
p(s,g(s))=s,\qquad g(p(s,v))=v.
\]

The two equations say that writing back the current view is inert and that an update establishes the requested view. For another such pair \((h,q):V\leftrightarrows W\), composition is

\[
g_{21}=h\circ g,\qquad
p_{21}(s,w)=p(s,q(g(s),w)).
\]

These laws and the composition pattern are verified in Foster et al., [*Combinators for Bi-Directional Tree Transformations*](https://www.cis.upenn.edu/~bcpierce/papers/newlenses-popl.pdf), §§3–4 [✓]; the present profile uses total functions. Substitution proves the two laws for the composite. For example, reading after updating gives \(h(g(p(s,q(g(s),w))))=h(q(g(s),w))=w\). Writing back its current view gives \(p(s,q(g(s),h(g(s))))=p(s,g(s))=s\).

The forward view does not determine the relationship. Let \(S=\{0,1\}^2\), \(V=\{0,1\}\), and \(g(a,b)=a\). Two update policies are

\[
p_0((a,b),a')=(a',b),\qquad
p_1((a,b),a')=(a',b\mathbin{\oplus}a\mathbin{\oplus}a'),
\]

where \(\oplus\) is XOR. Both satisfy the two laws, and both satisfy the stronger overwrite equation \(p(p(s,v),v')=p(s,v')\): for \(p_1\), the repeated middle bit cancels. Yet updating \((0,0)\) to view \(1\) gives \((1,0)\) through \(p_0\) and \((1,1)\) through \(p_1\). Their forward views agree on every source state. An observation-only representation of these relationships therefore loses a distinction a subsequent update immediately exposes.

The stronger overwrite law also has a meaningful boundary. Suppose a view update changes its visible value and appends a log entry only when that value changes. Writing back an unchanged view is inert, and reading after a write returns the new value. But \(0\to1\to0\) leaves two log entries, while directly writing \(0\) to \(0\) leaves none. Overwrite fails because history is retained. This does not invalidate the two other laws or the intended logging behavior; it identifies an extra assumption required by the overwrite judgment.

Retain both directions, residual source state, and the update policy or a sufficient equivalent. Residual state is therefore a candidate ingredient of an enrichment for editing; whether the present form/occurrence data can already represent it adequately remains open. This example concerns exact finite state updates, not concurrent edits or error-prone synchronization.

## Taking something as an interacting component

For a component embedded in an environment, composition may mean enforcing a wiring relation rather than applying one readout after another. Willems's [behavioral account of open and interconnected systems](https://homes.esat.kuleuven.be/~sistawww/smc/jwillems/Articles/JournalArticles/2007.1.pdf) treats interconnection through shared variables and distinguishes manifest behavior from latent-variable realizations [✓]. The following scalar example is a local derivation, not a model of a particular physical installation.

Let two memoryless components have dimensionless scalar equations

\[
y=a u+r,\qquad u=k y.
\]

Each individually specifies a total function for its input. Wiring them into a loop produces

\[
(1-ak)y=r.
\]

There is a unique solution when \(ak\ne1\), no solution when \(ak=1,r\ne0\), and infinitely many when \(ak=1,r=0\). The failure is explained by their joint equations and feedback wiring, although neither component separately failed. As a relational operation, forming the conjunction is always defined; the resulting behavior may be empty or nonfunctional. Calling the loop a deterministic executable component requires the stronger existence-and-uniqueness judgment.

Time structure changes the result. The delayed equations \(y_{t+1}=a u_t+r_t\), \(u_t=k y_t\) determine a unique trajectory recursively from \(y_0\) and an input sequence, even when \(ak=1\). For zero input, \(y_t=(ak)^t y_0\), so existence, uniqueness, and asymptotic decay are distinct questions. A static observation map that forgets the delay cannot distinguish the two well-posedness problems.

Control also makes the order of choices material. For bits \(u,w\) and a requirement \(u=w\), \(\forall w\,\exists u\) holds, while \(\exists u\,\forall w\) does not. If \(u\) is chosen before \(w\) is observed, the former statement does not supply an implementable policy. The same set of permitted pairs yields different guarantees under different information and choice structures.

Retain ports and their sharing, latent state, delay or causal order, and who can choose what with which information. This comparison provides a bridge to [system-and-interaction-doctrines/interaction-kernel.md](system-and-interaction-doctrines/interaction-kernel.md): both distinguish a joint law from its realization and effect. It does not verify that strand's general mixed-law criterion. A part's role in such a joint law need not be a passive form occurring in a host; the relevant semantic object may be a family of compatible trajectories.

## Analogical correspondence

In an analogy, a domain is taken as another through selected relational organization. Gentner's [structure-mapping account](https://groups.psych.northwestern.edu/gentner/papers/Gentner83.2b.pdf), pp. 157–159, explicitly distinguishes object correspondences from the relational structure selected for transfer [✓]. Its psychological claims are not adopted here. The following is an exact relational skeleton for testing the anatomy of a declared analogy.

A correspondence from \(A\) to \(B\) carries a partial object map \(f\), a selected vocabulary \(\mathcal P_f\), and a predicate translation \(\theta_f\), with preservation claims for the selected relations and tuples. A second correspondence \((g,\theta_g)\) from \(B\) to \(C\) can transmit a predicate \(P\) only where the object maps are defined and \(\theta_f(P)\) belongs to the second map's selected vocabulary. The resulting vocabulary is therefore restricted to

\[
\{P\in\mathcal P_f\mid\theta_f(P)\in\mathcal P_g\},
\]

with translated predicate \(\theta_g(\theta_f(P))\). Atomic preservation on that restricted domain follows by applying the two preservation claims. It does not follow for arbitrary statements suggested by the analogy, or for relations discarded by either stage.

For an explicit obstruction, take three two-object structures. Let \(A\) have \(P=\{(0,1)\}\); let \(B\) have \(R=\{(0,1)\}\) and \(S=\{(1,0)\}\); let \(C\) have \(Q=\{(1,0)\}\). The identity object map \(A\to B\) preserves \(P\mapsto R\). The identity object map \(B\to C\) preserves \(S\mapsto Q\). Their object maps compose, but no translation of \(R\) was supplied in the second stage. Inferring \(P\mapsto Q\) would be false on \((0,1)\). This finite example isolates predicate alignment; it omits the cognitive selection, defeasibility, and relevance judgments of actual analogy.

The familiar statement that analogy is nontransitive should therefore be sharpened. Particular compatible relational maps compose; unqualified pairwise analogical aptness does not supply the matched domains, predicate translations, or warranted target claims needed for that construction. The failure can be a change of which structure in the middle domain is being used, even when the middle object and its object-level correspondence are unchanged.

Retain the selected substructure, semantic role alignment, intended inference family, and evidential status of projected claims. “Same form in the middle” is insufficient unless it determines these. Unsupported extrapolation should remain expressible as a proposed reading rather than be silently certified by the existence of a structural map.

## Joint readings and contextual assembly

An atlas also combines several local readings at once. Here the operation is a joint realization over overlaps, not a serial chain. Abramsky–Brandenburger's [sheaf treatment of contextuality](https://arxiv.org/pdf/1102.0264), §§2.5 and 4, supplies a verified setting in which locally compatible distributions need not possess a global realization [✓]. The following is an abstract finite compatibility example; no quantum implementation or empirical social interpretation is claimed.

Let \(x,y,z\) be bits. Local contexts permit

\[
R_{xy}:x=y,\qquad R_{yz}:y=z,\qquad R_{xz}:x\ne z.
\]

Each relation has two allowed assignments, and all its one-variable projections are \(\{0,1\}\). Assigning uniform probability to each local relation also gives matching uniform marginals on overlaps. Every pair of the three constraints has a simultaneous realization, but all three do not: the first two imply \(x=z\), contradicting the third. Hence there is no joint distribution with these three local distributions either, since any supported global assignment would have to satisfy all three constraints.

The matched local data here are sets of possibilities or distributions, not a chosen family of individual assignments agreeing on overlaps. For individual assignments, agreement on shared variables does permit their union. The distinction is essential: the example does not refute the sheaf property for ordinary assignments.

Combination can also create useful information absent from every member. For independent fair bits \(u,v\), let \(z=u\oplus v\). Either bit alone is independent of \(z\); together they determine it. A serial data-processing restriction cannot be applied to this parallel fusion as though it were another lossy step along one chain. Its additional information comes from the joint input.

Retain overlap identifications, shared-variable meaning, joint dependencies or coupling, and the distinction between chosen realizations and sets of alternatives. Pairwise binary support does not determine a global assembly verdict. Binary operations can implement a global constraint calculation if their intermediate objects retain the relevant correlations and interfaces; the counterexample rules out discarding those dependencies, not binary syntax itself.

## Candidate enrichment obligations

The following rows are consequences of exhibited separating cases, not a universal record schema. A field can be replaced by any construction that recovers the required distinction. The common criterion is preservation of the continuation judgments stated above.

| Information that must remain recoverable in the indicated regime | Separating continuation | Consequence of forgetting it |
| --- | --- | --- |
| The query class and admissible source variation | Identity observation followed by a constant observation | A defined composite is mistaken for an adequate one |
| Sentence/model variance, assumptions, and preservation versus reflection | Identity syntax interpreted with an additional axiom | Target consequences are imported without their premises |
| Intervention translation and response semantics | Passive-equivalent causal models under `do(X=0)` | Predictive fit is mistaken for intervention validity |
| Residual state and update behavior | Equal views with the two XOR-based update policies | The same representation is assumed to imply the same action |
| Wiring, delay, and order of choices | Scalar feedback and the bit-choice quantifiers | Local functionality or existential feasibility is mistaken for a realizable guarantee |
| Predicate and role alignment | The `P→R`, `S→Q` correspondence chain | Matching endpoints conceal a change of semantic relationship |
| Joint constraints and shared-variable dependencies | Three pairwise feasible binary contexts | Local compatibility is mistaken for a global reading |

These are requirements for the indicated enriched regimes and operations. They are not objections to a weak base or a finite minimal list for every taking-as relationship. They also do not show that any of the distinctions is unencodable in `Str`, `Closure`, or `OccursIn`; those types are too unconstrained for such an argument. The issue is which distinctions the formulation makes available to its operations and which guarantees it derives from them. Encoding an update policy inside a form is useful only if composition can recover and use that policy lawfully.

Grading supplies another cross-cutting test. Suppose \(f,\widehat f:X\to Y\) differ by at most \(\varepsilon\), \(g,\widehat g:Y\to Z\) differ by at most \(\delta\), and \(g\) is \(K\)-Lipschitz on the relevant metric domain. The triangle inequality gives

\[
d_Z(g(f(x)),\widehat g(\widehat f(x)))\le K\varepsilon+\delta.
\]

An unconditional additive bound would forget downstream sensitivity. With \(f(0)=0\), \(\widehat f(0)=1/10\), and \(g(y)=\widehat g(y)=10y\), the composite error is \(1\), not \(1/10\). Thus a grade algebra must be derived from transported discrepancies and their amplification, domains, and units. A witness type alone supplies no universal quantitative composition law. This is a mathematical error-propagation example, not an empirical calibration claim.

## A possible common construction, with its limit exposed

The cases suggest a research direction: present the interfaces of a relationship together with the realizations and warranted judgments that connect them. A requested assembly supplies matching and wiring data. Its realization space then carries the compatible internal witnesses, and any compressed output comes with a declared account of what it forgets.

For proof-relevant relations \(R(x,y)\), \(S(y,z)\), \(T(z,w)\), a serial realization has the type

\[
\sum_{y,z}R(x,y)\times S(y,z)\times T(z,w).
\]

Both parenthesizations of dependent-sum composition reassociate to this type. This explains associativity of that assembly operation: the same internal variables and witnesses satisfy the same constraints. It is not a proof that every apprehension product has this semantics. A total function, a nonblocking process, a conservative interpretation, and a coherent family of local readings each impose additional conditions on the resulting witness space. The assembly can exist as a relation while leaving one of those classes.

More complex cases make the limits explicit. Lens composition retains the old state and runs update operations in a specified order. Causal transport must preserve intervention equations. A control guarantee quantifies over an available policy before unknown disturbances; a bare existential joint solution does not do so. Resource-sensitive operations cannot duplicate a shared witness merely because products permit duplication. These obligations have to come from the relationship's independently specified semantics, not from a generic compatibility oracle.

These constructions are possible resources for enriched apprehension regimes. Their comparison does not establish that a family of local presentations is superior to the existing base with suitable added data and laws. That judgment requires actual realizations and translations, including an account of which operation in an enrichment corresponds to apprehension composition and which operations are additional capabilities.

## What the comparison establishes and leaves open

The local examples distinguish requirements of different enriched regimes. They do not establish that R-C1 or R-C2 should change. Content invariance is a stated law of the current re-grounding product; the fact that an edit changes a view is not a counterexample unless the edit has first been shown to instantiate that product while preserving the relevant interpretation of content. No such identification is supplied here. An enrichment may add update, feedback, or fusion operations alongside re-grounding.

Adding laws is part of the intended explanation, not a defect to eliminate. The useful question is which independently meaningful assumptions yield which consequences. A primitive support relation together with axioms may be entirely appropriate. Merely assigning the desired verdict to that relation does not explain the verdict, but this narrower objection does not apply to introducing and studying a law package.

The results have different strengths. The observation criterion and finite obstructions directly determine success or failure in their settings. Interpretation and causal composition are closure results conditional on each leg satisfying its semantic preservation law. Lens composition likewise assumes local round-trip laws. These are legitimate conditional results. The linked lens/causal construction realizes those two regimes over the base; corresponding constructions for the other profiles remain open. The examples alone neither vindicate nor refute Closure/OccursIn.

**Reserve.** Institutional recognition that constitutes a status, normative authority and delegation, intentional aboutness, and changes that constitute their own relata have not been modeled here. The examples do not license collapsing these to causal responses or logical truth. A recognition relationship may change who may act, rather than merely describe what is true; a future comparison must test authority and scope, with an explicit source for its normative law. Reflection and carrier revision may require more than the fixed interfaces used above. These are live limits of the proposed organization, not evidence for any particular extra primitive.

## Follow-up questions with a discriminating use

The nearest useful test of an enrichment intended to cover these uses is whether it distinguishes the two lenses with identical `get`, and the two causal models with identical passive observations, while deriving the relevant update or intervention judgments. Failure exposes a missing action or counterfactual distinction in that enrichment, not necessarily in the base. Success establishes adequacy for those particular continuations, not an entire theory.

A second test is whether it can express the three-context obstruction without adding a manually asserted global `Supported` answer. Retaining the local supports and their shared variables suffices to derive the contradiction; a representation storing only pairwise pass/fail verdicts does not. This discriminates direct computation of compatibility from merely relocating the answer into a field.

An atlas construction should then combine different profiles through an explicit bridge. For example, a causal response model can supply an observational channel, but the reverse inference fails in the exhibited causal pair. A lens exposes a readout, but its readout does not determine its update policy. These are useful forgetful maps with demonstrated losses; demanding reversible equivalences would erase the very distinctions under investigation. No new universal formalism is required to test these bridges.

## Verification and source boundary

The exact examples and hand derivations are local results under their stated assumptions. [taking-as-anatomy-checks.py](taking-as-anatomy-checks.py) checks the observation obstruction, nonconservative model inclusion, causal pair, two view/update policies and their compositions, logging counterexample, scalar feedback cases and quantifier distinction, predicate-matching obstruction, joint-context contradiction, XOR information example, and amplification counterexample. Its 112 lens-law instances and finite enumerations do not substitute for general proofs or independent verification.

Primary-source checks for this comparison covered the institution exposition's variance principle; lens laws and sequential composition; the causal compatibility equation and its intervention indexing; Gentner's selected relational mappings; Willems's interconnection and latent-variable distinction; and compatible local distributions versus global realization in Abramsky–Brandenburger. Source definitions and the constructions developed here are distinguished above. The linked lens/causal construction now supplies mechanized proofs and explicit base realizations for its stated regimes; the remaining profiles have only the local checks described here. No comprehensive literature or novelty search, empirical validation of analogy, or audit of every inherited claim was performed. Independent review remains open.
