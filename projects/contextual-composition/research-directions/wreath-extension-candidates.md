# Candidate extensions of contextads as wreaths

> Status: exploratory proposals and candidate arguments. Literature attributions and proposed constructions have not been independently re-audited here. This note does not establish completion of the programme or amend its contract.

Discussion of [Contextads as Wreaths](https://arxiv.org/abs/2410.21889). The associated applications overview is [Constructions, enrichments and applications](constructions-enrichments-and-applications.md).

The paper, Contextads as Wreaths; Kleisli, Para, and Span Constructions as Wreath Products by Matteo Capucci and David Jaz Myers, has a particularly extensible feature: it turns constructions that previously looked unrelated into instances of one higher-categorical operation, the wreath product.

That suggests two different research directions\:

1. Internal enrichment\: Add algebraic, logical, differential, probabilistic, or computational structure to contextads and investigate what survives the $\mathrm{Ctx}$ construction.
2. External generalization\: Change the ambient tricategory or the kind of wreath being formed, allowing constructions that cannot be represented by ordinary contextads at all.

The second is more ambitious. The first has a more direct route to theorems.

There is an important qualification about originality. Section 8 already proposes mixed contextad-contentad distributive laws, reconstruction via factorization systems, and higher wreath products accommodating general monoidal 2-categorical actions. Those are substantial open directions identified by the authors, not extensions to attribute to a new proposal.

## 1\. The interface that has to be preserved

In the paper's Definition 3.15, a contextad is roughly a fibred colax action

$$
\mathcal C \xleftarrow{p}\mathcal M
\xrightarrow{\odot}\mathcal C
$$

where $p$ is a suitable displayed fibration. Each object $A$ has a category $\mathcal M_A$ of permissible contexts, and a context $P\in\mathcal M_A$ gives an extension $A\odot P$\.

There are also units $I_A$, dependent context combination $P\otimes Q$, and comparison maps

$$
\varepsilon_A:A\odot I_A\to A,
$$

$$
\delta_{A,P,Q}:
A\odot(P\otimes Q)\longrightarrow
(A\odot P)\odot Q.
$$

The associativity and unit coherence, as well as compatibility with reindexing, are essential. In particular, $Q$ lives over $A\odot P$, not necessarily over $A$\. This dependency is what distinguishes contextads from ordinary graded comonads.

A horizontal arrow in $\mathrm{Ctx}(\odot)$ then has the form

$$
(P,f):A\rightsquigarrow B,\qquad
f:A\odot P\to B.
$$

Composition reindexes the second context along $f$, combines it with the first, and uses $\delta$ to interpret the combined context. The resulting structure is a double category, retaining pure maps, contextful maps, and squares that relate them.

The critical constraint for any proposed extension\: its operations must be compatible with dependent reindexing and horizontal composition, not merely well-defined on individual contextful arrows.

That constraint will separate the plausible extensions from decorative additions.

## 2\. First target: stochastic and probabilistic contextads

Priority: very high · Feasibility: high in finite settings · Extends a direction suggested in §8

This is one of the first constructions worth actually attempting, because there is a fairly concrete model and an exact comparison theorem to pursue.

### A finite stochastic contextad

Take $\mathcal C=\mathbf{FinSet}$\. Let a context over $X$ be a family of finite probability spaces

$$
P=((E_x,\mu_x))_{x\in X}.
$$

A morphism of contexts is a family of measure-preserving functions. Reindexing along $h:X'\to X$ is ordinary substitution, $h^*P=(E_{h(x')},\mu_{h(x')})$\.

Define context extension by dependent sum\:

$$
X\odot P=\sum_{x\in X}E_x.
$$

Now suppose $Q$ is a context over $X\odot P$, with fibres $(F_{x,e},\nu_{x,e})$\. Define context composition by

$$
\begin{aligned}
(P\otimes Q)_x
&=\sum_{e\in E_x}F_{x,e},\\
(\mu\otimes\nu)_x(e,z)
&=\mu_x(e)\nu_{x,e}(z).
\end{aligned}
$$

The unit is the singleton probability space, and the comparison

$$
X\odot(P\otimes Q)
\cong
(X\odot P)\odot Q
$$

is the evident reassociation of dependent sums.

Here the contextad laws follow from the associativity of dependent sums and multiplication of probabilities; cartesian reindexing is inherited from substitution. This gives a concrete strong contextad, subject to the standard categorical bookkeeping.

A contextful arrow is precisely a randomized algorithm with explicit randomness\:

$$
(P,f):X\rightsquigarrow Y,\qquad
f:\sum_xE_x\to Y.
$$

Its observable behavior is the stochastic kernel

$$
K_f(y\mid x)
=
\sum_{\substack{e\in E_x\\f(x,e)=y}}\mu_x(e).
$$

The significant payoff is that the contextful composition law becomes exactly stochastic-kernel composition after forgetting the random representation\:

$$
K_{g\circ f}(z\mid x)
=
\sum_yK_f(y\mid x)K_g(z\mid y).
$$

This follows by expanding the dependent joint distribution and rearranging finite sums.

There is an even stronger result to pursue: the connected components of the horizontal hom-categories of this $\mathrm{Ctx}$ should recover the hom-sets of $\mathbf{FinStoch}$\. Every finite kernel has a latent representation; conversely, two representations of the same kernel admit a common measure-preserving refinement, constructed by coupling their random variables conditionally on the common output. This gives a direct route to identifying the quotient, rather than merely asserting an analogy.

### Why this is worth doing

It creates three distinguishable mathematical levels\:

- Representation\: a chosen source of randomness and a deterministic program using it.
- Reparameterization\: a map relating two such implementations.
- Observation\: the induced Markov kernel, forgetting implementation details.

The double-categorical level retains information lost by the usual stochastic semantics. It distinguishes different implementations even when their output distributions agree.

The next extension would be conditioning and Bayesian inversion. However, inversion requires a prior, and at zero-probability events a posterior cannot be determined canonically. Thus Bayesian inversion cannot simply be declared a universally defined converse operation on contextful arrows. A prior-indexed, support-sensitive lens or optic is a more defensible target.

This links naturally to existing work on Dependent Bayesian Lenses\.

The paper itself constructs a probabilistic contentad example (§6.7) and suggests transposing such probability constructions into contextads (§8). The construction above makes that proposal explicit and supplies a concrete semantic quotient to test.

## 3\. Differential contextads and reverse-mode automatic differentiation

Priority: very high · Feasibility: moderate · Main obstacle: tangent structure versus reindexing

The paper already connects $\mathrm{Para}$ with machine learning, and reverse differentiation of parameterized lenses is established mathematics. The interesting extension would be to make differentiation compatible with genuinely dependent contexts, not merely ordinary parameter spaces.

Consider a smooth parameterized map

$$
f:A\times P\to B.
$$

Its tangent map has type

$$
Tf:TA\times TP\to TB,
$$

using the canonical identification $T(A\times P)\cong TA\times TP$\. The chain rule makes this compatible with parameterized composition.

For a general contextad, this lift is not automatic. If $h^*P$ is reindexing in the context fibration, the desired comparison is

$$
T(h^*P)\cong(Th)^*(TP).
$$

This is essentially a Beck-Chevalley requirement for differentiation: differentiation must commute with context substitution\.

There is a concrete obstruction in smooth geometry. Arbitrary pullbacks of smooth manifolds may not exist as manifolds, and even existing pullbacks need not be preserved by the tangent functor. One should restrict to a suitable display class, such as submersions, and prove stability there. The 2025 work Pullbacks in Tangent Categories and Tangent Display Maps provides directly relevant machinery.

Reverse differentiation adds another layer. For a smooth map $f:A\times P\to B$, the reverse derivative acts on cotangents\:

$$
R[f]:
(A\times P)\times B^*
\longrightarrow A^*\times P^*
$$

in a finite-dimensional vector-space setting, with the appropriate point-dependent cotangent interpretation on manifolds.

The input cotangent, parameter cotangent, and their reindexing laws must be tracked separately. A lens-like or optic-like construction should encode this backward information; an ordinary contextful arrow does not.

Proposed target\: a differential $\mathrm{Ctx}$ construction that retains not only parameterized evaluation but also tangent and cotangent transport through changing dependent contexts.

This could support differentiable partial maps, constrained optimization, variable-dimensional parameter spaces, and differentiation of compositional systems whose allowable parameters depend on intermediate states.

It also connects to the existing categorical foundations of gradient-based learning, which already use $\mathrm{Para}$, lenses, and reverse derivatives. The added research question is whether this combination lifts from fixed parameter categories to arbitrary suitable context fibrations.

## 4\. Relations, corelations, and exact quotients of contextful arrows

Priority: high · Feasibility: high in regular or finitely cocomplete settings

The paper gets $\mathrm{Span}(\mathcal C)$ from $\mathrm{Ctx}$, and $\mathrm{Cospan}(\mathcal C)$ from the dual $\mathrm{Cnt}$ construction.

The natural next question is whether the respective quotients to relations and corelations can be integrated into the wreath-product machinery.

For a regular category $\mathcal C$, define

$$
\mathrm{Span}(\mathcal C)\longrightarrow
\mathrm{Rel}(\mathcal C)
$$

by sending a span

$$
A\xleftarrow{s}S\xrightarrow{t}B
$$

to the image subobject

$$
\operatorname{im}\langle s,t\rangle
\hookrightarrow A\times B.
$$

The image discards the number and identity of witnesses in $S$, retaining only whether a pair $(a,b)$ is related.

For sets, this says

$$
aRb\iff \exists s\in S:
s(s)=a,\quad t(s)=b,
$$

where the same symbol $s$ is being used conventionally for the source map and, separately, an element of the apex.

Composition survives the quotient because relational composition corresponds to pullback followed by existential image. Regularity supplies stable images, which are the relevant exactness condition.

The dual direction is to obtain corelations from cospans, using appropriate image factorizations and pushout stability. In finite sets, a corelation can be represented as an equivalence relation on the disjoint union of its interfaces, recording connectivity rather than the internal nodes of a chosen cospan.

There are two different possible results here. The immediately accessible one is a quotient of an existing $\mathrm{Ctx}$ or $\mathrm{Cnt}$ construction. The harder one would identify a doctrine of wreaths whose products are already relational or corelational, rather than producing spans or cospans first and quotienting afterward.

That distinction matters: the latter is genuinely a new universal construction.

An interesting companion problem is to characterize when $\mathrm{Ctx}(\odot)$ is a proarrow equipment, with both companions and conjoints for every tight arrow. The paper proves the existence of all companions (Theorem 4.24), but explicitly gives conjoints only for invertible tight maps. Full equipment structure therefore requires additional hypotheses.

This would put contextads closer to the machinery of tabulations, relational logic, and proarrow semantics. For comparison, Lambert's work characterizes double categories of relations using equipment and tabulation properties. [Double Categories of Relations](https://arxiv.org/abs/2107.07621)>

## 5\. Logical doctrines and predicate transformers

Priority: high · Feasibility: high for comprehension-style contexts; conditional in general

A further addition would be to attach an indexed logic to $\mathrm{Ctx}$, giving an interpretation not only of what contextful arrows do, but also of what they prove or guarantee\.

Take a predicate fibration $\mathrm{Pred}\to\mathcal C$\. For a contextful arrow

$$
(P,f):A\rightsquigarrow B
$$

and a postcondition $\varphi$ on $B$, first pull it back along $f$\:

$$
f^*\varphi\in\mathrm{Pred}(A\odot P).
$$

If context extension comes with a projection $\pi_P:A\odot P\to A$, quantify over its fibre\:

$$
\begin{aligned}
\mathrm{wp}_{\exists}(P,f)(\varphi)
&=\exists_{\pi_P}(f^*\varphi),\\
\mathrm{wp}_{\forall}(P,f)(\varphi)
&=\forall_{\pi_P}(f^*\varphi).
\end{aligned}
$$

These express different semantics: existential reachability versus universal satisfaction. For partial maps, they also make different assertions about computations whose domain of definition is empty.

For stochastic contexts, the corresponding quantitative predicate transformer is

$$
\mathrm{wp}_{(P,f)}(\varphi)(x)
=
\sum_{e\in E_x}\mu_x(e)\,\varphi(f(x,e)).
$$

The expected compositionality equation is

$$
\mathrm{wp}_{g\circ f}
=
\mathrm{wp}_f\circ\mathrm{wp}_g.
$$

In the finite stochastic model this follows from the same finite-sum calculation used for kernel composition. In a general predicate fibration, the relevant obligations become Beck-Chevalley, Frobenius reciprocity, and compatibility of quantification with context combination.

One limitation is important: a general contextad does not provide a canonical map $A\odot P\to A$\. The formulas above therefore require additional comprehension/projection structure, or a replacement notion of context elimination. They cannot simply be imposed on every contextad.

The payoff would be a unified categorical interface for partial correctness, nondeterministic choice, quantitative verification, probabilistic reasoning, and resource-sensitive typing.

## 6\. Mixed contextads and contentads: reading and writing in one calculus

Priority: very high · Feasibility: moderate in simple cases; substantially harder for dependent grades · Explicit future direction in §8

This is arguably the most natural structural generalization of the paper, and the authors explicitly identify it.

A contextad describes a computation consuming an extended context. A contentad describes one producing additional content. The basic combined arrow should resemble

$$
A\odot P\longrightarrow Q\star B,
$$

but the type of $Q$, its dependence on intermediate outputs, and the order in which context and content are combined require additional laws.

A useful starting point avoids the full tricategorical complexity. Take an ordinary comonad $G$ and monad $T$, and suppose there is a mixed distributive law

$$
\lambda:GT\Longrightarrow TG
$$

compatible with both (co)units and (co)multiplications.

Then arrows

$$
f:GA\to TB,\qquad g:GB\to TC
$$

admit the candidate composition

$$
\begin{aligned}
GA &\xrightarrow{\delta_A}GGA
\xrightarrow{Gf}GTB\\
&\xrightarrow{\lambda_B}TGB
\xrightarrow{Tg}TTC
\xrightarrow{\mu_C}TC.
\end{aligned}
$$

The unit is $GA\xrightarrow{\varepsilon_A}A\xrightarrow{\eta_A}TA$\. The mixed distributive-law axioms supply the associativity and unit obligations.

This already combines coeffects and effects without identifying them.

For the reader comonad $G(A)=A\times R$ and writer monad $T(A)=A\times W$, the obvious reassociation/interchange

$$
((A\times W)\times R)
\cong
((A\times R)\times W)
$$

gives a basic test case: read from an environment and accumulate a log.

The genuinely new challenge is to replace fixed $G,T$ with dependent context and content fibrations. The interchange must then account for how producing content changes the base over which later contexts are indexed.

Success would produce a combined $\mathrm{Ctx}$\-$\mathrm{Cnt}$ construction containing sequential read/write systems, possibly more general polynomial interactions, and bidirectional computational semantics.

The paper explicitly conjectures that polynomials in the sense of Gambino-Kock could arise from such a mixed construction. That conjecture would be a worthwhile central target, rather than merely another example.

## 7\. Feedback, traces, and conditionally commuting contexts

Priority: medium-high · Feasibility: conditional · Main obstacle: solving feedback and exchanging dependencies

Two structures are often conflated here, but need different laws.

Feedback asks when a contextful morphism with an internal interface can be closed around that interface. For a parameterized map

$$
f:A\times P\times U\to B\times U,
$$

a traced ambient monoidal category would suggest

$$
\operatorname{Tr}^{U}(f):A\times P\to B.
$$

For ordinary $\mathrm{Para}$, a compatible traced structure offers a straightforward starting point: retain the parameter $P$ while tracing the $U$\-wire.

For dependent contextads, however, closing a wire may affect which contexts are legal. There must be a rule for reindexing contexts through feedback, as well as an appropriate trace or guarded fixed-point operation.

This is a genuine obstruction, not merely another coherence diagram. For example, no cartesian trace on ordinary $\mathbf{Set}$ can extend to arbitrary feedback in the expected way: traced cartesian structure induces fixed-point operations, whereas Boolean negation has no fixed point. Guarded iteration, partiality, domain-theoretic fixed points, or contractive maps are plausible restrictions.

Context commutation is a separate issue. The paper's monoidal inheritance results do not mean that sequentially acquired dependent contexts can be exchanged.

A second context may only exist after the first has been applied. To interchange them, one needs an independence condition and a coherent exchange map between their two combination orders.

For example, updates to disjoint components of a state should commute, while arbitrary updates to the same component need not. A graded independence relation or a duoidal-style structure could express this distinction, with exchange available only when the dependency conditions are satisfied.

This suggests a categorical semantics of concurrency and separation logic in which independence is witnessed rather than assumed.

## 8\. A useful obstruction: not every effect monad can be transposed into discrete context

There is a precise limit to the paper's transposition program that is worth making explicit.

Suppose a monad $T$ on $\mathbf{Set}$ admits a discrete-grade contextad presentation whose equivalence with its Kleisli category preserves postcomposition by pure maps.

Then for each fixed $A$,

$$
\mathbf{Set}(A,TB)
\cong
\coprod_{P\in\mathcal M_A}
\mathbf{Set}(A\odot P,B)
$$

naturally in $B$\.

Taking $A=1$, this forces

$$
TB\cong\coprod_{P\in\mathcal M_1}B^{E_P},
\qquad E_P=1\odot P.
$$

Thus the underlying functor $T$ must be a coproduct of representables: a polynomial functor on sets.

Such functors preserve pullbacks.

Now consider the continuation monad with answer set $2=\{0,1\}$\:

$$
T(B)=2^{\,2^B}.
$$

Apply $T$ to the pullback square $2\times_1 2=4$, where both maps $2\to1$ are constant. Direct calculation gives

$$
|T(4)|=2^{16}=65536,
$$

but

$$
|T(2)\times_{T(1)}T(2)|=64.
$$

The canonical comparison cannot be an isomorphism. Therefore this continuation functor is not polynomial, and no pure-map-compatible, discrete-grade transposition of the stated form exists\.

This conclusion has a specific scope. It does not prohibit presentations using non-discrete context categories followed by quotienting, nor does it settle the paper's weaker notion of identity-on-objects equivalence if preservation of pure maps is omitted.

It does show why simply adding the continuation monad to the paper's list of discrete contextad transpositions is not a routine generalization.

The positive counterpart is the paper's Appendix A: polynomial monads do admit the intended transposition construction (Theorem A.4, for which the authors leave the abstract proof as future work).

## 9\. Compose contextads with other contextads

Priority: high · Feasibility: conditional · Potential payoff: a calculus of interacting coeffects

The mixed contextad-contentad construction combines context consumption with content production. A separate question is what happens when two different notions of context consumption interact\.

Suppose $D$ and $E$ are contextad structures over a compatible base. One might hope to form a composite $DE$, analogous to composing monads. But two pseudomonads do not generally compose to another pseudomonad merely by composing their underlying morphisms.

The likely missing datum is a higher distributive law, schematically

$$
\chi:DE\Longrightarrow ED,
$$

together with compatibility with the context units, context combination, and dependent reindexing. Its exact type must be formulated in the ambient tricategory, rather than imported unchanged from ordinary monad theory.

A concrete test case would combine two context mechanisms: stochastic randomness and partiality. Does drawing randomness before testing definedness have the same semantics as first restricting the legal inputs and then drawing randomness? Usually not without additional normalization or conditioning choices.

That makes the interchange law mathematically meaningful. It specifies which reorderings of contextual effects are admissible, and which semantic information would be lost by reordering.

The target theorem would characterize when two contextads admit a composite contextad and when its resulting $\mathrm{Ctx}$ construction agrees with an iterated construction. This could yield a modular theory of coeffects rather than a catalog of isolated examples.

## 10\. Recognition theorems: when is a double category secretly a $\mathrm{Ctx}$?

Priority: very high for foundational development · Explicitly suggested by the authors

There is also a converse problem to the paper's construction.

Every contextful arrow has a canonical-looking factorization into acquiring context and then applying a pure map\:

$$
A
\xrightsquigarrow{(P,\mathrm{id})}
A\odot P
\xrightarrow{f}
B.
$$

This suggests asking which double categories can be reconstructed as $\mathrm{Ctx}(\odot)$\.

A factorization property alone is insufficient. One would additionally need to recover the context fibres $\mathcal M_A$, their reindexing, and the coherent operation that combines contexts. These data should be stable under the relevant squares and horizontal compositions.

The contrast with relations is instructive. Passing from spans to relations preserves compositional behavior but forgets which witnesses realized the relation. A recognition theorem that assumes witness recovery without encoding it would accidentally exclude exactly the quotients that make the construction interesting.

The paper identifies reconstruction by factorization systems as a future direction. A worthwhile refinement would be a recognition theorem with a controlled quotient clause\: distinguish double categories that are literally of the form $\mathrm{Ctx}(\odot)$ from those that are quotients or completions of one. That distinction would unify the recognition problem with the stochastic and relational constructions above.

One foundational caution also deserves attention. The discussion surrounding §4.4 describes the relevant presentation of Kleisli tricocompletion as conjectural at the level of its full universal property. That does not invalidate the explicit $\mathrm{Ctx}$ composition, but it makes separating concrete coherence results from stronger universal-property claims especially important before attempting another categorical level.

For precision, the relational formula in §4 above should be read as follows: given $A\xleftarrow{\sigma}S\xrightarrow{\tau}B$,

$$
aRb\iff \exists u\in S:
\sigma(u)=a\ \wedge\ \tau(u)=b.
$$

## What actually merits a research program?

The most promising projects have different optimization targets.

| Target                            | Why pursue it                                                                    | Decisive first result                                                                                               |
| --------------------------------- | -------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------- |
| Stochastic contextads             | Concrete semantics; retains latent randomness and its reparameterizations        | Construct the finite contextad and prove its observational quotient is $\mathbf{FinStoch}$                                        |
| Differential contextads           | Makes dependency-sensitive differentiation compositional                         | Exhibit a display class on which tangent transport preserves context substitution                                   |
| Mixed contextad-contentad wreaths | Potential new universal construction containing both effect and coeffect systems | Prove associativity for a nontrivially dependent mixed example                                                      |
| Recognition and quotients         | Explains the exact expressive boundary of the whole framework                    | Necessary and sufficient conditions for reconstruction, including witness-retaining versus witness-forgetting cases |
| Interacting contextads            | Modular composition of multiple contextual mechanisms                            | Construct and verify a nontrivial higher distributive law                                                           |

The finite stochastic construction would be the first one to develop. It has a precise input category, explicit context composition, an ordinary semantics against which the result can be checked, and a quotient theorem that is substantial but accessible. It also exposes an important distinction: equality of probabilistic behavior is weaker than equivalence of implementations.

The mixed contextad-contentad construction would be the higher-risk, potentially higher-payoff project. Its central problem is not finding another example of an effect. It is deriving the distributive law that makes context acquisition and content production compose coherently when both are dependent.

The recognition theorem would be the project most likely to clarify the mathematical boundaries of the framework itself.

A particularly strong eventual result would connect all three: a contextad whose horizontal arrows are probabilistic implementations, a mixed construction that adds observations or state changes, and a theorem showing precisely which information survives passage to ordinary stochastic semantics.

That would demonstrate something considerably stronger than “yet another construction fits the framework”: it would show that wreath products organize the distinction between intensional computational structure, compositional interaction, and extensional behavior, with mathematically controlled passage between those levels.
