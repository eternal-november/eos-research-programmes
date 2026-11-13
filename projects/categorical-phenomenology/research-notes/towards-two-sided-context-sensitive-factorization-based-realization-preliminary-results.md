NOTE:
 - continuation of `towards-two-sided-context-sensitive-factorization-based-realization.md`
 - results were smoke tested with python, not a theorem prover
 - needs to be disaggregated, formally verified (ideally); eventually research seeds/contracts/programs should be made. Might do this along with a refactor of this subproject's layout
 - [7.3](7.3 Serial composition of open systems) a point-mass successor after quotienting is not alone sufficient for a valid quotient machine. The output laws and quotient-successor laws must also agree between representatives of the same quotient state.

You:
What is the minimal categorical structure needed to organize two-sided, context-sensitive realization, and what are its nontrivial universal properties?

Specify the primitive observational data, admissible contexts and tests, categories of realizations, morphisms between realizations, and reconstruction operations. Distinguish what is assumed from what can be derived.

Work through one finite example that supports two genuinely different constructions—such as behavioral minimization and Isbell/FCA completion—from the same observational data.

Establish an explicit comparison between them. Which universal properties determine the comparison? Under what conditions does it preserve compositional structure? Exhibit an obstruction when those conditions fail.

Determine whether the example supports a general theorem, a restricted family of compatible reconstruction doctrines, or merely a common presentation of otherwise independent constructions.

Discriminate among at least three materially different possibilities:

1. A genuine common construction: The same mathematical machinery derives several reconstruction procedures, and relationships between them follow from its axioms.

2. A structured family of doctrines: Different reconstruction procedures have different universal properties, but meaningful comparison maps, exactness conditions, and obstructions organize their relationships.

3. A largely formal umbrella: The procedures can all be represented in a common framework, but the framework contributes little beyond recording known constructions individually.

ChatGPT:
## Result and scope

For exact Boolean observations, there is a genuine common reconstruction mechanism: freely add the chosen algebraic structure, then take the image of the observational interpretation. Behavioral minimization and FCA completion are two instances. Their comparison is canonical, and compatibility with contexts has a necessary-and-sufficient condition.

That is stronger than a common presentation. But it establishes a theorem for a restricted family of reconstruction doctrines, not a universal semantics of phenomenology.

The assumptions below are exact Boolean responses, deterministic contexts, and specified algebraic operations on response profiles. The derived objects are observational quotients, concept lattices, comparison maps, and obstruction witnesses. The choice of tests, their empirical adequacy, noisy-data stability, and compatibility with parallel composition are not derived.

The finite example will have six preparations, three behavioral states, and five FCA states. A context preserving the behavioral states will fail to extend to the FCA structure. Enlarging the tests repairs the failure but produces eight FCA states.

## 1. Primitive observational data

### 1.1 Preparations, tests, and contexts

A lean typed formulation starts with a small category $\mathcal C$ of admissible contexts and two functors

$$
P:\mathcal C\to\mathbf{Set},
\qquad
T:\mathcal C^{op}\to\mathbf{Set}.
$$

At an interface $x$, $P_x$ is the set of preparations or histories and $T_x$ the set of tests. A context $c:x\to y$ acts forward on preparations,

$$
P(c):P_x\to P_y,
$$

and backward on tests,

$$
T(c):T_y\to T_x.
$$

The observational datum is a family

$$
H_x:P_x\times T_x\to 2
$$

satisfying the compatibility law

$$
\boxed{
H_y(P(c)p,t)=H_x(p,T(c)t).
}
\tag{1}
$$

Thus “perform the context and then test” agrees with “perform the corresponding test before the context.”

The two-sided pairing is a Boolean Chu/formal-context datum; the forward/backward compatibility is the same form of equation used for infomorphisms between formal contexts. ([Mickey Lili](https://math.mickeylili.com/files/preprints/The_concept_lattice_functors.pdf))

Equation (1) is an assumption, not a consequence of having a table. A primitive test family need not contain its precompositions with admissible contexts. When those precompositions are declared admissible, the test family can be enlarged by closure under them. That enlargement changes the observational regime.

For a single interface, $\mathcal C$ is simply a monoid of contexts.

### 1.2 The response-profile object

Define

$$
B_x=\mathcal P(T_x),
\qquad
\rho_x(p)=\{t:H_x(p,t)=1\}.
$$

Contexts act on profiles by inverse image:

$$
B(c)(V)=T(c)^{-1}(V).
$$

Equation (1) says precisely that

$$
\rho:P\Rightarrow B
$$

is natural. Moreover, every $B(c)$ preserves arbitrary intersections, including the empty intersection.

This is the first substantive compatibility fact: context transport preserves the algebra used by the completion below.

No Markov category, equipment, or cylinder factorization system is needed for this fragment.

## 2. Categories of realizations

First suppress the interface index.

A set-based realization of $H$ is a factorization

$$
P\xrightarrow{r}S\xrightarrow{o}B,
\qquad
or=\rho.
\tag{2}
$$

Here $r$ assigns a represented state to each preparation; $o$ gives that state’s complete response profile. In the contextual version, $S:\mathcal C\to\mathbf{Set}$ and both maps are natural.

A morphism of realizations

$$
f:(S,r,o)\longrightarrow(S',r',o')
$$

is a context-compatible map satisfying

$$
fr=r',
\qquad
o'f=o.
\tag{3}
$$

These conditions preserve both the preparation interpretation and every admitted test-not merely an aggregate score.

A realization is observable when $o$ is injective, and preparation-reachable when $r$ is surjective. Neither condition is imposed on every realization.

### 2.1 Adding a reconstruction doctrine

A doctrine specifies the admissible structure on $S$ and the operations its interpretation must preserve.

For example:

| Doctrine        | State objects              | Interpretation maps                      |
| --------------- | -------------------------- | ---------------------------------------- |
| Behavioral      | Sets                       | Functions                                |
| Conjunctive/FCA | Complete meet-semilattices | Maps preserving all meets, including top |

In the second doctrine, $B=\mathcal P(T)$ carries intersection as meet. Requiring $o$ to preserve meets asserts

$$
o\!\left(\bigwedge_i s_i\right)=\bigcap_i o(s_i).
$$

This is a substantive modeling choice: the doctrine admits formal conjunctions of response profiles. The observation table alone does not require that choice.

For a general doctrine, write

$$
F:\mathbf{Set}\rightleftarrows\mathcal A:U,
\qquad F\dashv U,
$$

for its free/forgetful adjunction. Assume $B$ has an admissible $\mathcal A$-structure. A realization consists of

$$
r:P\to US,
\qquad
o:S\to B
$$

with $o$ an $\mathcal A$-morphism and $U(o)r=\rho$. Realization morphisms are $\mathcal A$-morphisms satisfying (3).

This identifies exactly what is extra: the algebraic doctrine, its free objects, and its admissible interpretation maps.

## 3. A common reconstruction theorem

The observation map uniquely extends along the free-object adjunction:

$$
\bar\rho:F(P)\longrightarrow B.
$$

Assume the relevant category has an orthogonal factorization system $(\mathcal E,\mathcal M)$. Factor

$$
F(P)\xrightarrow{e}M_H\xrightarrow{m}B,
\qquad
e\in\mathcal E,\quad m\in\mathcal M.
\tag{4}
$$

In the examples, these are surjective and injective homomorphisms.

### Theorem: free structure followed by image

The realization $M_H$ is:

Initial among observable realizations. Every realization whose observation map lies in $\mathcal M$ receives a unique realization morphism from $M_H$.

Terminal among algebraically reachable realizations. Every realization whose extended preparation map $F(P)\to S$ lies in $\mathcal E$ has a unique realization morphism to $M_H$.

Consequently, $M_H$ is the unique, up to unique realization isomorphism, realization that is both algebraically reachable and observable.

Proof. For an observable realization $F(P)\xrightarrow{a}S\xrightarrow{b}B$, orthogonality applied to

$$
\begin{array}{ccc}
F(P)&\xrightarrow{a}&S\\
{\scriptstyle e}\downarrow&&\downarrow{\scriptstyle b}\\
M_H&\xrightarrow{m}&B
\end{array}
$$

gives the unique map $M_H\to S$. When $a\in\mathcal E$, applying orthogonality with $a$ and $m$ instead gives the unique map $S\to M_H$. ∎

This is the factorization mechanism underlying categorical minimization: appropriate initial and terminal objects, together with a factorization system, yield a canonical minimal realization. ([Logical Methods in Computer Science](https://lmcs.episciences.org/6213/pdf))

For contexts, the construction is performed in the corresponding functor category. In the concrete examples, images are computed pointwise, and naturality supplies their context actions.

### What is actually minimal here?

The proof needs only the relevant factorizations and unique lifting properties. A full factorization system is a convenient global package. The free-object adjunction supplies the initial realization; the response-profile object supplies the terminal one.

There is no established doctrine-independent “smallest categorical structure.” But the above is a lean sufficient structure with genuine consequences.

### 3.1 Behavioral reconstruction

For $\mathcal A=\mathbf{Set}$, the free functor is the identity:

$$
Q_H=\operatorname{im}(\rho)
=\{\rho(p):p\in P\}\subseteq B.
$$

Equivalently,

$$
p\sim_H p'
\iff
\forall t\in T,\quad H(p,t)=H(p',t).
$$

The quotient $P\twoheadrightarrow Q_H$ is the coequalizer of this equivalence relation. Because the tests satisfy (1), the equivalence is stable under all admitted contexts.

Here algebraic reachability is ordinary preparation-reachability: there are no extra operations generating states.

### 3.2 FCA reconstruction

Let $\mathcal A=\mathbf{CMeet}$, the category of complete meet-semilattices and arbitrary-meet-preserving maps.

The free complete meet-semilattice on $P$ is

$$
F(P)=\mathcal P(P)^{op}.
$$

Its meets are unions, its top is $\varnothing$, and its generators are the singletons. The extended interpretation is

$$
\bar\rho(A)=\bigcap_{p\in A}\rho(p).
$$

Its image is

$$
\boxed{
L_H=
\left\{
\bigcap_{p\in A}\rho(p):A\subseteq P
\right\}.
}
\tag{5}
$$

Thus $L_H$ is the smallest intersection-closed family containing the observed rows, including the empty intersection $T$.

This is exactly the family of FCA intents. Define the antitone maps

$$
A^\uparrow=\{t:\forall p\in A,\ H(p,t)=1\},
$$

$$
V^\downarrow=\{p:\forall t\in V,\ H(p,t)=1\}.
$$

Then

$$
L_H=\operatorname{Fix}((-)^{\downarrow\uparrow}).
$$

The usual concept lattice is ordered by inclusion of extents, hence reverse inclusion of intents. Accordingly, $L_H$, ordered here by inclusion, is the opposite of the usual concept lattice. The standard Galois-connection and fixed-point descriptions are the Boolean FCA construction. ([Mickey Lili](https://math.mickeylili.com/files/preprints/The_concept_lattice_functors.pdf))

There is also a poset adjunction:

$$
c_H:\mathcal P(T)\rightleftarrows L_H:i,
\qquad c_H\dashv i,
$$

where

$$
c_H(V)=V^{\downarrow\uparrow}.
$$

Explicitly, for $W\in L_H$,

$$
c_H(V)\subseteq W
\iff
V\subseteq W.
$$

This is a closure/reflection universal property, distinct from the image universal property used for behavioral minimization.

The common theorem does not identify the two constructions. It explains how changing the free structure changes the generated image.

## 4. The comparison and its exact compatibility condition

### 4.1 Why the comparison is canonical

Every row belongs to its intersection closure, so there is an inclusion

$$
j_H:Q_H\hookrightarrow L_H,
\qquad
j_H(\rho(p))=\rho(p).
\tag{6}
$$

This is not an arbitrary embedding. Forgetting the meet structure, $L_H$ is an observable set-based realization. Since $Q_H$ is initial among such realizations, $j_H$ is the unique realization morphism $Q_H\to L_H$.

The two universal properties have different roles: the image property determines $Q_H$, while meet-generation determines $L_H$; initiality among observable realizations determines their comparison.

Moreover,

$$
j_H\text{ is an isomorphism}
\iff
Q_H\text{ is already closed under all intersections, including }T.
\tag{7}
$$

Forgetting meet structure does not generally preserve reachability. “Generated from preparations by meets” is different from “every state is the image of a preparation.”

### 4.2 The completion is not freely generated by the behavioral states

Although $F(P)$ is free, $L_H$ usually is not. Its generators satisfy equations imposed by their actual profiles:

$$
\bigcap_{q\in A}q=\bigcap_{q\in A'}q.
$$

Those equations are crucial.

Let $g:Q_H\to Q_{H'}$ be a proposed comparison or transition. There exists a complete-meet-preserving extension

$$
\widehat g:L_H\to L_{H'}
$$

with $\widehat g\,j_H=j_{H'}g$ if and only if

$$
\boxed{
\bigcap_{q\in A}q=\bigcap_{q\in A'}q
\Longrightarrow
\bigcap_{q\in A}g(q)=\bigcap_{q\in A'}g(q)
}
\tag{8}
$$

for all $A,A'\subseteq Q_H$, including empty subsets.

Proof. Necessity follows by applying a meet-preserving map to the equation. For sufficiency, the only possible extension is

$$
\widehat g\!\left(\bigcap_{q\in A}q\right)
=
\bigcap_{q\in A}g(q).
$$

Condition (8) makes it well-defined. Intersections of represented elements correspond to unions of their indexing families, so the extension preserves all meets. Meet-generation proves uniqueness. ∎

This gives an exact obstruction criterion, rather than a generic demand that some diagram commute.

It also supplies coherence. Whenever the extensions exist,

$$
\widehat{g_2g_1}=\widehat g_2\,\widehat g_1,
\qquad
\widehat{\mathrm{id}}=\mathrm{id},
$$

because both sides are meet-preserving extensions agreeing on the generators.

### 4.3 Why the admitted contexts extend

For a context $c$, inverse image preserves intersections:

$$
T(c)^{-1}\!\left(\bigcap_i V_i\right)
=
\bigcap_i T(c)^{-1}(V_i).
$$

Therefore its action on behavioral states satisfies (8). It extends uniquely to $L_H$, and

$$
\begin{array}{ccc}
Q_x&\xrightarrow{j_x}&L_x\\
{\scriptstyle Q(c)}\downarrow&&\downarrow{\scriptstyle L(c)}\\
Q_y&\xrightarrow{j_y}&L_y
\end{array}
\tag{9}
$$

commutes.

The primitive test-reindexing condition is a transparent sufficient condition. Equation (8) is the precise necessary-and-sufficient condition for extending a given map of behavioral states.

This guarantees context composition and meet structure. It does not automatically guarantee preservation of joins, parallel composition, gluing, or feedback.

### 4.4 Comparisons between observational presentations

For tables $H,H'$, an infomorphism consists of

$$
u:P\to P',
\qquad
v:T'\to T,
\qquad
H'(u(p),t')=H(p,v(t')).
$$

Then inverse image induces both

$$
Q_H\to Q_{H'},
\qquad
L_H\to L_{H'},
$$

and the square between their canonical inclusions commutes. With contexts, require the corresponding maps to be natural.

Thus the comparison is functorial on an independently defined category of observational presentations. This is consistent with the established functorial treatment of formal contexts and concept lattices-not merely object-by-object bookkeeping. ([ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0888613X12001351))

## 5. One finite example

### 5.1 Observations and admissible contexts

Take

$$
P=\{0,1,2\}\times\{0,1\}.
$$

The second coordinate labels two preparations with the same observed behavior.

Let

$$
T=\{t_0,t_1,t_2,\mathsf{true},\mathsf{false}\},
$$

with

$$
H((i,k),t_j)=1\iff i=j.
$$

The constant tests always return their indicated truth values.

| Preparations | $t_0$ | $t_1$ | $t_2$ | $\mathsf{true}$ | $\mathsf{false}$ |
| ------------ | ----: | ----: | ----: | ----: | ----: |
| $(0,0),(0,1)$        |     1 |     0 |     0 |     1 |     0 |
| $(1,0),(1,1)$        |     0 |     1 |     0 |     1 |     0 |
| $(2,0),(2,1)$        |     0 |     0 |     1 |     1 |     0 |

Choose the context monoid consisting of permutations and constant maps on $\{0,1,2\}$, acting by

$$
m(i,k)=(m(i),k).
$$

These are permutations and resets. They form a monoid.

Tests reindex by precomposition. A permutation sends a singleton test to a singleton test. A reset sends a singleton test to either $\mathsf{true}$ or $\mathsf{false}$. Hence the given test family is closed under these contexts.

### 5.2 Behavioral minimization

The distinct rows are

$$
R_i=\{\mathsf{true},t_i\},
\qquad i=0,1,2.
$$

Therefore

$$
Q_H=\{R_0,R_1,R_2\}.
$$

The six preparations reduce to three behavioral states. Contexts act by

$$
R_i\longmapsto R_{m(i)}.
$$

No smaller exact set realization exists: the three distinct profiles require three distinguishable states.

### 5.3 FCA completion

For $i\neq j$,

$$
R_i\cap R_j=\{\mathsf{true}\}.
$$

The empty intersection is $T$. Thus

$$
L_H=
\left\{
\underbrace{\{\mathsf{true}\}}_{\bot_L},
R_0,R_1,R_2,
\underbrace{T}_{\top_L}
\right\}.
$$

It is the five-element lattice with three incomparable intermediate elements.

The comparison $j_H$ includes the three behavioral states into the five concept states. The additional elements are not additional observed preparations. They arise from the selected conjunction/completion doctrine.

A permutation permutes the $R_i$ and fixes $\bot_L,\top_L$. A reset to $0$ sends

$$
\bot_L,R_0,R_1,R_2\longmapsto R_0,
\qquad
\top_L\longmapsto\top_L.
$$

This preserves all meets.

It does not preserve all joins:

$$
R_1\vee R_2=\top_L,
$$

but the reset sends the two sides respectively to $\top_L$ and

$$
R_0\vee R_0=R_0.
$$

Thus even a valid context need not be a complete lattice homomorphism. The guaranteed doctrine is meet-preservation; changing to preservation of both lattice operations would impose a stronger requirement.

## 6. An obstruction, and an explicit repair

### 6.1 A valid behavioral transition that cannot extend

Consider

$$
g(0)=0,\qquad g(1)=0,\qquad g(2)=1.
$$

It defines a perfectly valid deterministic transition on $Q_H$:

$$
R_0\mapsto R_0,\qquad
R_1\mapsto R_0,\qquad
R_2\mapsto R_1.
$$

It also lifts to the preparations by $g(i,k)=(g(i),k)$, so it respects the behavioral quotient.

Nevertheless, it cannot extend to a meet-preserving map $L_H\to L_H$. The source has the equation

$$
R_0\cap R_1=R_0\cap R_2=\bot_L.
$$

Its proposed images give

$$
g(R_0)\cap g(R_1)=R_0,
$$

while

$$
g(R_0)\cap g(R_2)=\bot_L.
$$

Condition (8) fails.

The violated invariant is an equality between two conjunctions of response profiles. Preservation of behavioral equivalence alone does not preserve that equality.

The failure is visible directly in the tests:

$$
t_0\circ g=t_0\lor t_1,
$$

and this test is absent from $T$. The new transition therefore does not satisfy the original context contract.

In fact, for this example, the maps $Q_H\to Q_H$ admitting meet-preserving extensions are exactly the permutations and constants. A map with two-element image necessarily identifies one pair of generators but not another, producing the displayed contradiction. Thus nine of the twenty-seven state transformations extend.

### 6.2 Closing the tests under the new contexts

Adjoin the missing precomposed tests and close under the existing permutations and $g$.

The permutations generate all three two-element predicates from $t_0\lor t_1$. Together with the existing singleton and constant predicates, the resulting test set is

$$
T^+=\mathcal P(\{0,1,2\}).
$$

Interpret $U\in T^+$ by

$$
H^+((i,k),U)=1\iff i\in U.
$$

The three behavioral states remain distinct and no new ones arise.

But their new response profiles are

$$
R_i^+=\{U:i\in U\}.
$$

Their intersections are

$$
R_A^+
=
\bigcap_{i\in A}R_i^+
=
\{U:A\subseteq U\},
\qquad A\subseteq\{0,1,2\}.
$$

All eight are distinct. Hence

$$
|Q_{H^+}|=3,
\qquad
|L_{H^+}|=8.
$$

Every function $f:\{0,1,2\}\to\{0,1,2\}$ now acts on tests by inverse image and on the completion by

$$
\widehat f(R_A^+)=R_{f[A]}^+.
$$

In particular, $g$ extends.

### 6.3 Why forgetting the added tests is not dynamically harmless

Restriction of profiles gives a meet-preserving map

$$
\pi:L_{H^+}\to L_H.
$$

The two distinct states

$$
R_{\{0,1\}}^+,\qquad R_{\{0,2\}}^+
$$

both restrict to $\bot_L$. But after applying $g$,

$$
\pi\widehat g(R_{\{0,1\}}^+)=R_0,
$$

whereas

$$
\pi\widehat g(R_{\{0,2\}}^+)=\bot_L.
$$

Consequently, no function at all $h:L_H\to L_H$ can satisfy

$$
h\pi=\pi\widehat g.
$$

This is stronger than failure of meet-preservation: the restriction quotient is not a congruence for the enlarged dynamics.

There is no contradiction with the comparison theorem. Restriction remains a valid comparison of static observational tables, and respects the original context monoid. It does not respect the enlarged context monoid.

The example therefore separates three claims:

$$
\text{same behavioral states},
\qquad
\text{same completed structure},
\qquad
\text{same context-compatible completed structure}.
$$

They are not equivalent.

## 7. What general theorem has actually been established?

The calculations support more than this one example.

### A restricted reconstruction theorem

Given a context-compatible observational profile map

$$
\rho:P\to UB,
$$

a doctrine with a free-object adjunction and suitable image factorization produces

$$
\boxed{
M_H=\operatorname{im}\bigl(F(P)\to B\bigr).
}
$$

The resulting realization has the universal properties in Section 3. Contexts lift when their action on the ambient profiles preserves the doctrine’s operations. Comparisons between generated realizations are determined by preservation of the equations satisfied by their generators.

For the two doctrines examined here:

$$
\begin{aligned}
\text{no additional operations}
&\quad\Rightarrow\quad
Q_H=\operatorname{im}(\rho),\\
\text{arbitrary meets}
&\quad\Rightarrow\quad
L_H=\operatorname{im}(\bar\rho).
\end{aligned}
$$

Their inclusion, its isomorphism criterion, the extension condition, and the obstruction all follow from this machinery.

The theorem is not limited to finite tables. Finiteness makes the example computable and allows the full compatibility classification. What remains restricted is the class of doctrines admitting the specified free structures, factorization systems, and compatible context actions.

### What it does not establish

The theorem does not show that arbitrary topological reconstruction, stochastic realization, descent, causal identification, and neural representation learning fit these hypotheses. Each proposed import must supply its admissible structure, interpretation object, generation operation, and preservation theorem.

Nor does the occurrence of “Isbell” establish such a transfer. Garner’s Isbell-envelope theorem characterizes cylinder factorization systems through a pseudomonad, but that is additional mathematics-not a proof that every observational nucleus or empirical reconstruction is an instance of the present construction. ([arXiv](https://arxiv.org/abs/1410.7108))

For the current problem, cylinder factorization systems are unnecessary overhead. The stronger claim would require an application in which their extra generality supplies a reconstruction or comparison unavailable here.

## 8. Discriminating the three possibilities

| Possibility                       | Assessment                                                                                                                                                                                                                                                                                                      |
| --------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| 1. Genuine common construction    | Established for this pair, in a qualified but substantive sense. The same free-structure-plus-image theorem derives both reconstructions. Their comparison and compatibility conditions follow from universal properties. The choice of algebraic structure remains an input.                                   |
| 2. Structured family of doctrines | The strongest justified broader conclusion. Different doctrines impose different generation and preservation requirements. The common machinery supplies meaningful comparisons only when those requirements interact appropriately.                                                                            |
| 3. Largely formal umbrella        | Accurate for the bare pairing-and-factorization presentation, but not for the sharpened theory above. A category of arbitrary realizations alone predicts little. Specifying free structures, image classes, and equations produces unique comparisons, exactness criteria, and explicit impossibility results. |

The distinction between the first two is not a choice between incompatible answers. A structured family can contain genuine common-construction theorems on substantial subfamilies.

The mathematical conclusion is therefore: a general theorem for a restricted family of compatible reconstruction doctrines, with a real common construction inside that family. The organizing structure earns its content from three ingredients:

$$
\boxed{
\text{specified generation}
\;+\;
\text{observational identification}
\;+\;
\text{context-preservation laws}.
}
$$

Removing the first leaves no account of which structure is being introduced. Removing the second leaves arbitrary presentations. Removing the third permits abstractions that cease to represent the observations once the system is used in context.

The finite example proves all three ingredients matter: behavioral minimization and FCA completion are canonically related, but admitting one additional context forces a change in the completion even though the behavioral state set is unchanged.


You:
Let's try to break the theorem. For example: Does the common reconstruction theorem survive stochastic realization?



Work first in \\(\mathbf{FinStoch}\\), with finite preparations, tests, stochastic responses, and explicitly specified admissible contexts.

Compare three constructions from the same observational data:

1. Behavioral realization: quotient preparations by observational indistinguishability.
2. Convex realization: freely generate probabilistic mixtures and take the image of the resulting response map.
3. Latent stochastic realization: factor the observed Markov kernel through a hidden-state space, minimizing latent-state cardinality where meaningful.

Determine whether these are instances of one universal construction or genuinely different reconstruction doctrines.

Establish their universal properties, if any. Determine whether canonical comparisons exist, whether they preserve sequential and parallel stochastic composition, and which compatibility conditions are necessary.

Produce explicit finite counterexamples distinguishing their notions of minimality, demonstrating nonuniqueness of latent realizations, or obstructing compositional comparison.

Crucially, distinguish individual-test marginals from joint observational laws, and do not assume that observationally equivalent latent representations remain equivalent under arbitrary wiring or interventions.

Conclude by determining exactly which part of the Boolean free-structure-plus-image theorem survives, which requires additional hypotheses, and which fails. Do not manufacture a unifying construction if the procedures genuinely have incompatible universal properties.

ChatGPT:
# Stochastic stress test of the reconstruction theorem

## 1\. Audit: the theorem does not survive unchanged

The Boolean reconstruction theorem splits into three different claims in the stochastic setting\:

1. Behavioral identification survives\: preparations with identical observational probability laws admit a canonical deterministic quotient, provided the observational interface is fixed.
2. Convex reconstruction survives after changing the ambient category\: freely mixing preparations and taking their observable image gives a canonical convex polytope with an image universal property. It is generally not an object of $\mathbf{FinStoch}$\.
3. Minimal latent stochastic realization is different\: factoring a kernel through the fewest hidden states is a nonnegative-factorization problem. It generally has nonunique minimizers and does not satisfy the same observable-image universal property.

The decisive obstruction is stronger than nonuniqueness\:

Some finite stochastic matrices have no epi-mono factorization in $\mathbf{FinStoch}$\. Consequently, the previous free-structure-plus-image argument cannot simply be internalized in that category.

The categorical setting is standard: objects of $\mathbf{FinStoch}$ are finite sets, arrows are row-stochastic matrices, composition is matrix multiplication, and the symmetric monoidal product is the Kronecker product. Its deterministic subcategory is $\mathbf{FinSet}$\.

### Exact failure of epi-mono factorization

For $K:X\rightsquigarrow Y$, with rows indexed by $X$,

$$
\begin{aligned}
K\text{ monic in }\mathbf{FinStoch}
&\iff \operatorname{rank}_{\mathbb R}K=|X|,\\
K\text{ epic in }\mathbf{FinStoch}
&\iff \operatorname{rank}_{\mathbb R}K=|Y|.
\end{aligned}
$$

To prove the first equivalence, full row rank ensures that postcomposition by $K$ is injective on stochastic matrices. Conversely, a nonzero left-kernel vector of $K$ has coordinate sum zero, so a sufficiently small perturbation of an interior probability distribution produces two distinct distributions with identical images.

For epimorphisms, full column rank makes precomposition injective. Conversely, a nonzero right-kernel vector allows two distinct, slightly perturbed stochastic maps $Y\rightsquigarrow\{0,1\}$ whose composites with $K$ agree.

Now consider

$$
K=\frac12
\begin{pmatrix}
0&0&1&1\\
1&0&0&1\\
1&1&0&0\\
0&1&1&0
\end{pmatrix}.
\tag{1}
$$

It is row-stochastic and has ordinary rank $3$\. Its nonnegative rank is $4$\.

For the nonnegative-rank lower bound, observe that each row has two positive entries and each pair of distinct rows has at most one common positive column. Thus the positive support contains no $2\times2$ rectangle. Each nonnegative rank-one summand can cover at most two of the eight positive entries. At least four summands are necessary, and four suffice.

Suppose there were an epi-mono factorization

$$
4\xrightarrow{A}Z\xrightarrow{B}4,
\qquad K=AB
$$

in $\mathbf{FinStoch}$\.

Epicity forces $\operatorname{rank}A=|Z|$, and monicity forces $\operatorname{rank}B=|Z|$\. Therefore

$$
\operatorname{rank}K=|Z|.
$$

So $|Z|=3$\. But a stochastic factorization through three states is a nonnegative factorization of inner dimension three, contradicting $\operatorname{rank}_+(K)=4$\.

Hence no such factorization exists.

This is a counterexample to the required categorical factorization property itself, not merely to an interpretation of minimality.

A substantial literature studies precisely the gap between ordinary rank, nonnegative rank, and stochastic latent representations.

## 2\. Specify the observational interface before reconstructing

Let $P,T,Y$ be finite sets of preparations, tests, and test outcomes. Take a kernel

$$
K:P\times T\rightsquigarrow Y.
$$

Write

$$
k_p^t(y)=K(y\mid p,t),
\qquad
r_p=(k_p^t)_{t\in T}\in
V:=\prod_{t\in T}\Delta(Y).
$$

Here $\Delta(Y)$ is the simplex of distributions on $Y$\.

This specifies the law of one selected test on one preparation\. It does not specify the joint law of several tests on the same preparation, or how the preparation changes after a test.

A joint experiment would require a kernel into a joint outcome space, such as $Y^T$, or a stateful instrument whose repeated application defines the experiment. Those are different observational interfaces.

### Admissible contexts

For a tractable initial interface, let an admissible context consist of a stochastic preparation transformation

$$
c:P\rightsquigarrow P
$$

and a deterministic test reindexing $\tau_c:T\to T$ satisfying

$$
\boxed{
\sum_{p'}c(p'\mid p)\,K(y\mid p',t)
=
K(y\mid p,\tau_c(t)).
}
\tag{2}
$$

The transformations must be closed under composition, with the corresponding contravariant composition of test reindexings.

This is a specified class of observationally compatible contexts, not the class of every stochastic map on $P$\. It can be generalized to richer test transformations and stateful open-system contexts, but neither extension follows from (2).

For the finite example below, the admissible contexts will be identity and an involution. More general stochastic contexts will be tested separately.

## 3\. Three constructions on one finite observation table

Take

$$
P=\{\ell_0,\ell_1,m,r_0,r_1\},
\quad
T=\{a,b\},
\quad
Y=\{0,1\}.
$$

The table records the probability of outcome $1$\.

| Preparation | Test $a$ | Test $b$ |
| ----------- | --------- | --------- |
| $\ell_0,\ell_1$        | 0         | 1         |
| $m$        | $1/2$      | $1/2$      |
| $r_0,r_1$        | 1         | 0         |

The admissible nonidentity context $s$ exchanges $\ell_i\leftrightarrow r_i$, fixes $m$, and exchanges tests $a\leftrightarrow b$\. Thus $s^2=1$, and (2) holds.

### A. Behavioral realization

Define

$$
p\sim_K p'
\iff
r_p=r_{p'}.
$$

The quotient has three elements,

$$
Q_K=\{L,M,R\},
$$

corresponding to the distinct row profiles

$$
(0,1),\quad
(1/2,1/2),\quad
(1,0).
$$

There is a deterministic surjection $q:P\to Q_K$, and the response kernel factors uniquely through it.

Universal property. In the category of deterministic preparation factorizations with injective response-profile maps, $Q_K$ is initial. Among preparation-surjective deterministic factorizations, it is terminal. Hence it is the canonical reachable-and-observable deterministic realization.

This statement uses the injectivity of the set map sending represented states to probability profiles. It does not claim that the corresponding stochastic output map is monic in $\mathbf{FinStoch}$\.

The involution acts on $Q_K$ by exchanging $L,R$ and fixing $M$\.

### B. Convex realization

Mix preparations before selecting a test. The observation map extends uniquely to an affine map

$$
\bar r:\Delta(P)\longrightarrow V,
\qquad
\bar r(\pi)=\sum_p\pi(p)r_p.
$$

Its image is

$$
C_K=\operatorname{conv}\{r_p:p\in P\}.
$$

In this example,

$$
C_K=
\{(u,1-u):0\leq u\leq1\}.
$$

Thus the reconstruction is a line segment, not a three-element set. It has two extreme points and affine dimension one.

Universal property. Work in finite-dimensional convex polytopes with affine maps. Consider factorizations of $\bar r$ through a convex space $S$,

$$
\Delta(P)\xrightarrow{a}S\xrightarrow{b}V.
$$

The image $C_K$ is initial among factorizations with injective $b$, and terminal among those with surjective $a$\. The proof is the usual affine image-factorization argument.

There is a canonical map

$$
Q_K\longrightarrow C_K
$$

sending each behavioral state to its row profile. It is injective, and its image affinely generates $C_K$\.

The same map extends uniquely to a surjective affine map

$$
\Delta(Q_K)\twoheadrightarrow C_K.
$$

Its kernel identifies the middle generator with the equal mixture of the endpoints\:

$$
\delta_M\sim
\tfrac12\delta_L+\tfrac12\delta_R.
\tag{3}
$$

This is exactly the new identification made by convex reconstruction.

However, $\Delta(P)$ and $C_K$ have infinitely many points. They are not objects of $\mathbf{FinStoch}$\. The construction uses an ambient category of convex spaces; $\mathbf{FinStoch}$ itself does not contain the object of all distributions on a nontrivial finite set.

### C. Minimal latent stochastic realization

Seek a finite hidden-state set $Z$ and kernels

$$
\alpha:P\rightsquigarrow Z,
\qquad
\beta:Z\times T\rightsquigarrow Y
$$

with

$$
K(y\mid p,t)
=
\sum_z\alpha(z\mid p)\beta(y\mid z,t).
\tag{4}
$$

The hidden-state distribution $\alpha(-\mid p)$ is independent of which test will subsequently be chosen. This is a substantive causal restriction.

The factorization has two latent states $Z=\{z_L,z_R\}$\. Take deterministic response profiles

$$
r_{z_L}=(0,1),
\qquad
r_{z_R}=(1,0),
$$

and let $\alpha$ assign $z_L$ to both $\ell_i$, $z_R$ to both $r_i$, and an equal mixture to $m$\.

One latent state is impossible because the observed profiles differ across preparations. Hence

$$
\min |Z|=2.
$$

The three results are\:

| Reconstruction | Result                         |
| -------------- | ------------------------------ |
| Behavioral     | 3 distinct states              |
| Convex         | Line segment; 2 extreme points |
| Minimal latent | 2 hidden states                |

These numbers are not three measurements of the same invariant. Behavioral state count, affine dimension or vertex count, and hidden-state cardinality are different optimization targets. Their agreement in special examples does not establish equivalence of doctrines.

The original involution lifts to all three constructions: exchange $L,R$, reflect the convex segment, or exchange $z_L,z_R$, respectively.

This is one case where all three admit compatible context actions. It establishes feasibility, not a general comparison theorem for latent models.

## 4\. The latent problem has a different universal structure

The latent problem can be stated geometrically. Each hidden state $z$ determines a response profile

$$
b_z=(\beta(-\mid z,t))_{t\in T}\in V.
$$

Equation (4) is equivalent to

$$
r_p\in\operatorname{conv}\{b_z:z\in Z\}
\quad\text{for every }p.
$$

Thus

$$
\boxed{
k_{\mathrm{lat}}(K)=
\min\left\{
k:
\exists b_1,\ldots,b_k\in V,\quad
C_K\subseteq\operatorname{conv}\{b_1,\ldots,b_k\}
\right\}.
}
\tag{5}
$$

The archetypes $b_z$ are allowed to lie outside the observed convex hull $C_K$, provided they remain inside the ambient space of admissible probability profiles.

This changes the construction fundamentally. Convex realization generates the smallest convex set containing the observations; latent realization searches for a small simplex-like generating presentation whose image contains those observations.

For one test, $K:P\rightsquigarrow Y$ is an ordinary stochastic matrix, and

$$
k_{\mathrm{lat}}(K)=\operatorname{rank}_+(K).
$$

To see this, take a nonnegative factorization $K=AB$\. Normalize each nonzero row of $B$ to sum to one and absorb its former sum into the corresponding column of $A$\. Since $K$ is row-stochastic, the resulting $A$ is row-stochastic as well. Thus nonnegative and stochastic inner dimensions agree.

For multiple independently selectable tests, (5) remains the correct condition. It should not be silently replaced by ordinary nonnegative rank of a flattened matrix: each hidden state's decoder must be a normalized distribution separately for every test, while the same preparation-to-hidden-state distribution must work for all tests.

### 4.1 The factorization category

For a single test, let $\mathsf{Fact}(K)$ have objects

$$
(A:P\rightsquigarrow Z,\quad B:Z\rightsquigarrow Y),
\qquad AB=K.
$$

A morphism from $(A,B)$ to $(A',B')$ is a stochastic map $F:Z\rightsquigarrow Z'$ satisfying

$$
A'=AF,\qquad B=FB'.
\tag{6}
$$

Such maps preserve the one-step observable channel.

This category does have universal objects\:

$$
(P,I_P,K)
\quad\text{is initial},
$$

and

$$
(Y,K,I_Y)
\quad\text{is terminal}.
$$

The unique maps are respectively $A$ and $B$\. These are the trivial domain and codomain factorizations of an arrow.

They do not characterize minimum hidden-state cardinality. In general, the initial object has $|P|$ states and the terminal object has $|Y|$, either of which may substantially exceed $k_{\mathrm{lat}}(K)$\.

In particular, cardinality minimization is not an image-factorization universal property.

### 4.2 Explicit nonuniqueness at minimum cardinality

Take

$$
K=
\begin{pmatrix}
4/5&1/5\\
1/5&4/5
\end{pmatrix}.
\tag{7}
$$

It has two distinct rows, so $k_{\mathrm{lat}}=2$\.

Two factorizations are

$$
\begin{array}{lll}
\text{I:}&A_1=I_2,&B_1=K,\\[2pt]
\text{II:}&A_2=K,&B_2=I_2.
\end{array}
$$

Both have two hidden states and reproduce $K$ exactly.

They are not isomorphic as latent factorizations. An isomorphism in $\mathbf{FinStoch}$ must be a permutation of the hidden states. No permutation transforms $A_1=I_2$ into $A_2=K$\.

Indeed, there is a continuum of minimum-cardinality factorizations: choose latent Bernoulli success probabilities

$$
0\leq a\leq\tfrac15,
\qquad
\tfrac45\leq b\leq1,
$$

and represent the observed success probabilities $1/5$ and $4/5$ as mixtures of $a,b$\. With $a<b$, the mixture coefficient for a target probability $p$ is

$$
\lambda_p=\frac{p-a}{b-a}.
$$

Different pairs $(a,b)$ generally give non-isomorphic two-state factorizations.

So neither observational equivalence nor minimum cardinality selects a canonical latent mechanism.

### 4.3 A latent factorization need not be a realization of the convex image

Return to matrix (1), for which $k_{\mathrm{lat}}=4$\.

One minimum factorization is

$$
A=I_4,\qquad B=K.
$$

It assigns distinct pure latent states to the four preparations. But the observations satisfy the affine relation

$$
\frac12(r_1+r_3)
=
\frac12(r_2+r_4).
\tag{8}
$$

Both sides are the uniform output distribution.

The two corresponding distributions over hidden states,

$$
\frac12(\delta_{z_1}+\delta_{z_3}),
\qquad
\frac12(\delta_{z_2}+\delta_{z_4}),
$$

are different.

Therefore there is no affine map

$$
C_K\longrightarrow\Delta(Z)
$$

that sends every observed profile $r_p$ to its designated latent distribution $A(p,-)$\.

Such a map would have to assign two different values to the same convex mixture.

This is a failure of a canonical comparison in the intended direction. There remains a surjective affine map

$$
\operatorname{conv}\{A(p,-):p\in P\}
\twoheadrightarrow C_K
$$

induced by the decoder $B$\. It need not be injective.

That is the general relationship\:

$$
\boxed{
\text{reachable latent distributions}
\twoheadrightarrow
\text{observable convex realization}.
}
\tag{9}
$$

The map is canonical given a chosen latent factorization\. The latent factorization itself is not canonically determined.

The obstruction to reversing it is precisely failure of the decoder to distinguish distributions on the reachable latent space.

## 5\. A fourth finite example: convex vertices do not determine latent cardinality

Even counting the extreme points of $C_K$ does not generally recover the minimum latent-state count.

Consider the single-test stochastic matrix

$$
K_\square=
\frac1{12}
\begin{pmatrix}
5&4&3\\
5&2&5\\
3&6&3\\
3&4&5
\end{pmatrix}.
\tag{10}
$$

Its four rows are distinct. They form a nondegenerate parallelogram in the two-dimensional simplex $\Delta(\{1,2,3\})$\. In particular, the first and fourth rows have the same midpoint as the second and third, and the two independent edge directions span a plane.

Thus

$$
|Q_{K_\square}|=4,
\qquad
|\operatorname{Ext}(C_{K_\square})|=4.
$$

But its ordinary rank is three. Since it has only three output outcomes, the factorization

$$
K_\square=K_\square I_3
$$

uses three latent states. The rank lower bound makes this optimal\:

$$
k_{\mathrm{lat}}(K_\square)=3.
$$

The latent states in this factorization are the three pure output distributions-the vertices of the ambient simplex. They are outside the observed parallelogram.

Consequently,

$$
\boxed{
\text{minimum latent cardinality}
\neq
\text{number of extreme observed profiles}.
}
$$

This is another obstruction to treating latent realization as simply a different presentation of the convex image.

## 6\. Context compatibility breaks differently for behavioral and convex realizations

The deterministic Boolean theorem relied on context actions descending through the observational quotient. In the stochastic setting, this splits into two non-equivalent preservation requirements.

### 6.1 Behavioral realization requires strong lumpability

Let $q:P\to Q_K$ be the deterministic row-profile quotient and $c:P\rightsquigarrow P$ a stochastic context.

To obtain a genuine induced stochastic transition

$$
\bar c:Q_K\rightsquigarrow Q_K
$$

making the state-reduction square commute, one needs

$$
\boxed{
q(p)=q(p')
\Longrightarrow
q_*c(-\mid p)=q_*c(-\mid p').
}
\tag{11}
$$

This condition is necessary and sufficient: the common pushforward distribution defines $\bar c$\.

It is the familiar strong lumpability requirement for a stochastic state abstraction.

Equation (2), which only requires observational compatibility, does not imply (11).

#### Explicit counterexample

Take one binary test and five preparations

$$
P=\{a,b,u,v,w\}.
$$

Let their outcome-$1$ probabilities be

$$
h(a)=h(b)=h(u)=\tfrac12,\qquad
h(v)=0,\qquad h(w)=1.
$$

The behavioral quotient has three states\:

$$
M=\{a,b,u\},\qquad V=\{v\},\qquad W=\{w\}.
$$

Define a stochastic context by

$$
\begin{aligned}
c(a)&=\delta_u,\\
c(b)&=\tfrac12\delta_v+\tfrac12\delta_w,\\
c(u)&=\delta_u,\\
c(v)&=\delta_v,\\
c(w)&=\delta_w.
\end{aligned}
$$

Direct calculation gives

$$
h\circ c=h.
$$

Thus $c$ is observationally compatible, with the identity test reindexing. Its powers are compatible as well, so it can be included in a composition-closed class of admissible contexts.

Yet

$$
q_*c(a)=\delta_M,
$$

while

$$
q_*c(b)=\tfrac12\delta_V+\tfrac12\delta_W.
$$

Since $q(a)=q(b)$, condition (11) fails.

No $\bar c$ makes

$$
q\circ c=\bar c\circ q
$$

commute.

The behavioral quotient still reproduces every selected test law. What fails is preservation of the stochastic state transition. The same outcome distribution can arise from different distributions over observable successor states.

### 6.2 Convex realization requires preservation of affine relations

Let

$$
R:\Delta(P)\to C_K,
\qquad R(\pi)=\sum_p\pi(p)r_p.
$$

A stochastic context induces an affine map

$$
c_*:\Delta(P)\to\Delta(P).
$$

There exists an affine context action

$$
\widetilde c:C_K\to C_K,
\qquad
\widetilde c R=Rc_*,
$$

if and only if

$$
\boxed{
R(\pi)=R(\pi')
\Longrightarrow
Rc_*(\pi)=Rc_*(\pi')
}
\tag{12}
$$

for all distributions $\pi,\pi'$ on $P$\.

Necessity is immediate. For sufficiency, define

$$
\widetilde c(R(\pi))=R(c_*\pi).
$$

Condition (12) makes the definition independent of the chosen representative, and the resulting map is affine.

Equivalently, the linear extension of $R$ must have a kernel invariant under $c_*$\.

This is stronger than preserving equality between individual row profiles, because it also preserves all relations among mixtures.

In the preceding five-preparation counterexample, (12) does hold: $Rc_*=R$, so $\widetilde c$ is the identity on the convex interval.

Thus the same stochastic context acts perfectly well on the convex realization but does not descend through the behavioral quotient as a Markov transition.

This is a concrete separation between the doctrines.

### 6.3 The reverse separation also occurs

Return to the three response profiles in Section 3\:

$$
r_L=(0,1),\qquad
r_M=\tfrac12(r_L+r_R),\qquad
r_R=(1,0).
$$

Define a deterministic state transformation on the behavioral quotient by

$$
g(L)=L,\qquad g(M)=L,\qquad g(R)=R.
$$

It is a legitimate transformation of the three distinct behavioral states and can be lifted to a deterministic map on preparations.

But an affine extension to $C_K$ is impossible. Such an extension would fix both endpoints, hence their midpoint, while $g$ sends the midpoint to the left endpoint.

In other words, the relation

$$
r_M=\tfrac12r_L+\tfrac12r_R
$$

is not preserved.

This $g$ is not among the original admissible test-compatible contexts. Declaring it admissible would require enlarging the tests or changing the structural contract. That is the obstruction: behaviorally admissible state operations do not automatically become admissible affine operations.

### 6.4 A useful sufficient condition

If the distinct behavioral profiles are affinely independent, the map

$$
\Delta(Q_K)\longrightarrow C_K
$$

is injective. In that case, an observationally compatible stochastic context satisfying (2) necessarily satisfies strong lumpability.

The reason is that observational compatibility determines the response mixture after applying $c$, while affine independence makes the probability distribution over $Q_K$ uniquely recoverable from that mixture.

This is a finite form of tomographic completeness for distributions over behavioral states\.

The condition is sufficient, not generally necessary for a particular context.

It also exposes the origin of the obstruction: when the observed response profiles satisfy affine dependencies, tests can fail to distinguish different distributions over otherwise distinct behavioral states.

## 7\. Sequential and parallel composition

There is an important difference between preserving an observable channel under composition and preserving its minimum realization\.

### 7.1 Sequential composition

For ordinary kernels

$$
K:P\rightsquigarrow Y,\qquad
L:Y\rightsquigarrow O,
$$

postprocessing gives $KL:P\rightsquigarrow O$\.

Behavioral realization has a canonical surjection

$$
Q_K\twoheadrightarrow Q_{KL},
$$

because equal rows of $K$ remain equal after $L$\.

Convex realization has a canonical affine surjection

$$
C_K\twoheadrightarrow C_{KL},
\qquad
\mu\longmapsto\mu L.
$$

The latent cardinalities satisfy

$$
\operatorname{rank}_+(KL)
\leq
\min\{\operatorname{rank}_+(K),\operatorname{rank}_+(L)\},
$$

since either factorization can be composed with the remaining kernel.

But minimum cardinality need not be preserved.

Consider

$$
K=
\begin{pmatrix}
1/2&1/2&0\\
0&0&1
\end{pmatrix},
\qquad
L=
\begin{pmatrix}
1&0\\
0&1\\
1/2&1/2
\end{pmatrix}.
$$

Both have nonnegative rank two, whereas

$$
KL=
\begin{pmatrix}
1/2&1/2\\
1/2&1/2
\end{pmatrix}
$$

has nonnegative rank one.

Thus

$$
k_{\mathrm{lat}}(K)=2,\quad
k_{\mathrm{lat}}(L)=2,\quad
k_{\mathrm{lat}}(KL)=1.
$$

Composing valid minimal latent representations produces a valid factorization, but it need not remain minimal.

The convex comparison does survive this particular operation because stochastic output postprocessing is affine. This is closely related to the Blackwell garbling order on statistical experiments: postprocessing cannot create distinctions between input states that the original experiment lacked.

### 7.2 Parallel composition

For independent systems, $\mathbf{FinStoch}$ has the tensor

$$
K\otimes L,
$$

given by the Kronecker product of stochastic matrices.

Assume all preparation pairs and joint output measurements are admitted. Then

$$
Q_{K\otimes L}\cong Q_K\times Q_L,
$$

because the two marginals of a product distribution recover the component distributions.

For convex realizations, however,

$$
C_{K\otimes L}
=
\operatorname{conv}
\{r_p\otimes s_q:p\in P,\ q\in Q\}.
\tag{13}
$$

This is the convex hull generated by tensor-product profiles, not the Cartesian product $C_K\times C_L$\.

For example, when $K=L=I_2$,

$$
C_K=C_L=\Delta(2),
\qquad
C_{K\otimes L}=\Delta(4).
$$

The Cartesian product of the local convex realizations is a square of dimension two. The global convex realization is a tetrahedron of dimension three.

It includes distributions such as

$$
\tfrac12\delta_{00}+\tfrac12\delta_{11},
$$

whose marginals are both uniform but whose outputs are correlated.

There is no inconsistency: the tensor of individual deterministic preparations is independent, but freely allowing shared randomized mixtures of pairs introduces correlated global preparations.

The appropriate convex operation must preserve this joint information. A Cartesian product of marginal distributions does not.

For latent realizations,

$$
\operatorname{rank}_+(K\otimes L)
\leq
\operatorname{rank}_+(K)\operatorname{rank}_+(L).
$$

Taking tensor products of local factorizations proves the inequality.

Equality does not hold in general.

An explicit family given by Vandaele, Gillis, Glineur, and Tuyttens is the row-stochastic matrix

$$
K_a=\frac14
\begin{pmatrix}
1+a&1-a&1-a&1+a\\
1-a&1+a&1+a&1-a\\
1+a&1+a&1-a&1-a\\
1-a&1-a&1+a&1+a
\end{pmatrix}.
$$

For $a=\sqrt2-\frac9{10}$, they report an exact nonnegative factorization of the Kronecker square using at most twelve factors, while the original matrix has nonnegative rank four. Hence their reported construction yields

$$
\operatorname{rank}_+(K_a\otimes K_a)
\leq12<16
=
\operatorname{rank}_+(K_a)^2.
$$

The twelve-factor bound is taken from their published factorization result, rather than independently reconstructed here.

Thus a joint hidden-state realization can be smaller than the product of the minimum local hidden-state spaces.

If the modeling doctrine requires hidden states to retain a separated product decomposition, that smaller joint factorization may be inadmissible. The permitted latent architecture is therefore part of the reconstruction problem.

## 8\. Individual-test marginals do not determine joint observation laws

This is the most consequential limitation for world modeling.

Take two binary tests $a,b$, and six preparations

$$
P=\{p_{00},p_{01},p_{10},p_{11},u,v\}.
$$

Give $p_{ij}$ deterministic response probabilities $i,j$ for the two tests. Let both $u,v$ have marginal success probabilities $(1/2,1/2)$\.

The response profiles are therefore

$$
(0,0),\ (0,1),\ (1,0),\ (1,1),\
(1/2,1/2),\ (1/2,1/2).
$$

Under single-test observations\:

$$
|Q_K|=5,\qquad
C_K=[0,1]^2.
$$

The minimum latent cardinality is four. All four corners of the ambient square must be represented by distinct latent archetypes: an extreme point cannot be obtained as a nontrivial convex combination of other admissible profiles. Four archetypes also suffice.

Choose the four hidden states $z_{ij}$, each returning $i,j$ deterministically under the respective tests. Define

$$
\alpha(-\mid u)
=
\tfrac12\delta_{z_{00}}+
\tfrac12\delta_{z_{11}},
$$

and

$$
\alpha(-\mid v)
=
\tfrac12\delta_{z_{01}}+
\tfrac12\delta_{z_{10}}.
$$

Both reproduce the same individual-test laws.

But the latent distributions differ. Since $u\sim_K v$, this minimum-cardinality latent realization does not factor through the behavioral quotient at the preparation-to-latent stage\:

$$
\alpha\neq Fq
$$

for every stochastic $F:Q_K\rightsquigarrow Z$\.

If both tests can be applied to the same sampled latent state, their joint laws are\:

$$
\begin{aligned}
J_u&=\tfrac12\delta_{00}+\tfrac12\delta_{11},\\
J_v&=\tfrac12\delta_{01}+\tfrac12\delta_{10}.
\end{aligned}
$$

They are maximally distinguishable by the parity of the two outcomes, despite having identical individual-test marginals.

Under this enlarged joint-testing interface,

$$
u\not\sim_J v.
$$

The joint observable response table has six distinct rows rather than five, and its convex image is the full simplex $\Delta(4)$, not the square of marginal success probabilities.

This is not evidence that the original observational quotient was wrong. It was correct for the specified single-test interface. The new experiment is strictly stronger.

There is also no warrant to assume that the two tests can be jointly performed. If they are mutually exclusive or disturb the state, a joint measurement protocol must be specified rather than inferred from the marginal table.

### 8.1 Nonunique minimal latent models can disagree under wiring

The two minimum factorizations of matrix (7) provide an even more direct demonstration.

Recall

$$
K=
\begin{pmatrix}
4/5&1/5\\
1/5&4/5
\end{pmatrix},
$$

and the two hidden-state realizations\:

$$
(A_1,B_1)=(I_2,K),
\qquad
(A_2,B_2)=(K,I_2).
$$

Suppose the wiring copies the realized hidden state and applies the output decoder independently to both copies.

For the first preparation, model I fixes the hidden state and performs two independent stochastic output computations. Consequently,

$$
P_{\mathrm I}(Y_1=Y_2=1)=\frac1{25},
$$

and

$$
P_{\mathrm I}(Y_1\neq Y_2)=\frac8{25}.
$$

Model II samples the hidden bit once and then outputs it twice deterministically\:

$$
P_{\mathrm {II}}(Y_1=Y_2=1)=\frac15,
$$

and

$$
P_{\mathrm {II}}(Y_1\neq Y_2)=0.
$$

Both factor the original $K$ exactly. Both have minimum hidden-state cardinality. But they produce different joint output laws when the internal state is copied.

This is not the same as making two independent invocations of the complete kernel $K$\. Those would yield the same product law for both models. The distinguishing operation explicitly accesses and copies the intermediate state.

### Categorical obstruction

The comparison between the two latent models uses the stochastic map $F=K$\. It satisfies the factorization-morphism conditions (6), but it does not preserve copying\:

$$
\Delta\circ F
\neq
(F\otimes F)\circ\Delta.
$$

This is precisely the failure of $F$ to be deterministic in the Markov-category sense.

A deterministic comparison map preserves copying. A general stochastic comparison map does not. The latter may preserve a single-use observation while failing under a context that duplicates its internal result.

For the specific wiring, the necessary condition is equality of the resulting joint decoder kernels. Requiring the comparison itself to preserve copying is a stronger, general sufficient condition; in $\mathbf{FinStoch}$ it forces determinism.

Therefore, the factorization category with arbitrary stochastic morphisms is not automatically a category of realizations interchangeable under every open-system context. Such morphisms certify equality of the specified one-step channel, not equivalence under all possible interventions on hidden state.

## 9\. Final status of the Boolean theorem

| Claim from the Boolean construction                             | Status in finite stochastic realization                                    |
| --------------------------------------------------------------- | -------------------------------------------------------------------------- |
| Quotient equal observational profiles                           | Survives, relative to the specified test family                            |
| Universal reachable/observable deterministic quotient           | Survives, in the external category of deterministic profile factorizations |
| Quotient automatically inherits stochastic contexts             | Fails; strong lumpability is required                                      |
| Free generation of mixtures                                     | Survives outside $\mathbf{FinStoch}$, in convex spaces                                   |
| Observable affine-image factorization                           | Survives in the finite-dimensional convex setting                          |
| Affine contexts descend automatically from row equality         | Fails; affine-relation preservation is required                            |
| A general epi-mono image factorization inside $\mathbf{FinStoch}$             | Fails, by matrix (1)                                                       |
| Minimum latent cardinality equals an observable image invariant | Fails, by ordinary versus nonnegative rank                                 |
| A canonical minimum latent realization                          | Fails in general; explicit non-isomorphic minima exist                     |
| Stochastic factorization morphisms preserve arbitrary wiring    | Fails; copying provides a counterexample                                   |
| Sequential composition preserves minimum realizations           | Fails                                                                      |
| Parallel composition multiplies minimum latent cardinalities    | Fails in general                                                           |
| Individual-test marginals determine joint behavior              | Fails                                                                      |
| Compatible comparisons under restricted, specified contexts     | Survives conditionally, with the relevant preservation equations           |

### What common mathematics remains?

There is still a common observational starting point\:

$$
K:P\times T\rightsquigarrow Y.
$$

It supports three different operations\:

$$
\begin{aligned}
Q_K
&=\{r_p:p\in P\},
\\[2pt]
C_K
&=\operatorname{conv}\{r_p:p\in P\},
\\[2pt]
k_{\mathrm{lat}}(K)
&=\min\{|Z|:K=\alpha;\beta
\text{ with the stipulated test interface}\}.
\end{aligned}
$$

The first forms a quotient by equality of responses. The second forms a convex image under free mixing. The third optimizes over possible stochastic factorizations, whose hidden generators need not be observed response profiles or vertices of their convex hull.

There is a meaningful common comparison between the first two: behavioral states embed in the convex realization, and their mixture relations determine the latter's affine structure.

For a chosen latent factorization, the convex hull of reachable latent distributions maps surjectively to the observable convex realization. This is a valid comparison, but it does not supply a canonical hidden-state space or a canonical inverse.

Those facts support a structured family of reconstruction doctrines rather than one unrestricted reconstruction theorem.

### Precise surviving theorem

A reasonable stochastic replacement for the earlier theorem is\:

> Given a finite test-indexed stochastic response kernel, behavioral quotienting and convex image formation provide canonical reconstructions relative to their respective deterministic and affine doctrines. A specified context descends to the behavioral Markov state space exactly under the relevant lumpability condition, and descends to the convex image exactly when it preserves all affine observational relations. For latent stochastic factorizations, minimum cardinality exists, but neither uniqueness nor context-compatible comparison follows without additional hypotheses.

That claim is supported by the constructions and counterexamples above.

A stronger statement could be obtained by restricting latent models-for example, imposing an observable decoder, preparation reachability, a prescribed conditional-independence structure, or a fixed interface-composition law. But each restriction changes the admissible factorization problem. Some exclude cardinality-minimal factorizations that were previously allowed.

In particular, requiring the reachable latent-belief representation to map injectively to $C_K$ makes it affinely equivalent to the observable convex realization. That restores an image-type universal property at the level of reachable beliefs, but it does not identify the underlying pure hidden states or make the minimum hidden-state count canonical.

## Conclusion

The stochastic test decisively rejects possibility 1, interpreted as a single free-structure-plus-image construction in $\mathbf{FinStoch}$ that also derives minimum latent stochastic realizations.

It supports possibility 2, but with sharper boundaries than before\:

- Behavioral reconstruction is an observational quotient doctrine.
- Convex reconstruction is a free-mixture and affine-image doctrine.
- Latent stochastic reconstruction is a constrained factorization and optimization doctrine.

They admit nontrivial relationships, but the relationships preserve different invariants. Their compatibility with contexts must be proved at the level of the particular operations admitted.

Possibility 3 remains a serious risk for any larger proposed categorical framework that merely packages these doctrines without deriving additional comparison or obstruction theorems.

The most important mathematical discovery in this stress test is that passing from deterministic to stochastic structure changes the exactness conditions themselves\. Row equality is no longer enough for stochastic state abstraction; convex observational equivalence is not the same as latent equivalence; and equivalence of single-use channels is not equivalence under state copying.

A useful categorical phenomenology therefore cannot treat “same observations,” “same mixtures,” and “same behavior under composition” as a single equivalence relation. Those distinctions are not peripheral complications. They determine whether the reconstruction actually survives use as a world model.


You:
**Does contextual saturation yield a canonical, compositional predictive realization of finite stochastic open systems?**

Work with finite-state controlled stochastic transducers

[\
K_a\longrightarrow\mathcal D(O\times S),\
]

where (a) is an admissible action, (O) is the observation space, and (\mathcal D) is the finite-distribution monad.

Specify a category of experiments, including finite adaptive action–observation protocols, sequential composition, and explicitly typed parallel wiring. Distinguish externally accessible contexts from interventions on hidden state.

Define observational equivalence on histories by equality of all admissible future experimental laws.

Determine:

1. Whether this equivalence is the greatest congruence compatible with the specified tests and contexts, and whether its quotient has a universal property among reachable, observable, or unifilar realizations. Keep these classes distinct.
2. Whether contextual saturation can be characterized by an adjunction, closure operator, codensity construction, or categorical factorization theorem, rather than merely defined as an intersection of equivalence relations.
3. Whether the resulting reconstruction is functorial and preserves sequential and parallel composition. State necessary conditions, not only sufficient ones.
4. How the canonical predictive realization compares with convex belief-state realizations and minimum-cardinality hidden-state realizations. Determine whether comparison maps are canonical, whether they preserve the relevant operational structure, and which maps fail to exist.
5. Whether finite latent-state realizability implies finite predictive-state realizability. If not, characterize the obstruction and its implications for a finitary internal language.
6. Whether there is a nontrivial category of realization doctrines in which contextual saturation and reconstruction satisfy Beck–Chevalley-type compatibility conditions.

**Required counterexample:** Analyze a two-state hidden Markov model with a fixed latent bit (Z\in{0,1}), initially uniform, and conditionally independent Bernoulli observations with success probabilities (1/4) and (3/4). Determine the exact predictive states reachable from finite histories and compare their cardinality with the minimum hidden-state cardinality.

Conclude with the strongest justified theorem, explicit counterexamples, and the minimum additional assumptions needed for stronger results. Do not manufacture a universal construction if full abstraction, finite realization, and compositionality cannot be simultaneously established.

ChatGPT:
## Result

Contextual saturation yields a canonical exact predictive realization for a fixed public experimental interface. It does not, in general, yield a finite realization, nor does reconstruction commute with ordinary state-product composition or observation hiding.

Three claims must remain separate:

- Behavioral compositionality: replacing a component by one with the same complete public experimental laws preserves those laws under admissible external wiring.
- Canonical predictive realization: each behavior has a unique reachable, observable realization whose current state is determined by the observed history.
- Compositional state reconstruction: the canonical state space of a composite is obtained directly from the canonical state spaces of its components.

The first two hold in the setting below. The third requires additional conditions and fails for ordinary serial composition that hides an intermediate observation.

The required example has
$$
\boxed{Q_{\mathrm{predictive}}\cong\mathbb Z,\qquad
|S_{\mathrm{hidden,min}}|=2.}
$$
Moreover, it can be obtained by cascading two finite, history-determined unifilar machines. Thus exact predictive realization leaves the finite-state category even when the components individually have finite predictive realizations.

The construction below uses finite histories from a specified initial distribution, not stationary semi-infinite pasts. That distinction prevents an incorrect appeal to minimality statements about stationary $\epsilon$-machines. The relevant existing categorical machinery includes filtering adjunctions, final coalgebras of unifilar machines, and coalgebraic minimization; the precise finite-history claims are established below. ([arXiv](https://arxiv.org/html/2305.02826))

---

## 1. Systems and the experimental interface

### 1.1 Controlled transducers

Fix nonempty finite sets $A,O,S$, an initial distribution $\mu\in\mathcal D(S)$, and kernels
$$
K_a:S\longrightarrow\mathcal D(O\times S),\qquad a\in A.
$$

An action is chosen, an observation is returned, and the hidden state changes. Write
$$
M_{a,o}(s,s')=K_a(o,s'\mid s).
$$
These are substochastic matrices satisfying
$$
\sum_{o\in O}M_{a,o}\mathbf 1=\mathbf 1.
$$

All actions are assumed available at every state. State-dependent availability would have to be included in the observable interface.

### 1.2 A category of finite experiments

For a finite list $I$ of named public interfaces $A_i\Rightarrow O_i$, define $\mathsf{Exp}_I$ as follows.

Its objects are finite classical data types. An arrow $X\to Y$ is a finite, well-founded probabilistic protocol with input $X$, built from classical stochastic operations, calls to a named interface, branching on returned observations, and termination with a value in $Y$.

Sequential composition substitutes the second protocol at the leaves of the first. The system instance persists between calls: composition does not reset it.

Given transducers implementing the interfaces, a protocol has semantics
$$
\llbracket e\rrbracket:
X\times\prod_{i\in I}S_i
\longrightarrow
\mathcal D\!\left(Y\times\prod_{i\in I}S_i\right).
$$

For disjoint resource lists $I,J$, parallel composition has the explicit type
$$
\mathsf{Exp}_I(X,Y)\times\mathsf{Exp}_J(X',Y')
\longrightarrow
\mathsf{Exp}_{I\sqcup J}(X\times X',Y\times Y').
$$
It uses independent system instances and independent initialization unless a joint preparation is supplied explicitly. Classical wires may subsequently correlate actions or route observed outputs between components.

This permits finite adaptive protocols and finite acyclic wiring. Feedback is admitted only with an explicit causal delay, or as a bounded protocol unrolled into a finite interaction tree. This is consistent with the distinction between causal process semantics and stateful presentations in categorical stream semantics. ([Logical Methods in Computer Science](https://lmcs.episciences.org/16337))

### 1.3 What is not an external context

The protocol language does not automatically permit reading, resetting, copying, or conditioning on hidden state. Nor does it permit attaching a new component already correlated with that hidden state without supplying the joint preparation.

A hidden-state operation can become admissible by being declared a public action. Its meaning must then be part of the interface contract.

Histories below serve as descriptions of conditional system states. A test cannot distinguish histories merely by asking the controller to print its old transcript. Controller memory and the system’s predictive state are separately typed.

---

## 2. Histories, joint laws, and the greatest predictive congruence

A history is
$$
h=(a_1,o_1)\cdots(a_n,o_n).
$$
Its likelihood is
$$
L(h)=\mu M_{a_1,o_1}\cdots M_{a_n,o_n}\mathbf1.
$$

Let $H$ contain exactly the histories with $L(h)>0$, including the empty history. The posterior is
$$
b_h=
\frac{\mu M_{a_1,o_1}\cdots M_{a_n,o_n}}{L(h)}.
$$

Actions are treated as controlled inputs. Probabilities with which an independent controller happened to select them are not included in this likelihood.

For a future action-observation word $w$, define
$$
B_h(w)=b_hM_w\mathbf1.
$$
This is a joint future trace probability, not a collection of one-time marginals.

Define
$$
h\equiv h'
\quad\Longleftrightarrow\quad
\text{every admissible future protocol has the same result law from }h,h'.
\tag{1}
$$

### Adaptive experiments do not require a stronger equivalence than full trace laws

For this experiment language,
$$
h\equiv h'
\iff
B_h(w)=B_{h'}(w)\quad\text{for every finite }w.
\tag{2}
$$

One direction follows because fixed-action protocols can return their entire observation transcript. Conversely, each leaf probability in a finite adaptive protocol is a controller-dependent coefficient times a joint trace probability. Summing over leaves proves equality for arbitrary adaptive protocols.

This equivalence uses all finite joint laws. Equality of individual-time marginals would not suffice.

### The greatest-congruence theorem

Set
$$
p_h^a(o)=b_hM_{a,o}\mathbf1.
$$
For $p_h^a(o)>0$, appending $(a,o)$ defines the successor history $h(a,o)$.

Call an equivalence relation $R$ on $H$ a predictive congruence when
$$
hRh'\Longrightarrow p_h^a=p_{h'}^a
$$
and
$$
p_h^a(o)>0\Longrightarrow h(a,o)\,R\,h'(a,o).
\tag{3}
$$

Theorem. Relation $\equiv$ is the greatest predictive congruence.

Proof. Equality of all future laws implies equality of the first-observation laws. For a positive-probability branch,
$$
B_{h(a,o)}(w)
=
\frac{B_h((a,o)w)}{p_h^a(o)}.
$$
Thus equivalent histories have equivalent successors. Conversely, induction on protocol depth shows that every relation satisfying (3) preserves all finite experimental laws. ∎

Zero-probability branches are deliberately excluded. Assigning arbitrary successors there would introduce structure unsupported by the observations.

The quotient
$$
Q=H/{\equiv}
$$
has transition data
$$
p_{[h]}^a(o)=p_h^a(o),
\qquad
\delta([h],a,o)=[h(a,o)]
$$
on positive-probability outputs. It is therefore unifilar: given its current predictive state, action, and observation, its next state is determined.

This is a congruence on the history unfolding, not necessarily a lumpable partition of the original hidden-state space.

---

## 3. Saturation has actual universal structure

There are three complementary universal descriptions. They concern different operations and should not be identified.

### 3.1 Saturation of tests and the congruence interior

Finite protocols are freely generated from the primitive calls and classical operations. Closing a family of tests under these operations gives a least context-closed family. Thus test saturation is a closure operator, left adjoint to the inclusion of context-closed test families.

Dually, let $\mathsf{Eq}(H)$ be the poset of equivalence relations, ordered by inclusion, and let $\mathsf{Cong}(H)$ contain the predictive congruences.

The inclusion
$$
i:\mathsf{Cong}(H)\hookrightarrow\mathsf{Eq}(H)
$$
has a right adjoint:
$$
i\dashv\operatorname{Core}.
$$
Here $\operatorname{Core}(R)$ is the greatest predictive congruence contained in $R$. Explicitly, it is the greatest fixed point of
$$
\Phi_R(E)=
R\cap
\left\{
(h,h'):
p_h^a=p_{h'}^a,\
h(a,o)\,E\,h'(a,o)
\text{ on every positive branch}
\right\}.
$$

The adjunction states
$$
C\subseteq R
\iff
C\subseteq\operatorname{Core}(R)
\qquad(C\in\mathsf{Cong}(H)).
$$

In particular,
$$
\equiv=\operatorname{Core}(H\times H).
$$

Thus saturation is a closure on tests but an interior operation on permitted identifications: adding contextual obligations can force previously identified states apart.

### 3.2 A final coalgebra and an image factorization

Consider the set functor
$$
U_{A,O}(X)=
\prod_{a\in A}
\coprod_{p\in\mathcal D(O)}
X^{\operatorname{supp}(p)}.
\tag{4}
$$
Its coalgebras are unifilar machines with output-dependent updates defined only on possible observations.

A final coalgebra is the set $\mathcal B_{A,O}$ of causal stochastic behaviors: normalized, prefix-consistent families
$$
B_n:A^n\longrightarrow\mathcal D(O^n).
$$
Its transition takes the first-output marginal and the corresponding conditional residual behavior. This final-coalgebra description is established for supported stochastic Mealy machines. ([arXiv](https://arxiv.org/html/2607.00034v1))

The history unfolding has a unique behavior morphism
$$
\beta:H\longrightarrow\mathcal B_{A,O},
\qquad h\longmapsto B_h.
$$
Its image factorization is
$$
H\twoheadrightarrow Q\hookrightarrow\mathcal B_{A,O}.
\tag{5}
$$

This is the categorical reconstruction theorem: the predictive machine is the reachable image in the final behavior object. It takes place in a category of set-based unifilar coalgebras, not inside finite-state $\mathbf{FinStoch}$.

### 3.3 Reachability, observability, and unifilarity

Fix an initial behavior $B_\epsilon$. Consider pointed unifilar realizations with a known initial state, deterministic coalgebra morphisms, and that initial behavior.

A realization is reachable when every state occurs after some positive-probability history. It is observable when distinct states have distinct complete future behaviors.

Then:

| Class                                                                      | Universal property                               |
| -------------------------------------------------------------------------- | ------------------------------------------------ |
| All pointed unifilar realizations of the behavior                          | The history unfolding $H$ is initial.           |
| Reachable pointed unifilar realizations                                    | $Q$ is terminal.                                |
| Observable pointed unifilar realizations, possibly with unreachable states | $Q$ is initial.                                 |
| Reachable and observable pointed unifilar realizations                     | $Q$ is unique up to unique pointed isomorphism. |

For example, the unique map from a reachable realization $X$ to $Q$ sends the state reached after $h$ to $[h]$. It is well-defined because the same state cannot have two different future behaviors. Surjectivity follows from reachability.

Equivalently, minimization is a reflection into observable unifilar coalgebras; reachability is a separate restriction. This separation is essential in categorical minimization. ([DROPS](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CALCO.2021.24))

None of these statements says that $Q$ minimizes hidden-state cardinality among randomly initialized generators.

---

## 4. Filtering itself is an adjoint-not merely a convenient implementation

There is also a universal construction before minimization.

Let $\mathsf G_{A,O}$ contain stochastic Mealy machines, allowing arbitrary sets with finitely supported transitions. A morphism $F:S\rightsquigarrow S'$ satisfies
$$
M_{a,o}F=FN_{a,o}.
\tag{6}
$$
In the pointed version, it also satisfies $\mu F=\mu'$.

Let $\mathsf U_{A,O}$ contain unifilar machines with deterministic morphisms. Forgetting unifilarity gives
$$
J:\mathsf U_{A,O}\to\mathsf G_{A,O}.
$$

The belief-machine construction $\mathsf B$ uses state space $\mathcal D(S)$, output probabilities
$$
p_b^a(o)=bM_{a,o}\mathbf1,
$$
and update
$$
\tau_{a,o}(b)=
\frac{bM_{a,o}}{p_b^a(o)}
\qquad\text{when }p_b^a(o)>0.
\tag{7}
$$

For this discrete Mealy setting,
$$
\boxed{J\dashv\mathsf B.}
\tag{8}
$$

The hom-set bijection can be checked directly. A stochastic map from a unifilar machine $X$ to $S$ assigns a belief $f(x)$ to each $x$. The intertwining equation becomes
$$
p_x^a(o)\,f(\delta(x,a,o))
=
f(x)M_{a,o}.
$$
Taking total mass gives equality of output probabilities; dividing on positive branches gives exactly the condition that $x\mapsto f(x)$ is a deterministic morphism into the belief machine.

This is the discrete counterpart of the filtering-adjunction approach; the distinction between output randomness and conditional deterministic updating is load-bearing. ([arXiv](https://arxiv.org/html/2305.02826))

Consequently, the reconstruction pipeline is
$$
\boxed{
\text{generator}
\xrightarrow{\mathsf B}
\text{belief machine}
\xrightarrow{\mathrm{Reach}}
\text{reachable beliefs}
\xrightarrow{\mathrm{Min}}
\text{predictive machine}.
}
\tag{9}
$$

These are a right-adjoint filtering construction, a reachability restriction, and an observable reflection. They are not one undifferentiated image operation.

A codensity description is unnecessary here. No such description is being asserted without a specified probing functor and an accompanying theorem.

---

## 5. Required counterexample: a fixed latent bit

Let
$$
Z\sim\operatorname{Bernoulli}(1/2)
$$
remain fixed. Conditional on $Z$, observations are independent, with
$$
\Pr(Y_t=1\mid Z=0)=\tfrac14,
\qquad
\Pr(Y_t=1\mid Z=1)=\tfrac34.
$$

There is one action.

### 5.1 Exact finite-history predictive states

For a history with $k$ ones and $\ell$ zeros,
$$
\frac{\Pr(Z=1\mid h)}{\Pr(Z=0\mid h)}
=
3^{k-\ell}.
$$

Put $d=k-\ell$. Then
$$
b_d:=\Pr(Z=1\mid h)=\frac{3^d}{1+3^d}.
\tag{10}
$$

Every $d\in\mathbb Z$ is reachable with positive probability. At exactly length $n$, the possible values are
$$
-n,-n+2,\ldots,n.
$$

The next-observation success probability is
$$
r_d
=
\tfrac14+\tfrac12b_d
=
\frac{1+3^{d+1}}{4(1+3^d)}.
\tag{11}
$$
This is strictly increasing in $d$. Hence distinct $d$'s are distinguished by a single next-observation test.

Conversely, equal $d$'s give equal posteriors and therefore equal entire future laws. Thus
$$
\boxed{Q=\mathbb Z.}
$$
The transitions are
$$
d\xrightarrow{\,1\,}d+1,
\qquad
d\xrightarrow{\,0\,}d-1,
$$
with probabilities $r_d$ and $1-r_d$, respectively. The initial predictive state is $0$.

### 5.2 Minimum hidden-state cardinality

Two hidden states suffice by construction. One cannot suffice because
$$
\Pr(Y_1=1)=\tfrac12,
\qquad
\Pr(Y_1=Y_2=1)=\tfrac{5}{16}\neq\tfrac14.
$$
A time-homogeneous one-state generator would produce independent outputs with the same marginal.

Therefore
$$
\boxed{|S_{\mathrm{hidden,min}}|=2<|Q|=\aleph_0.}
$$

The two-state generator is itself unifilar: its hidden state remains $Z$. What it lacks is a known, history-determined initial state. Its initial state is randomly selected and not exactly revealed by any finite history.

This also explains why “minimal unifilar generator” is insufficient terminology here. Unifilar transitions with random initialization and a history-determined predictive realization are different classes.

With an infinite observation past, the empirical frequency identifies $Z$ almost surely. That is a different observation regime from the finite-history problem.

---

## 6. Comparison with belief and convex realizations

Let
$$
B_{\mathrm{reach}}=\{b_h:h\in H\}\subseteq\mathcal D(S).
$$
There is a canonical surjective deterministic morphism
$$
\pi:B_{\mathrm{reach}}\twoheadrightarrow Q,
\qquad
b_h\longmapsto B_h.
\tag{12}
$$

It preserves output laws and Bayesian updates. Its kernel identifies beliefs with identical complete future experimental laws.

It is injective precisely when the admitted experiments separate the reachable beliefs.

### 6.1 The convex object is not generally the predictive state set

For each prior $b$, let $J(b)$ be its complete future behavior. Each trace probability is linear in $b$, so
$$
J:\mathcal D(S)\longrightarrow\mathcal B_{A,O}
$$
is affine when behaviors carry pointwise mixtures.

Its image is the finite-dimensional polytope
$$
C=\operatorname{conv}\{J(\delta_s):s\in S\}.
\tag{13}
$$

But
$$
Q=J(B_{\mathrm{reach}})
$$
need not be convex, finite, or closed. The convex hull of reachable predictive states is another object, and need not equal $C$.

In the fixed-bit example, $C$ is a line segment parameterized by $b\in[0,1]$, whereas
$$
Q=\left\{\frac{3^d}{1+3^d}:d\in\mathbb Z\right\}.
$$
The endpoints correspond to knowing $Z$ exactly; neither is reached by a finite history.

Filtering is not affine with fixed mixing weights:
$$
\tau_{a,o}(\lambda b+(1-\lambda)c)
=
\frac{\lambda p_b^a(o)}
{\lambda p_b^a(o)+(1-\lambda)p_c^a(o)}\tau_{a,o}(b)
+\frac{(1-\lambda)p_c^a(o)}
{\lambda p_b^a(o)+(1-\lambda)p_c^a(o)}\tau_{a,o}(c).
\tag{14}
$$
The observation changes the weights. The joint, unnormalized update is linear; normalization is the extra operation. Categorical Bayes-filter constructions retain precisely this joint-law/conditioning distinction. ([arXiv](https://arxiv.org/html/2401.14669))

### 6.2 Reverse comparisons can fail

There need not be a recursive section $Q\to B_{\mathrm{reach}}$.

For an elementary example, take two hidden states that alternate deterministically while always emitting $0$, initially at the first state. The reachable beliefs alternate between two point masses, but $Q$ has one state. No section of (12) can commute with the update: neither reachable belief is fixed.

More generally, a pointed stochastic machine morphism
$$
Q\rightsquigarrow S
$$
assigning the original initial prior to $q_0$ exists if and only if
$$
h\equiv h'\Longrightarrow b_h=b_{h'}.
\tag{15}
$$
Indeed, its intertwining equations force its value after every history to be the Bayesian posterior. Conversely, when the posterior depends only on the predictive class, those posteriors define the morphism.

Thus such a comparison is canonical when it exists, but does not always exist.

The opposite direction fails in the required HMM. A pointed stochastic morphism $S\rightsquigarrow Q$ would have to send the uniformly distributed initial hidden bit to the point mass at $q_0$. Both hidden states must therefore map to $q_0$. But their next-output probabilities are $1/4$ and $3/4$, while $q_0$'s is $1/2$. The machine-morphism equation is impossible.

The canonical comparison is from reachable beliefs to predictive behavior-not from hidden states directly to predictive states.

---

## 7. Functoriality and composition: what actually survives

### 7.1 Functoriality on joint-law-preserving simulations

For a stochastic simulation $F$ satisfying (6),
$$
b\longmapsto bF
$$
preserves filtering:
$$
\tau'_{a,o}(bF)=\tau_{a,o}(b)F.
\tag{16}
$$
The observation probabilities agree as well.

Conversely, preservation of those probabilities and equation (16) for every prior imply the joint intertwining equation (6). Thus this is an exact necessary-and-sufficient condition, not merely a sufficient simulation rule.

Filtering, reachable restriction, and predictive quotienting are functorial on this category. Initial behavior-preserving morphisms induce canonical isomorphisms between the reachable observable predictive realizations.

Arbitrary stochastic maps between hidden-state spaces do not satisfy these requirements.

### 7.2 Sequential composition of experiments

The quotient $H\to Q$ preserves the joint law of a protocol’s result and its next predictive state. Therefore sequential protocol composition is preserved exactly.

This is stronger than matching a terminal output marginal: it retains the residual state needed by the continuation.

### 7.3 Serial composition of open systems

For
$$
M:A\Rightarrow B,\qquad N:B\Rightarrow C,
$$
the serial composite has kernel
$$
(N\circ M)_a(c,s',t'\mid s,t)
=
\sum_{b\in B}
M_a(b,s'\mid s)\,N_b(c,t'\mid t).
\tag{17}
$$

Its complete causal behavior is determined by the complete behaviors of its components. Replacing either component by an externally equivalent one preserves composite behavior, provided no unmodeled correlation with hidden state is attached.

Thus behavioral semantics is compositional.

But ordinary serial composition does not preserve predictive state spaces.

#### Explicit obstruction

Let $M$ have three predictive states:
$$
\{\mathrm{start},0,1\}.
$$
At its first call it samples a fair bit, emits it, and enters the corresponding state. Thereafter it emits that bit forever. This is a finite, observable, known-initial-state unifilar machine.

Let $N$ be the one-state memoryless channel
$$
\Pr(N(z)=1)=
\begin{cases}
1/4,&z=0,\\
3/4,&z=1.
\end{cases}
$$

Hide the intermediate bit and observe only $N$'s outputs. The composite is exactly the fixed-bit HMM.

Therefore
$$
|Q_M|=3,\qquad |Q_N|=1,
\qquad |Q_{N\circ M}|=\aleph_0.
\tag{18}
$$

Neither a Cartesian product of component predictive states nor any finite quotient of that product can be the exact composite predictor.

The cause is specific: the component state update depends on an intermediate observation that the composite observer does not see.

For the raw product to remain unifilar, the conditional successor pair given current pair, external action, and external observation must be a point mass. For a proposed quotient $q$ of that product, the necessary-and-sufficient condition is that the successor distribution pushed through $q$ be a point mass. These conditions can fail after the sum over $b$ in (17).

### 7.4 Parallel composition

For independent components with product initialization, independent transition randomness, and the full paired transcript retained,
$$
Q_{M\otimes N}
\cong
\operatorname{Reach}(Q_M\times Q_N).
\tag{19}
$$

The joint posterior factors given the complete transcript. The pair of local predictive states is therefore sufficient and recursively updateable. Local experiments separate distinct pairs.

If components can be addressed independently, every pair of reachable local states is reachable, and the right side is the full product. With synchronized calls only, reachability can be a proper subset.

These assumptions are sufficient, but independence is not logically necessary in every particular model. The exact criterion for a proposed statistic $s:H_{\mathrm{global}}\to X$ is:

$$
s(h)=s(h')\Longrightarrow h\equiv_{\mathrm{global}}h',
\tag{20}
$$
together with recursive updateability. It is the canonical realization exactly when its kernel equals global predictive equivalence and all its states are reachable.

Marginal predictive states do not generally determine a joint realization. Two fixed fair bits may satisfy either
$$
(Z_1,Z_2)\sim\tfrac12\delta_{00}+\tfrac12\delta_{11}
$$
or
$$
(Z_1,Z_2)\sim\tfrac12\delta_{01}+\tfrac12\delta_{10}.
$$
The individual component processes are identical in both cases. The first joint observation distinguishes the joint systems perfectly.

A doctrine allowing arbitrary shared preparations therefore needs joint information beyond the component marginals.

### Consequence

Canonical predictive machines can represent a compositional category of behaviors if composition is defined by composing, filtering, and minimizing again. They do not form a finite-state category closed under ordinary serial state-product composition.

That is a legitimate reconstruction-based composition, but it is not a theorem that minimization commutes with the original implementation-level composition.

---

## 8. Finite hidden realizability versus finite predictive realizability

The exact necessary-and-sufficient condition for a finite history-determined predictive realization is
$$
\boxed{|H/{\equiv}|<\infty.}
\tag{21}
$$

This is a finite residual-behavior condition, not a finite hidden-state condition.

The obstruction can be characterized more sharply. Define the observable linear space
$$
W=\operatorname{span}\{M_w\mathbf1:w\text{ a finite trace word}\}
\subseteq\mathbb R^S.
$$
Then
$$
J(b)=J(c)
\iff
(b-c)v=0\quad\text{for every }v\in W.
\tag{22}
$$

The space $W$ has dimension at most $|S|$ and is invariant under every $M_{a,o}$. Hence finitely many trace probabilities can separate all distinguishable beliefs. Nevertheless, the normalized Bayesian updates can generate infinitely many distinct points in that finite-dimensional observable space.

Finite predictive dimension does not imply finitely many predictive states.

For the fixed-bit example, the observable space has dimension two, while posterior odds evolve by multiplication by $3$ or $1/3$. Their reachable normalized orbit is infinite.

Finite predictive realization follows under additional assumptions such as finite residual index, a finite Bayesian-update orbit modulo observational equivalence, or a uniformly finite-memory law. Merely having a finite unifilar generator with random initialization is insufficient.

For an internal language, the distinction is between finitary syntax and finite semantic state spaces. The required predictor has a finite description:
$$
d\in\mathbb Z,\qquad d\mapsto d\pm1,\qquad
\Pr(1\mid d)=\frac{1+3^{d+1}}{4(1+3^d)}.
$$
It requires an unbounded state type, not an infinite program. A finite-state-only language cannot express every exact predictive reconstruction of a finite hidden-state program.

---

## 9. Beck-Chevalley-type compatibility: a nontrivial but restricted family

There is a concrete family of doctrines with genuine comparison structure:

$$
\mathsf G_{A,O}
\;\underset{J}{\overset{\mathsf B}{\rightleftarrows}}\;
\mathsf U_{A,O}
\;\underset{I}{\overset{\mathrm{Min}}{\rightleftarrows}}\;
\mathsf{Obs}_{A,O},
$$
with
$$
J\dashv\mathsf B,\qquad \mathrm{Min}\dashv I,
$$
and a separate reachable-part construction for pointed machines.

The base changes must be specified.

### 9.1 Action translation

An action map
$$
\phi:A\to A'
$$
induces a reduct
$$
r_\phi^*:\mathsf U_{A',O}\to\mathsf U_{A,O}
$$
by interpreting $a$ as $\phi(a)$. The same reduct exists for generators.

Filtering commutes with this reduct:
$$
\boxed{
\mathsf B_{A,O}\,r_\phi^*
\cong
r_\phi^*\,\mathsf B_{A',O}.
}
\tag{23}
$$
Both sides have the same belief space and the same selected Bayesian updates. This is an invertible comparison between the right adjoints in the corresponding forgetful/filtering square.

For minimization there is always a canonical comparison
$$
\kappa_X:
r_\phi^*\mathrm{Min}_{A',O}(X)
\longrightarrow
\mathrm{Min}_{A,O}(r_\phi^*X),
\tag{24}
$$
because equality under all original actions implies equality under the translated actions.

It is an isomorphism exactly when the translated experiments still separate the original behavioral classes. In the pointed case, restrict this assertion to reachable states; commuting reachability additionally requires that no relevant reachable states be lost.

Surjective $\phi$, allowing action aliases, guarantees this exactness for every system. Omitted actions may be redundant in a particular system, but need not be.

Where reducts preserve observability, they restrict to the observable categories. The square of inclusions then has a genuine adjunction mate; its invertibility is the Beck-Chevalley condition. The comparison is coherent under composition because it is uniquely determined on the quotient generators.

#### Finite failure

Take a known initial state that, under action $a$, emits a fair bit and enters state $x_0$ or $x_1$. From either state, $a$ thereafter emits $0$. Another action $b$ reveals whether the state is $x_0$ or $x_1$.

With both actions, the three states are reachable and observable. After restricting to $a$, $x_0,x_1$ merge. Comparison (24) is a noninvertible three-state-to-two-state quotient.

Thus exactness is a real separating condition, not an automatic consequence of having a square.

### 9.2 Output hiding is more obstructive

Output coarsening need not even define a reduct on unifilar machines: the next state may depend on the observation that was hidden.

Consider the fixed-bit generator with a public output $(Z,Y)$, using a known initial “start” state that first selects $Z$. Its predictive realization has three states: start, known $0$, known $1$.

Now apply the deterministic observation map
$$
(Z,Y)\longmapsto Y.
$$
The predictive realization becomes the countably infinite machine of Section 5.

There is no state map induced by forgetting histories
$$
Q_{\mathrm{rich}}\longrightarrow Q_{\mathrm{coarse}}.
$$
For example, rich histories ending after the observations $(1,1)$ and $(1,0)$ both reach the same rich predictive state, “known $Z=1$.” Their coarse histories reach predictive states $d=1$ and $d=-1$, respectively.

The missing operation is conditioning on less information. A coarse posterior is a weighted mixture over compatible rich histories; it is not the rich posterior with an output coordinate deleted.

Output hiding can still be interpreted by
$$
\text{hide outputs}
\;\to\;
\text{filter}
\;\to\;
\text{restrict reachability}
\;\to\;
\text{minimize}.
$$
But that is not a Beck-Chevalley isomorphism between the original state reconstructions.

Therefore a nontrivial indexed family of realization doctrines exists, with exactness theorems for specified changes of experiments and simulations. It does not extend to arbitrary wiring and observation changes with all comparison maps invertible.

---

## 10. Strongest justified theorem

For a finite controlled stochastic transducer with a specified initial distribution, admit all finite adaptive public protocols, record complete joint transcripts, and exclude undeclared hidden-state access and undeclared shared correlations.

Then:

1. Equality of future experimental laws is the greatest congruence on positive-probability histories compatible with one-step laws and continuation.
2. Its quotient is a canonical reachable, observable, known-initial-state unifilar realization. It is the reachable image in the final causal-behavior coalgebra.
3. Filtering, reachability, and observable minimization have distinct universal properties. Together they construct the quotient functorially on joint-law-preserving simulations.
4. The resulting behavior semantics is fully abstract for the specified experiments and compositional under their external wiring.
5. The canonical predictive state space is at most countable for finite action and observation alphabets, but need not be finite-even when a two-state hidden generator exists.
6. State-level compatibility with composition or changes of observation requires additional exactness conditions. Serial hiding can force new belief states; arbitrary coupling invalidates reconstruction from marginal predictors.

The minimum additional conditions are correspondingly specific: finite residual index for finite predictive state; recursive sufficiency for a proposed state abstraction; joint-law determination for parallel reconstruction; and preservation of observational distinctions and reachability for invertible reconstruction/base-change comparisons.

The obstruction is not a general impossibility of combining finite generative models, full behavioral semantics, and composition. Finite hidden-state languages can have all three. What fails is the stronger demand that their canonical, exact, history-determined predictive realizations remain finite and compose by the original state-product operations.

That boundary is sharp: the fixed-bit example proves the finiteness failure, and its realization as a cascade of two finite predictive machines proves the compositional state-reconstruction failure.


You:
Can finite-dimensional Hankel realization be extended to a canonical, positive, compositionally compatible reconstruction theory for controlled stochastic open systems?

For finite-state stochastic transducers, construct the generalized Hankel operator from all admissible preparation–continuation experiments. Determine:

1. Whether its image yields a canonical minimal linear realization, with a universal property among reachable and observable linear representations.
2. Under what conditions this realization admits an invariant positive cone, normalized states, and stochastic transition operators. Is the positive structure canonical? Must it be finitely generated?
3. Whether behavioral minimization, convex belief-state realization, and finite hidden-state realization can be recovered as distinct structures associated with the Hankel realization. Characterize their comparison maps and obstructions.
4. Whether linear realization and its positive refinements are compatible with sequential wiring, observation hiding, independent parallel composition, and explicitly correlated joint preparations. Determine the exact comparison cells and Beck–Chevalley-type conditions.
5. Whether a finite-dimensional but non-finitely generated positive realization can be given a finite symbolic presentation suitable for an internal language, without identifying finite-dimensionality with finite-state cardinality.

ChatGPT:
Yes, provided “positive realization” means an ordered finite-dimensional linear realization-not necessarily a finite hidden-state model-and composition is allowed to include a new reachability/observability reduction.

There is a substantive reconstruction theorem:

$$
\boxed{
\text{experimental laws}
\longmapsto
\text{minimal Hankel space}
+
\text{canonical preparation-generated positive cone}.
}
$$

Its universal property survives. What does not survive automatically is reconstruction into a finite simplex, preservation of the chosen cone under observation hiding, or reconstruction of correlated composites from separately initialized components.

The principal distinctions are:

$$
\text{linear dimension},\qquad
\text{number of predictive states},\qquad
\text{finite generation of a positive cone},\qquad
\text{number of hidden states}.
$$

These are different invariants. The argument below gives explicit examples separating them.

The established antecedents are weighted-automaton realization, observable operator models, and predictive-state representations. Their common linear framework is well developed; the additional positive-realization problem is genuinely extra. ([Journal of Machine Learning Research](https://jmlr.org/papers/v16/thon15a.html))

## 1. Generalized Hankel realization

### 1.1 Fix the experimental interface

Let $A,O,S$ be finite. Use column distributions and write

$$
M_{a,o}(s',s)=K_a(o,s'\mid s),
\qquad
\sum_o \mathbf 1^\top M_{a,o}=\mathbf 1^\top.
$$

Fix the admissible initial preparations. These can be a single distribution $\mu$, or a specified family $(\mu_i)$. Do not silently include all pure hidden states as preparable states.

At a fixed interface cut, let:

- $P$ contain finite preparation protocols, including selected events in their observation transcripts;
- $T$ contain finite continuation protocols with a selected result event.

Protocols may use public actions adaptively, classical randomization, and finite sequential composition. Their semantics retain joint transcript probabilities. Hidden-state copying, resetting, or intervention is excluded unless explicitly exposed as an operation.

Each preparation has an unnormalized state $\alpha_p\in\mathbb R_{\ge0}^{S}$. Each continuation has an effect $\beta_t\in[0,1]^{S}$. Their interaction is

$$
H(p,t)=\beta_t^\top\alpha_p.
\tag{1}
$$

Keeping preparations unnormalized is essential: postselection probabilities remain part of the pairing, and composition remains linear. Conditioning is performed later.

This is a fixed-resource interface. Adding another persistent instance introduces another state wire and generally a tensor-product realization; it is not an operation that duplicates the state at the existing cut.

### 1.2 The Hankel operator

Define

$$
\mathsf H:\mathbb R^{(P)}\longrightarrow\mathbb R^T,
\qquad
\mathsf H(e_p)=H(p,-),
$$

where $\mathbb R^{(P)}$ consists of finitely supported linear combinations. Its image is

$$
V_H=\operatorname{im}\mathsf H
=\operatorname{span}\{H(p,-):p\in P\}.
\tag{2}
$$

Since (1) factors through $\mathbb R^S$,

$$
r:=\dim V_H\le |S|.
$$

Finite adaptive protocols do not increase this bound: their event laws are finite sums of primitive trace laws.

Let $x_p=H(p,-)$. Appending a primitive action-observation event induces

$$
D_{a,o}x_p=x_{p;(a,o)}.
\tag{3}
$$

This is well-defined. A linear relation between preparation profiles remains a relation after appending $(a,o)$, because testing the new profile is equivalent to testing the old one with the continuation prefixed by $(a,o)$.

Let $u(x)=x(\epsilon)$, where $\epsilon$ is the discard/empty continuation. Then

$$
\sum_o uD_{a,o}=u.
\tag{4}
$$

For a single initial preparation, write $x_0=H(\epsilon,-)$. The complete controlled trace law is

$$
\Pr(o_1,\ldots,o_n\mid a_1,\ldots,a_n)
=
uD_{a_n,o_n}\cdots D_{a_1,o_1}x_0.
\tag{5}
$$

The construction is coordinate-free. A finite matrix presentation requires a basis, which is not canonical.

### 1.3 Universal property

A linear representation consists of a vector space $W$, operators $L_{a,o}$, preparation vectors $w_i$, and a functional $v$, realizing the same experiments.

Morphisms are linear maps preserving preparation vectors, intertwining every operator, and preserving the terminal functional.

A representation is:

- linearly reachable when its preparation-orbit vectors span $W$;
- observable when its continuation effects separate $W$.

Then:

> Hankel image theorem. $V_H$ is terminal among linearly reachable representations of the given laws and initial among observable representations. It is the unique reachable and observable representation, up to unique representation isomorphism. Every linear representation has dimension at least $r$.

For a reachable $W$, the unique map $W\to V_H$ sends each state to its continuation profile. For an observable $W$, the assignment $x_p\mapsto w_p$ is well-defined: any relation among the $x_p$ gives an observationally zero vector in $W$, hence the zero vector.

This is the linear instance of the initial-to-terminal factorization account of automata minimization. ([Logical Methods in Computer Science](https://lmcs.episciences.org/6213))

So the answer to question 1 is affirmative. The assumptions that do the work are linear closure of preparations, closure of tests under continuation, and a sufficiently complete observational interface.

---

## 2. Positive structure: canonical bounds, and a canonical generated realization

Linear minimality does not determine which vectors should count as positive states. There are, however, two canonical extremal cones.

Write $e_t(x)=x(t)$. Define

$$
C_-=
\overline{\operatorname{cone}\{x_p:p\in P\}},
\tag{6}
$$

and

$$
C_+=
\{x\in V_H:e_t(x)\ge0\text{ for every admissible event test }t\}.
\tag{7}
$$

The closure in (6) is a declared convention: it admits limits of finite mixtures and rescalings. Without that convention, the algebraically generated cone need not be closed.

### 2.1 What is derived

Both cones are invariant:

$$
D_{a,o}C_\pm\subseteq C_\pm.
\tag{8}
$$

For $C_-$, this follows from appending events to preparations. For $C_+$, it follows from prefixing tests.

They are pointed. If both $x$ and $-x$ lie in $C_+$, every test vanishes on $x$, so observability gives $x=0$.

Moreover,

$$
u(x)>0\qquad(x\in C_+\setminus\{0\}).
\tag{9}
$$

Indeed, an event test has an admissible complement, so

$$
0\le e_t(x)\le u(x).
$$

If $u(x)=0$, all tests vanish. Since finitely many tests span $V_H^*$, this also proves that

$$
\Omega_\pm=\{x\in C_\pm:u(x)=1\}
$$

are compact convex sets.

The operators form a positive instrument. On a normalized state $x$,

$$
p(o\mid a,x)=uD_{a,o}x,
$$

and, on a positive-probability branch,

$$
x'=\frac{D_{a,o}x}{uD_{a,o}x}.
\tag{10}
$$

The branch operators are linear and subnormalized; the conditional update is nonlinear.

### 2.2 Which positive cones are admissible?

A closed positive realization on the minimal linear space consists of a closed convex cone $C$ such that

$$
C_-\subseteq C\subseteq C_+,
\qquad
D_{a,o}C\subseteq C.
\tag{11}
$$

Thus $C_-$ is the least admissible closed cone and $C_+$ the greatest. Intermediate invariant cones form a complete lattice under intersection and closed conic generation.

This yields a precise answer about canonicity:

- The preparation-generated cone is canonical.
- The test-positive cone is canonical.
- The observations force a unique admissible closed cone exactly when $C_-=C_+$.
- Otherwise choosing the full positive state space requires a doctrine: generated states, all observationally consistent states, or some intermediate physical state space.

The minimal/maximal invariant-cone distinction is an established part of positive stochastic realization theory. ([Springer Link](https://link.springer.com/article/10.1007/s00220-023-04913-4))

### 2.3 A positive universal property really does survive

Consider finite-dimensional ordered linear representations with closed generating cones, strictly positive normalization functional, positive branch operators, and positive representation morphisms.

Call such a representation conically reachable when its cone is the closed conic hull of its actual preparation-orbit vectors.

Then:

> Positive generated-realization theorem.  
> $(V_H,C_-)$ is terminal among conically reachable positive representations of the given experimental laws and initial among observable positive representations.

The linear maps in the Hankel image theorem are positive because they send preparation generators to preparation generators and commute with finite conic combinations and limits.

This is stronger than merely placing different models in a common framework. It supplies a unique comparison map.

But conical reachability is stronger than linear reachability. A finite hidden-state model may be linearly reachable while allowing positive states that cannot be approximated by mixtures of accessible preparations.

### 2.4 When does a finite hidden-state realization exist?

For a finite-rank stochastic behavior, the following criterion holds:

$$
\boxed{
\text{finite hidden-state realization}
\iff
\text{an invariant polyhedral cone }C
\text{ satisfying (11) exists}.
}
\tag{12}
$$

The controlled statement can be proved directly.

Sufficiency. Choose generators $c_1,\ldots,c_m$ with $u(c_j)=1$. Positivity allows

$$
D_{a,o}c_j=\sum_i N_{a,o}(i,j)c_i,
\qquad N_{a,o}(i,j)\ge0.
$$

Applying $u$ and summing over $o$ gives

$$
\sum_{o,i}N_{a,o}(i,j)=1.
$$

Thus $N_{a,o}$ define an $m$-state stochastic transducer. Decompose each initial preparation in the same generators.

Necessity. Given a finite hidden-state model, let

$$
R=\operatorname{span}\{\alpha_p:p\in P\}\subseteq\mathbb R^S
$$

and let $\pi:R\twoheadrightarrow V_H$ be its observation map. Then

$$
C=\pi(R\cap\mathbb R_{\ge0}^{S})
\tag{13}
$$

is polyhedral, invariant, and lies between $C_-$ and $C_+$.

This is the controlled version of the classical invariant-polyhedral-cone criterion for positive realization. ([The Australian National University](https://researchportalplus.anu.edu.au/en/publications/realization-problem-for-hidden-markov-models/))

Several qualifications matter.

First, the canonical $C_-$ need not be polyhedral even when a polyhedral $C$ exists.

Second, a polyhedral cone supplies a finite hidden realization, but the nonnegative decompositions of its transformed generators need not be unique.

Third, the minimum hidden-state count is not simply “the number of rays of the canonical cone.” General hidden realizations can involve positive lifts and nontrivial reachable subspaces before taking the observational quotient.

A particularly clean exact condition is:

$$
\text{an }r\text{-state stochastic realization exists}
\iff
\text{an admissible invariant simplicial cone exists in }V_H.
\tag{14}
$$

A simplicial cone provides a positive basis. Conversely, an $r$-state realization of Hankel rank $r$ is linearly reachable and observable, so its orthant transfers to such a cone.

Finite rank alone does not imply finite hidden-state realizability. There are finite-rank stochastic processes with no invariant polyhedral realization cone. That limitation concerns extensions beyond the finite-hidden-state input class specified in the question. ([Springer Link](https://link.springer.com/article/10.1007/s00220-023-04913-4))

---

## 3. Behavioral, convex, and hidden-state realizations are different structures

For a positive-probability history $h$, define

$$
q_h=\frac{x_h}{u(x_h)}.
$$

### 3.1 Predictive states

The canonical behavioral state set is

$$
Q=\{q_h:h\text{ admissible and }u(x_h)>0\}.
\tag{15}
$$

Equality in $Q$ is equality of all conditional future laws. The update is the normalization in (10).

This is a subset of a finite-dimensional space, not generally a finite set.

### 3.2 The canonical convex realization

Its closed convex completion is

$$
\Omega_-=
\overline{\operatorname{conv}Q}.
\tag{16}
$$

Thus the least positive Hankel realization is the closed convex completion of the predictive states, with unnormalized linear instruments supplying its dynamics.

For a particular hidden model, reachable Bayesian beliefs $b_h$ map canonically to predictive states:

$$
b_h\longmapsto q_h.
$$

The map extends affinely to the closed convex hull of reachable beliefs, and it commutes with conditioning wherever the observation probability is positive.

It need not be injective. An inverse requires the relevant beliefs to be observationally separated; a recursively compatible choice of representatives requires more than a set-theoretic section.

There is also a scope issue: if the hidden model is not linearly reachable, the observation map into $V_H$ is canonically defined on $R$, not necessarily on its entire hidden-state vector space. Allowing arbitrary hidden priors can enlarge the preparation interface and therefore enlarge the Hankel space.

### 3.3 Finite hidden-state realizations

These are positive lifts of the observable dynamics. They are not recovered by enumerating the points of $Q$, nor generally by taking the vertices of $\Omega_-$.

The earlier fixed-bit example makes the first distinction exact. With success probabilities $1/4$ and $3/4$,

$$
Q=
\left\{
\left(
\frac1{1+3^d},
\frac{3^d}{1+3^d}
\right):d\in\mathbb Z
\right\}.
$$

But the Hankel rank is two: the minor using histories and continuations $\epsilon,1$ is

$$
\det
\begin{pmatrix}
1&1/2\\
1/2&5/16
\end{pmatrix}
=\frac1{16}.
$$

The two-state generator gives the matching upper bound. Here $C_-=C_+=\mathbb R_{\ge0}^2$, yet there are countably infinitely many reachable predictive states.

Linear dimension and hidden-state cardinality can also differ. Consider the preparation-observation table

$$
K=\frac12
\begin{pmatrix}
0&0&1&1\\
1&0&0&1\\
1&1&0&0\\
0&1&1&0
\end{pmatrix}.
\tag{17}
$$

It has ordinary rank three and nonnegative rank four. The latter follows because each nonnegative rank-one summand can cover at most two of its eight positive entries.

Realize this as a transducer with four named preparations, using $K$ for the next output and resetting afterward to the uniform mixture of preparations. Its full Hankel rank remains three, while any hidden realization needs at least four states because it must factor the one-step table. Four suffice.

The Hankel space, its predictive points, its convex completion, and its finite positive lifts therefore cannot be identified.

---

## 4. A finite-state example with a non-finitely generated canonical cone

This example answers the finite-generation and symbolic-presentation questions without leaving the finite-hidden-state setting.

Take three hidden states, initial distribution

$$
\mu=\frac13(1,1,1)^\top,
$$

and two observations $c,r$. Let

$$
D=
\begin{pmatrix}
1&0&0\\
0&1/2&0\\
0&0&1/4
\end{pmatrix},
\qquad
E=
\mu
\begin{pmatrix}
0&1/2&3/4
\end{pmatrix},
\tag{18}
$$

with $u=(1,1,1)$.

Interpret $c$ as continuing in the same state and $r$ as resetting to $\mu$. Since

$$
u(D+E)=u,
$$

this is a stochastic transducer.

The vectors $\mu,D\mu,D^2\mu$ are linearly independent, as are the effects $u,uD,uD^2$. Hence the Hankel rank is exactly three.

### 4.1 The canonical cone has infinitely many exposed rays

After the most recent reset, a history with $n$ continuations has state proportional to

$$
v_n=(1,2^{-n},4^{-n})^\top.
$$

Consequently,

$$
C_-=
\overline{\operatorname{cone}\{v_n:n\ge0\}}.
\tag{19}
$$

Write $t_n=2^{-n}$. The functional

$$
\ell_n(x)=t_n^2x_0-2t_nx_1+x_2
$$

satisfies

$$
\ell_n(v_m)=(t_m-t_n)^2.
$$

It is nonnegative on $C_-$ and vanishes only on the ray through $v_n$. Every $v_n$ therefore generates an exposed ray.

Thus:

$$
\boxed{
\dim V_H=3,\quad
\text{minimum hidden-state count}=3,\quad
C_-\text{ is not finitely generated}.
}
\tag{20}
$$

The finite hidden-state realization uses the larger invariant orthant $\mathbb R_{\ge0}^3$.

### 4.2 A finite symbolic nonpolyhedral positive refinement

There is also an intermediate invariant cone with a finite polynomial presentation:

$$
C_{\mathrm{mom}}
=
\left\{
x:
0\le x_2\le x_1\le x_0,\quad
x_1^2\le x_0x_2
\right\}.
\tag{21}
$$

This is the cone generated by $(1,t,t^2)$ for all $t\in[0,1]$. It is closed, convex, and nonpolyhedral.

Both operators preserve it:

- $D$ sends $t$ to $t/2$;
- $E$ sends every state to a nonnegative multiple of $\mu$.

Therefore

$$
C_-\subsetneq C_{\mathrm{mom}}\subsetneq\mathbb R_{\ge0}^3\subseteq C_+.
\tag{22}
$$

The normalized type

$$
\{x\in\mathbb R^3:x\in C_{\mathrm{mom}},\ u(x)=1\}
$$

and its instrument updates have a finite rational/polynomial presentation.

But $C_{\mathrm{mom}}$ is not the canonical generated cone. It introduces additional states consistent with the chosen positive dynamics.

### 4.3 The exact canonical cone can require a different kind of syntax

Equation (19) is itself a finite symbolic definition using an integer-indexed orbit, conic hull, and closure. Equivalently, $C_-$ is the least closed convex cone containing $\mu$ and invariant under $D,E$.

It is not finitely semialgebraic. In the section $x_0=1$, its lower boundary has infinitely many distinct straight edges connecting consecutive points

$$
(2^{-n},4^{-n}).
$$

A finite polynomial description would put this boundary inside finitely many polynomial zero sets. Covering infinitely many distinct line segments would force one nonzero polynomial to vanish on infinitely many distinct lines, which is impossible.

So there are three different notions:

$$
\text{finite generators}
\neq
\text{finite polynomial description}
\neq
\text{finite recursive/closure description}.
$$

The example has the third for its canonical cone, the second for an intermediate nonpolyhedral cone, and the first for an alternative hidden-state cone.

A finitary internal language can support the canonical construction through refinement types and least-invariant-cone or closure operators. That does not give finite-state semantics or decidable membership for free.

---

## 5. Composition and the exact comparison maps

### 5.1 The general comparison is a reachable-subspace/observable-quotient span

Construct a raw linear realization $X_W$ by some specified wiring $W$. Let its preparation vectors be $x_p^W$, its continuation effects $e_t^W$, and define

$$
R_W=\operatorname{span}\{x_p^W\},
$$

$$
N_W=\{x\in R_W:e_t^W(x)=0\text{ for every continuation }t\}.
$$

The reconstructed space is

$$
V_W=R_W/N_W.
$$

The canonical comparison is

$$
\boxed{
X_W\ \xleftarrow{\;\iota_W\;}\ R_W\
\xrightarrow{\;q_W\;}\ V_W.
}
\tag{23}
$$

There is not necessarily a canonical map $X_W\to V_W$: unreachable vectors have no prescribed image.

The raw and reconstructed linear realizations agree exactly when

$$
\boxed{R_W=X_W,\qquad N_W=0.}
\tag{24}
$$

For the generated positive doctrine, define

$$
C_W^{\mathrm{reach}}
=
\overline{\operatorname{cone}\{x_p^W\}}.
$$

The ordered comparison is

$$
(X_W,C_W^{\mathrm{raw}})
\longleftarrow
(R_W,C_W^{\mathrm{reach}})
\longrightarrow
(V_W,C_{-,W}).
\tag{25}
$$

Thus positive exactness requires more than (24). Under the resulting linear isomorphism, the cones must agree:

$$
C_W^{\mathrm{raw}}=C_W^{\mathrm{reach}}.
\tag{26}
$$

Linear spans can agree while generated cones differ.

### 5.2 Temporal sequencing and serial wiring

Temporal concatenation of experiments is represented exactly by multiplication of the branch operators.

For serially wired transducers

$$
M:A\Rightarrow B,\qquad N:B\Rightarrow C,
$$

the raw state space is $V_M\otimes V_N$, with

$$
D^{N\circ M}_{a,c}
=
\sum_{b\in B}
D^M_{a,b}\otimes D^N_{b,c}.
\tag{27}
$$

This is finite-dimensional and realizes the joint channel law. It preserves the projective positive tensor cone generated by positive simple tensors.

However, the tensor representation need not remain reachable or observable. Nor need its whole positive cone be generated by the preparations accessible through the composite interface.

The exact comparison is therefore (23)-(26), applied to (27).

This is already an improvement over finite predictive-state reconstruction: serial wiring cannot force an infinite linear dimension. It satisfies

$$
\operatorname{rank}H_{N\circ M}
\le
(\operatorname{rank}H_M)(\operatorname{rank}H_N).
$$

But equality, and positive exactness, require the stated additional conditions.

### 5.3 Observation hiding

A stochastic relabeling of observations $\kappa(z\mid a,o)$ gives operators

$$
\widetilde D_{a,z}
=
\sum_o\kappa(z\mid a,o)D_{a,o}.
\tag{28}
$$

The raw space stays the same. Its new reachable span can shrink, and its new unobservable subspace can grow. Hence hiding cannot increase Hankel rank.

It can nevertheless change the canonical positive cone without changing rank.

#### Explicit rank-preserving, cone-changing hiding

Take a two-state hidden chain with transition matrix

$$
P=
\begin{pmatrix}
3/4&1/4\\
1/4&3/4
\end{pmatrix},
\qquad
\mu=(1/2,1/2)^\top.
$$

After transitioning, emit a noisy bit $Y$, with success probabilities $1/4,3/4$ in the two states.

First expose the rich observation $(Z_{\mathrm{new}},Y)$. Pure hidden states are then reachable after observation, so the generated cone is the full orthant.

Now hide $Z_{\mathrm{new}}$. The coarse operators are

$$
N_1=\operatorname{diag}(1/4,3/4)P,
\qquad
N_0=\operatorname{diag}(3/4,1/4)P.
$$

The coarse model is still linearly reachable and observable in dimension two.

But its normalized reachable beliefs $b=\Pr(Z=1)$ have closed convex hull

$$
\left[1-\frac{\sqrt3}{2},\,\frac{\sqrt3}{2}\right].
\tag{29}
$$

To verify this, the one-observation filter maps are

$$
f_1(b)=\frac{3(1+2b)}{2(3+2b)},
\qquad
f_0(b)=\frac{1+2b}{2(5-2b)}.
$$

The interval in (29) is invariant; repeated $1$'s and repeated $0$'s approach its endpoints.

Thus linear reconstruction commutes with this hiding up to the identity on $\mathbb R^2$, while reconstruction of the generated cone does not:

$$
C_{-,\mathrm{coarse}}\subsetneq C_{-,\mathrm{rich}}.
$$

Linear Beck-Chevalley exactness does not imply positive Beck-Chevalley exactness.

### 5.4 Independent parallel composition

For independently initialized components with independent transition randomness and the full paired observation interface,

$$
D^{M\otimes N}_{(a,b),(o,p)}
=
D^M_{a,o}\otimes D^N_{b,p}.
\tag{30}
$$

If the interface permits independent local scheduling-equivalently, enough idle operations to prepare arbitrary pairs of local histories-then

$$
V_{M\otimes N}\cong V_M\otimes V_N.
\tag{31}
$$

Product preparations span the tensor product, and product continuation effects separate it.

For generated cones,

$$
C_{-,M\otimes N}
=
\overline{\operatorname{cone}
\{x\otimes y:x\in C_{-,M},\,y\in C_{-,N}\}}.
\tag{32}
$$

For test-positive cones, the corresponding construction is instead

$$
C_{+,M\otimes N}
=
\{z:(e\otimes f)(z)\ge0
\text{ for all local event effects }e,f\}.
\tag{33}
$$

These are the minimal state-generated and maximal test-compatible tensor constructions, respectively. A choice of intermediate cones needs its own composite-state rule.

Without independent scheduling, (31) can fail. Two deterministic toggles advanced only in lockstep reach only the equal-parity state pairs. Their individually reachable two-dimensional spaces have a four-dimensional tensor product, but the joint reachable span is two-dimensional.

The necessary and sufficient linear conditions remain (24), not independence as a slogan.

### 5.5 Explicitly correlated preparations require additional data

Local laws do not determine a correlated joint initialization.

There is a sharper obstruction than merely failing to know the coupling.

Consider a local two-state machine that:

1. emits its current hidden bit;
2. replaces it with a fresh fair bit.

With a fair initial bit, its public process is i.i.d. fair output and its Hankel rank is one.

Take two such machines, but initialize their hidden bits equally:

$$
(Z_1,Z_2)\sim\tfrac12\delta_{00}+\tfrac12\delta_{11}.
$$

Their first joint output is correlated. Thereafter the independent resets make every joint output uniform on four outcomes.

The joint Hankel rank is two. For instance, using preparations $\epsilon,(00)$ and continuations $\epsilon,(01)$ gives

$$
\begin{pmatrix}
1&0\\
1/2&1/8
\end{pmatrix},
$$
whose determinant is $1/8$.

Therefore

$$
\operatorname{rank}H_1
=
\operatorname{rank}H_2=1,
\qquad
\operatorname{rank}H_{\mathrm{correlated}}=2.
\tag{34}
$$

No joint vector in the one-dimensional tensor product of the two separately reconstructed spaces can represent this correlated initialization.

The remedy is not a different tensor formula on those one-dimensional spaces. The preparation interface must be enlarged so that the local reconstruction retains the distinctions used by the joint preparation.

More generally, a correlated preparation can be transported through local reconstructions only when it descends through their observational reductions. For a joint functional, this means annihilating the relevant local observational kernels; for a concrete state presentation, it must lie in a domain on which the local quotient maps are defined. These are interface-adequacy conditions, not consequences of having correct local marginals.

---

## 6. Exactness and Beck-Chevalley-type conditions

The comparison can be stated directly at the level of observational presentations.

Suppose a protocol translation induces linear maps

$$
\ell:\mathbb R^{(P')}\to\mathbb R^{(P)},
\qquad
r:\mathbb R^T\to\mathbb R^{T'},
$$

and

$$
\mathsf H'=r\,\mathsf H\,\ell.
\tag{35}
$$

For physical protocol translations, the coefficients describing preparation randomization and event aggregation are nonnegative. The maps must also respect continuation composition; an arbitrary factorization of arrays is not enough.

Set

$$
U=\operatorname{im}(\mathsf H\ell)\subseteq V_H.
$$

The canonical comparison is

$$
V_H\longleftarrow U
\xrightarrow{r|_U}V_{H'}.
\tag{36}
$$

It is an isomorphism comparison precisely when

$$
\boxed{
U=V_H,\qquad
\ker(r|_U)=0.
}
\tag{37}
$$

These are preparation spanning and test separation.

For positivity they must be strengthened:

- Generated-cone exactness requires equality of the transported closed conic hulls of preparations-not merely their linear spans.
- Test-positive exactness requires equality of the relevant closed cones of effects-not merely their linear spans.

An invertible linear comparison can fail either test, as the hiding example demonstrates.

There is an actual adjunctional organization behind these criteria. In suitable categories of pointed linear representations:

- reachable restriction is right adjoint to inclusion of reachable representations;
- observable quotienting is left adjoint to inclusion of observable representations.

For ordered representations, replace linear reachability by closed-conic reachability and equip the observable quotient with its image cone. Under the normalization assumptions above, the relevant normalized cone sections are compact, so these quotient cones remain closed.

Where an interface-change functor preserves the corresponding reachable and observable subcategories, these squares have the usual mate comparisons. Their invertibility is the Beck-Chevalley condition. The criteria in (37), together with cone equality, give its concrete content here. The categorical minimization literature supplies the general adjunction/factorization setting; it does not make these preservation conditions automatic. ([Logical Methods in Computer Science](https://lmcs.episciences.org/6213))

The comparison span is therefore meaningful even when exactness fails. It identifies whether the obstruction is:

- loss of reachable directions;
- loss of observable distinctions;
- loss of positive preparation generation;
- or enlargement of the test-compatible positive states.

These are different failures.

### A compositionally compatible reconstruction still exists

After performing raw wiring, restrict to its reachable generated cone and quotient observationally. This produces the canonical positive Hankel realization of the composite.

Different parenthesizations of a causal wiring have the same experimental behavior. Their final reachable-observable realizations therefore have a unique comparison isomorphism, and those isomorphisms are coherent.

So reconstruction supports composition with re-reduction.

It does not generally preserve the raw state-space tensor, the raw cone, or a previously chosen hidden-state presentation. Instantaneous feedback, hidden-state interventions, and arbitrary correlated preparations require further interface structure and cannot be included by declaration.

---

## 7. Consequences for a finitary internal language

A finite symbolic language for these realizations is possible without requiring finite state cardinality.

A suitable model declaration can contain

$$
(V,u,(x_i),(D_{a,o}),C)
$$

with obligations

$$
x_i\in C,\quad u(x_i)=1,\quad
D_{a,o}C\subseteq C,\quad
\sum_o uD_{a,o}=u.
\tag{38}
$$

The cone can be supplied by finite generators, polynomial or conic constraints, a verified abstract cone type, or a least-invariant-cone construction.

These options have different verification costs. The example in Section 4 proves that even a canonical cone arising from rational finite-state matrices need not have a finite polynomial description. A finite recursive definition is not a membership algorithm.

The language should also distinguish:

$$
\text{unnormalized branch state }D_{a,o}x
$$

from

$$
\text{conditional state }
\frac{D_{a,o}x}{uD_{a,o}x}.
$$

The supplied probabilistic-language note makes the related distinction between normalized generative Markov operations and the additional structure needed for scoring or conditioning.

This is an exact-realization theory. It does not establish stable identification from finite noisy data; the method map explicitly separates existence, uniqueness, and stability for this reason.

## Strongest justified conclusion

For a fixed, compositionally closed public experimental interface with finite Hankel rank:

> There is a canonical minimal linear realization and a canonical least closed, preparation-generated positive realization. They are characterized by reachable/observable universal properties. Their normalized states carry stochastic instruments, even when the canonical cone is not finitely generated.

For finite hidden-state input systems, at least one invariant polyhedral refinement exists, but it need not be canonical or coincide with the generated cone.

Composition is exact at the level of experimental behavior. At the state level it is implemented by raw wiring followed by reachable-cone restriction and observable quotienting. Commutation without re-reduction requires the explicit span, separation, and cone-generation conditions above.

The strongest finite classical conclusion requires more:

$$
\boxed{
\text{invariant simplicial cone}
\Rightarrow
\text{a stochastic realization with }r\text{ hidden states}.
}
$$

If the admissible cone is uniquely forced and simplicial, its normalized extreme rays provide a canonical finite hidden-state presentation up to permutation. Without such conditions, finite hidden-state reconstruction remains a positive-lift problem rather than the Hankel image construction itself.

The resulting theory is genuinely canonical and compositional in an ordered-linear sense. It is not a canonical finite-state latent ontology. Its useful organizing structure is the minimal Hankel representation together with its preparation cone, test cone, admissible positive refinements, and exact comparison maps-not the vector-space dimension alone.


You:
What question should I ask next?

ChatGPT:
Can positive Hankel reconstruction be made statistically identifiable and compositionally stable from finite, noisy experiments-and which parts of exact reconstruction must be abandoned to achieve that?

That is the next question worth asking. Even granting the preceding exact constructions, they start with complete experimental laws. The missing step is:

$$
\text{finite experimental evidence}
\longrightarrow
\text{justified positive realization}
\longrightarrow
\text{certified predictions after composition}.
$$

A canonical reconstruction from an exact law is not yet a method for discovering warranted structure from observations. The method map explicitly distinguishes existence, identifiability, and stability, and requires approximate claims to specify their metric and preservation bounds.

The following prompt would test that gap without presupposing that it can be closed.

---

## Proposed next question

Does positive Hankel realization admit a finite-data, operationally stable reconstruction theory, or does empirical uncertainty require replacing canonical models by families of admissible realizations?

Work initially with finite controlled stochastic transducers and a declared operation that resets the system to its initial distribution. Observations consist of finitely many independent experimental episodes, each generated by a specified adaptive policy. Do not silently replace this sampling interface with exact probability queries, unrestricted interventions, or access to hidden states.

Let $\mathcal E_L$ be the admissible adaptive protocols using at most $L$ system calls, and define the operational discrepancy

$$
d_L(M,N)
=
\sup_{E\in\mathcal E_L}
\operatorname{TV}\!\left(
\operatorname{Law}_M(E),
\operatorname{Law}_N(E)
\right).
$$

Use complete joint transcript laws. Specify which preparations, auxiliary systems, and wiring operations the experiments permit.

### Statistical reconstruction

Determine what finite observations can justify: an exact Hankel rank, an approximate predictive representation, a positive cone, or only a confidence set of compatible behaviors.

Separate structural identification from predictive accuracy. State the assumptions needed for a guarantee of the form

$$
\Pr\!\left[
d_L(M,\widehat M)\le
\varepsilon(n,L,\delta,\text{conditioning parameters})
\right]\ge1-\delta.
$$

Make every conditioning parameter explicit. Distinguish assumptions supplied externally-such as a rank bound or observability margin-from properties that can themselves be certified from the data. Separate statistical identifiability, computational feasibility, and verification of the returned certificate.

### Positivity and model uncertainty

Determine whether the reconstruction can return a globally valid positive instrument, rather than matrices that fit sampled probabilities but assign invalid probabilities to untested protocols.

Compare a single reconstructed model with a confidence set of admissible models. What additional assumptions permit a sound reduction from the latter to the former?

Do not identify positivity on a finite test table with positivity under every continuation. Distinguish evidence-supported constraints from stronger restrictions imposed by the selected model class. Determine whether exact recovery of the preparation cone or test cone is meaningful, or whether only operational approximations are statistically warranted.

### Compositional error

For each admitted wiring operation $W$, establish a bound relating component errors to

$$
d_{L'}\!\left(
W(M_1,\ldots,M_k),
W(\widehat M_1,\ldots,\widehat M_k)
\right).
$$

Account explicitly for the number of component calls, adaptive routing, observation hiding, and the preparation interface. Treat independent parallel composition separately from correlated joint preparations.

Distinguish unconditional errors from errors after conditioning on an event. Identify the necessary branch-probability assumptions for conditional guarantees.

Determine whether reconstruction and wiring admit quantitatively controlled comparison cells. Do not introduce an “approximate Beck-Chevalley condition” without specifying its observable meaning, error budget, and behavior under repeated composition.

### Required stress test

Compare

$$
M_0:\quad Y_t\overset{\mathrm{iid}}{\sim}\operatorname{Bernoulli}(1/2)
$$

with

$$
M_\eta:\quad
Z\in\{-1,+1\}\text{ chosen uniformly once},\qquad
Y_t\mid Z\overset{\mathrm{iid}}{\sim}
\operatorname{Bernoulli}(1/2+\eta Z).
$$

As $\eta\downarrow0$, determine the exact Hankel ranks, finite-horizon distinguishability, long-horizon distinguishability, and sample requirements for distinguishing the models. Use this to test whether exact minimal reconstruction can be uniformly stable near a rank change.

Add a rare-event example testing whether a small unconditional discrepancy can become a large conditional discrepancy.

Conclude with either a constructive theorem or an impossibility result identifying the strongest attainable combination of finite evidence, positivity, structural identification, and compositional accuracy. Retain uncertainty rather than manufacturing a canonical answer where the evidence does not select one.

---

The comparison with existing work should be demanding. Spectral HMM learning already provides finite-sample predictive guarantees under separation assumptions; learning from a single dependent trajectory requires a separately specified sampling analysis. Merely renaming these results “quantitative categorical reconstruction” would add little. ([arXiv](https://arxiv.org/abs/0811.4413))

The substantive target is the connection those guarantees do not automatically supply: a positive realization whose experimentally justified error certificate survives the intended uses of the model. If that connection fails, the failure should determine the reconstruction interface-possibly a family of models with explicit unresolved distinctions, rather than one allegedly discovered structure.


You:
Let's answer it.

ChatGPT:
# Result

Finite observations can support a globally valid positive model with a certified finite-horizon prediction error, and that certificate can survive bounded causal composition. They cannot, without additional separation and completeness assumptions, support a uniformly stable reconstruction of exact Hankel rank, the canonical positive cone, or a unique latent mechanism.

Consequently, empirical uncertainty does not force every application to return only a family of models. A single positive representative can be adequate for a specified operational contract. But a representative should not be confused with an identified structure: outside its certified horizon and experimental interface, compatible models can disagree arbitrarily.

The distinction is the method map’s separation between existence, identifiability, and stability, now supplemented by explicit sampling and composition bounds.

The following construction establishes a baseline theorem. It is intentionally distribution-free and potentially expensive. Low-rank methods can improve its efficiency under additional assumptions; they are not needed for its existence.

---

## 1. Sampling interface and target guarantee

Let $A,O$ be finite action and observation alphabets, with all actions available. The unknown system $M$ is a controlled stochastic transducer.

A reset creates a fresh instance with the same initial distribution, independently of previous episodes. This is an explicit experimental capability-not access to a chosen hidden state.

Training consists of $n$ independent episodes, each of length $L$, under a known policy
$$
\rho_t(a\mid h_{t-1}).
$$
The policy can adapt to observations within an episode. For the theorem below, it is fixed before collecting the episodes and satisfies
$$
\rho_t(a\mid h)\ge \alpha>0.
\tag{1}
$$

The recorded data are complete action-observation transcripts. Unknown sensor corruption or imperfect resets would require an additional error model.

For any admissible policy $\pi$, let $P_M^\pi$ be its length-$L$ transcript law. Define
$$
d_L(M,N)
=
\sup_\pi \operatorname{TV}(P_M^\pi,P_N^\pi).
\tag{2}
$$
Allowing a protocol to stop early or return a function of its transcript does not enlarge this distance: it can be padded to length $L$, then postprocessed.

This is a distance on public behavior from the specified initial preparation. It does not certify equivalence under hidden-state interventions or undeclared correlated initializations.

### The sampling-to-use comparison

Write $Q_M=P_M^\rho$ for the exploratory transcript law. For a transcript
$$
h=(a_1,o_1,\ldots,a_L,o_L),
$$
the policy-change likelihood ratio is
$$
w_\pi(h)
=
\prod_{t=1}^L
\frac{\pi_t(a_t\mid h_{t-1})}
{\rho_t(a_t\mid h_{t-1})}.
$$
It is independent of the unknown system. Consequently,
$$
P_M^\pi(h)=w_\pi(h)Q_M(h).
$$

Let
$$
\Gamma_L=\sup_{\pi,h}w_\pi(h)\le \alpha^{-L}.
$$
Then
$$
\boxed{
d_L(M,N)\le
\Gamma_L\operatorname{TV}(Q_M,Q_N).
}
\tag{3}
$$

Proof. Multiply $Q_M-Q_N$ by $w_\pi$, take its $\ell_1$ norm, and use $w_\pi\le\Gamma_L$. Then take the supremum over $\pi$. ∎

No lower bound on the probability of every observation history is needed here. Rare stochastic histories remain weighted by their occurrence probabilities. A lower bound becomes necessary when making guarantees conditional on such histories.

### What is actually necessary?

Full-support exploration is sufficient, not intrinsically necessary for every model class. The necessary identifiability condition is
$$
Q_M=Q_N\Longrightarrow d_L(M,N)=0.
\tag{4}
$$

For uniform stability, the corresponding modulus must vanish:
$$
\omega_L(\varepsilon)
=
\sup\left\{
d_L(M,N):
\operatorname{TV}(Q_M,Q_N)\le\varepsilon
\right\}
\longrightarrow0.
\tag{5}
$$

Equation (3) supplies the explicit bound $\omega_L(\varepsilon)\le\Gamma_L\varepsilon$.

Without a condition like (4), reconstruction is impossible even with infinitely many exploratory samples. For example, a policy that never selects action $b$ cannot distinguish two unrestricted models that agree under every other action and produce opposite deterministic outputs under $b$.

---

## 2. A finite-data theorem with global positivity

Let
$$
m=(|A||O|)^L
$$
be the number of possible transcripts, and let $\widehat Q_n$ be their empirical distribution.

Define
$$
\beta_n(\delta)
=
\min\left\{
1,\sqrt{\frac{m\log 2+\log(1/\delta)}{2n}}
\right\}.
\tag{6}
$$

A direct concentration argument gives
$$
\Pr\!\left[
\operatorname{TV}(Q_M,\widehat Q_n)\le\beta_n(\delta)
\right]\ge1-\delta.
\tag{7}
$$

Indeed, total variation is the maximum discrepancy over subsets of the transcript space. Apply Hoeffding’s inequality to each subset and take a union bound over at most $2^m$ subsets. This bound is conservative but explicit.

### 2.1 Empirical frequencies must be made causally consistent

An empirical joint distribution of actions and observations need not obey the known policy exactly. It should therefore not be treated directly as a causal model.

Let $\mathcal Q_\rho$ be the polytope of transcript distributions compatible with policy $\rho$. If $q(h)$ denotes prefix mass, its constraints include
$$
q(\epsilon)=1,\qquad q(h)\ge0,
$$
and
$$
\sum_o q(hao)=\rho(a\mid h)\,q(h).
\tag{8}
$$

Choose
$$
\widehat Q\in
\arg\min_{q\in\mathcal Q_\rho}
\operatorname{TV}(q,\widehat Q_n).
\tag{9}
$$
This is a finite linear program.

From a feasible $q$, define an output kernel on each positive-mass history:
$$
\widehat p(o\mid h,a)
=
\frac{q(hao)}{\rho(a\mid h)q(h)}.
\tag{10}
$$
At unreachable histories choose any probability distribution.

A finite-state machine implements this kernel by storing the history up to length $L$. After that, send it to an absorbing state with an arbitrary normalized output rule.

The resulting transducer is globally stochastic: every transition is nonnegative and normalized for every future interaction. Its behavior beyond $L$ is a chosen completion, not an empirical conclusion.

### 2.2 The theorem

Because $Q_M\in\mathcal Q_\rho$, on event (7),
$$
\operatorname{TV}(\widehat Q,\widehat Q_n)\le\beta_n.
$$
Therefore
$$
\operatorname{TV}(Q_M,\widehat Q)\le2\beta_n.
$$

Combining this with (3):

> Positive finite-horizon reconstruction theorem.  
> Under independent resets and the known exploratory policy above, the causal projection construction returns a globally valid finite stochastic transducer $\widehat M$ satisfying
> $$> \boxed{
> \Pr\!\left[
> d_L(M,\widehat M)
> \le
> \min\{1,2\Gamma_L\beta_n(\delta)\}
> \right]\ge1-\delta.
> }
> \tag{11}
>$$

A sufficient sample count for error at most $\varepsilon$ is
$$
n\ge
\frac{2\Gamma_L^2}{\varepsilon^2}
\left(m\log2+\log(1/\delta)\right).
\tag{12}
$$

This theorem requires neither a Hankel-rank bound nor a spectral gap. It estimates behavior directly.

Its cost is substantial. The transcript space, history-state realization, and coverage factor can all grow exponentially with $L$. It is an existence and certification result, not a claim of efficient low-dimensional identification.

### 2.3 A certificate for any learned positive model

The argument is not restricted to the projection estimator. Suppose a learning procedure returns any globally valid positive model $\widetilde M$, possibly selected using the same data. Its empirical fit
$$
s_n=\operatorname{TV}(Q_{\widetilde M},\widehat Q_n)
$$
gives the certificate
$$
\boxed{
d_L(M,\widetilde M)
\le
\Gamma_L\bigl(\beta_n+s_n\bigr)
}
\tag{13}
$$
on event (7).

Thus a compact Hankel or hidden-state learner can be separated from its operational validator. The learner proposes a model; positivity is verified algebraically; experimental fit supplies the finite-horizon error bound.

There is no claim that finding a compact model with small $s_n$ is easy.

---

## 3. What finite data can-and cannot-identify structurally

### 3.1 Exact rank requires more than a small empirical residual

Suppose a selected square Hankel core $H$ and its shifted matrices $H_{a,o}$ determine a linear representation, with
$$
\sigma_{\min}(H)\ge\sigma>0.
$$

Assume certified estimation bounds
$$
\|\widehat H-H\|\le\tau<\sigma/2,
\qquad
\|\widehat H_{a,o}-H_{a,o}\|\le\tau_{a,o}.
$$
Then
$$
\|\widehat H^{-1}\|\le\frac2\sigma,
\qquad
\|\widehat H^{-1}-H^{-1}\|
\le\frac{2\tau}{\sigma^2}.
$$

In coordinates with $D_{a,o}=H_{a,o}H^{-1}$,
$$
\boxed{
\|\widehat D_{a,o}-D_{a,o}\|
\le
\frac{2\tau_{a,o}}{\sigma}
+
\frac{2\|H_{a,o}\|\tau}{\sigma^2}.
}
\tag{14}
$$

This is the instability that spectral separation controls. Hsu, Kakade, and Zhang obtain finite-sample predictive guarantees under explicit rank and singular-value assumptions; their learned observable representation need not recover the original hidden transition and emission matrices. ([arXiv](https://arxiv.org/abs/0811.4413))

Several obligations remain distinct.

Completeness: the selected core must capture the entire behavior, rather than only a low-rank projection of the tested fragment. The choice and sufficiency of histories and tests materially affect PSR learning. ([AAAI Publications](https://ojs.aaai.org/index.php/AAAI/article/view/9635))

Separation: the relevant nonzero singular values must be large enough relative to estimation error.

Propagation: small coordinate error must imply small experimental-law error over the intended horizon. A poorly conditioned coordinate system or unstable operator product can invalidate a naive conversion.

Positivity: the estimated operators must generate valid probabilities outside the sampled table.

A singular value satisfying
$$
\sigma_j(\widehat H)>\tau
$$
certifies a lower bound on the rank of that block. It does not certify that the full Hankel operator has no additional directions.

Exact upper-rank conclusions require an external rank bound, a complete witnessing block, a separation assumption on nonzero modes, or another independently justified structural restriction.

These assumptions are needed for the particular structural inverse-not for the mere existence of a good finite-horizon predictor, as theorem (11) demonstrates.

### 3.2 Global positivity is a model property, not a finite-table property

A finite probability table can be valid while an extrapolated linear model assigns negative probabilities to a longer sequence. Therefore finite-table fit is not a global positivity certificate.

One sufficient certificate is a finite positive lift. For proposed observable operators $D_{a,o}$, supply
$$
G,\quad B_{a,o}\ge0,\quad \pi\ge0
$$
such that
$$
x_0=G\pi,\qquad \mathbf1^\top\pi=1,
$$
$$
D_{a,o}G=GB_{a,o},
\qquad
uG=\mathbf1^\top,
$$
$$
\sum_o\mathbf1^\top B_{a,o}=\mathbf1^\top.
\tag{15}
$$

These equations prove that the observable representation is generated by a valid finite stochastic transducer. Every sequence probability is therefore nonnegative and normalized.

This certificate need not be minimal or canonical. It is a witness of global validity.

Other invariant-cone certificates can replace a finite lift, but the proof obligation remains explicit. Positivity imposed by the model class is not evidence that the true system has that particular cone or latent decomposition.

### 3.3 Exact canonical cones are not generally finite-data targets

The canonical preparation cone depends on all accessible preparations and arbitrarily long continuations. Finite-horizon data constrain only a finite operational fragment.

Without a state-count or other structural bound, two finite-state machines can agree exactly for every experiment of length at most $L$ and disagree deterministically at time $L+1$: use a clocked machine that delays its first distinguishing output.

Thus even infinitely many length-$L$ episodes cannot determine the full Hankel structure.

There is also no coordinate-free numerical error in “the recovered cone” until an ambient comparison, normalization, gauge, and metric are specified. A small behavioral error is not automatically a small error in extreme rays, face structure, or finite generation.

---

## 4. Required stress test: a rank change that short experiments barely detect

Consider
$$
M_0:\quad Y_t\overset{\mathrm{iid}}{\sim}\operatorname{Bernoulli}(1/2)
$$
and
$$
M_\eta:\quad
Z\in\{-1,+1\}\text{ initially uniform},\qquad
Y_t\mid Z\overset{\mathrm{iid}}{\sim}
\operatorname{Bernoulli}(1/2+\eta Z),
$$
where $0<\eta<1/2$. Each reset resamples $Z$.

### 4.1 Exact Hankel ranks

For $M_0$, every word probability factors into one scalar per symbol, so the Hankel rank is one.

For $M_\eta$, two latent states give rank at most two. The Hankel minor indexed by preparation and continuation words $\epsilon,1$ is
$$
\begin{pmatrix}
1&1/2\\
1/2&1/4+\eta^2
\end{pmatrix},
$$
whose determinant is $\eta^2$.

Therefore
$$
\boxed{
\operatorname{rank}H(M_0)=1,\qquad
\operatorname{rank}H(M_\eta)=2\quad(\eta>0).
}
\tag{16}
$$

The structural change occurs for every nonzero $\eta$.

### 4.2 Exact finite-horizon likelihood ratio

Set $X_t=2Y_t-1$, and let $P_0^L,P_\eta^L$ denote length-$L$ observation laws. Relative to the uniform law $P_0^L$,
$$
R_\eta(x)
=
\frac{dP_\eta^L}{dP_0^L}(x)
=
\frac12\prod_{t=1}^L(1+2\eta x_t)
+
\frac12\prod_{t=1}^L(1-2\eta x_t).
\tag{17}
$$

Hence the exact operational distance is
$$
d_L(M_0,M_\eta)
=
\frac12\mathbb E_0|R_\eta-1|.
\tag{18}
$$

The chi-squared divergence has a closed form:
$$
\boxed{
\chi_L^2
=
\frac{(1+4\eta^2)^L+(1-4\eta^2)^L}{2}-1.
}
\tag{19}
$$

To derive it, expand (17) in products $\prod_{t\in S}X_t$. Only even subsets occur, and these functions are orthogonal under the uniform law. Therefore
$$
\chi_L^2
=
\sum_{\substack{k\ge2\\ k\text{ even}}}
\binom Lk(4\eta^2)^k.
$$

In particular, for $L\eta^2$ sufficiently small and $L\ge2$,
$$
\chi_L^2
\asymp L(L-1)\eta^4,
$$
and
$$
d_L(M_0,M_\eta)\le\frac12\sqrt{\chi_L^2}
=O(L\eta^2).
\tag{20}
$$

At $L=1$, the laws are exactly identical. At $L=2$,
$$
d_2(M_0,M_\eta)=2\eta^2.
$$

### 4.3 Sample requirements

For $n$ independent reset episodes,
$$
1+\chi^2\!\left((P_\eta^L)^{\otimes n},(P_0^L)^{\otimes n}\right)
=
(1+\chi_L^2)^n.
\tag{21}
$$

Thus, if
$$
nL(L-1)\eta^4\ll1,
$$
the two data distributions remain close, and no test can reliably distinguish their ranks.

This scaling is attainable. For one episode define
$$
T_L=
\frac{\left(\sum_{t=1}^L X_t\right)^2-L}{L(L-1)}.
$$
Writing $\theta=2\eta$,
$$
\mathbb E_0T_L=0,\qquad
\mathbb E_\eta T_L=\theta^2,
$$
and direct counting gives
$$
\operatorname{Var}_\eta(T_L)
=
\frac{2(1-\theta^4)}{L(L-1)}
+
\frac{4(L-2)(\theta^2-\theta^4)}{L(L-1)}.
\tag{22}
$$

When $L\eta^2$ is bounded by a sufficiently small constant, this variance is $O(1/[L(L-1)])$. A median-of-means test across episodes therefore distinguishes the specified alternatives with error at most $\delta$ using
$$
n=
O\!\left(
\frac{\log(1/\delta)}
{L(L-1)\eta^4}
\right).
\tag{23}
$$

The matching lower order follows from
$$
D_{\mathrm{KL}}(P_\eta^L\|P_0^L)
\le \log(1+\chi_L^2)
$$
and the binary-testing lower bound obtained by applying relative-entropy data processing to the test decision.

For specified $\eta$, $L\ge2$, $\delta\le1/10$, and the small-signal regime,
$$
\boxed{
n\asymp
\frac{\log(1/\delta)}
{L(L-1)\eta^4}
}
\tag{24}
$$
up to absolute constants.

### 4.4 Longer episodes change the problem

Consider
$$
E_L=\left\{\left|\overline Y_L-\tfrac12\right|\ge\tfrac\eta2\right\}.
$$
Hoeffding bounds give
$$
P_0^L(E_L)\le2e^{-L\eta^2/2},
\qquad
P_\eta^L(E_L)\ge1-e^{-L\eta^2/2}.
$$
Consequently,
$$
\boxed{
d_L(M_0,M_\eta)\ge
1-3e^{-L\eta^2/2}.
}
\tag{25}
$$

One episode of length $O(\eta^{-2}\log(1/\delta))$ suffices for this specified testing problem.

In the infinite-horizon limit, the laws are mutually singular: the empirical frequency converges to $1/2$ under $M_0$, and to $1/2\pm\eta$ under $M_\eta$.

### Consequence

For every fixed finite experimental budget, sufficiently small nonzero $\eta$ makes rank one and rank two statistically indistinguishable. Hence:

> Exact rank reconstruction is not uniformly statistically stable near a rank change.

This does not preclude pointwise consistent procedures or reliable rank identification under a declared separation margin. It precludes a uniform finite-sample claim over all $\eta>0$.

It also shows why the intended horizon must remain part of the error contract. Small error at short horizons is compatible with almost perfect distinguishability at long horizons.

---

## 5. Conditioning is an explicit error amplifier

Let two joint laws $P,Q$ satisfy
$$
\operatorname{TV}(P,Q)\le\varepsilon.
$$
For an event $E$ with both probabilities positive,
$$
\boxed{
\operatorname{TV}(P(\cdot\mid E),Q(\cdot\mid E))
\le
\min\left\{
1,\frac{\varepsilon}{\max\{P(E),Q(E)\}}
\right\}.
}
\tag{26}
$$

For example, suppose $p=P(E)\ge q=Q(E)$. The variation outside $E$ is at least $p-q$. Combining this with the variation inside $E$ gives
$$
\operatorname{TV}(P,Q)
\ge
p\,\operatorname{TV}(P(\cdot\mid E),Q(\cdot\mid E)).
$$

Thus, if $P(E)\ge\tau$ and $\varepsilon<\tau$, the model conditional is defined and its error is at most $\varepsilon/\tau$.

### Tight rare-event example

Let
$$
P(\bot)=Q(\bot)=1-\alpha,
$$
while
$$
P(E,0)=\alpha,\qquad Q(E,1)=\alpha.
$$
Then
$$
\operatorname{TV}(P,Q)=\alpha,
$$
but
$$
\operatorname{TV}(P(\cdot\mid E),Q(\cdot\mid E))=1.
$$

With $n$ independent episodes, the data are identical whenever the rare event never occurs. That event has probability $(1-\alpha)^n$. Reliable discrimination therefore requires order
$$
\alpha^{-1}\log(1/\delta)
$$
episodes.

A finite-data certificate for conditional prediction must accordingly include a branch-probability lower bound, or an explicit abstention rule on insufficiently supported branches.

Reset access does not supply a conditional-sampling oracle. Rejection sampling a branch of probability $\alpha$ costs $1/\alpha$ episodes on average. Work on learning HMMs from conditional samples uses a genuinely stronger access model than independent observation episodes. ([arXiv](https://arxiv.org/abs/2302.14753))

---

## 6. Which error certificates survive composition?

The appropriate comparison is operational indistinguishability under the admitted contexts. This is also the organizing principle in mathematical treatments of interactive random systems. ([crypto.ethz.ch](https://crypto.ethz.ch/publications/LanMau21.html))

### 6.1 Persistent components and bounded causal wiring

Suppose
$$
d_{L_i}(M_i,\widehat M_i)\le\varepsilon_i.
$$

Let $W$ be a causal wiring that accesses each component instance through its public interface and makes at most $L_i$ calls to instance $i$. Assume independent initialization of the instances and no undeclared correlation with their hidden states.

Then
$$
\boxed{
d_{L'}\!\left(
W(M_1,\ldots,M_k),
W(\widehat M_1,\ldots,\widehat M_k)
\right)
\le
\min\left\{1,\sum_i\varepsilon_i\right\}.
}
\tag{27}
$$

Here $L'$ indexes the external protocol budget, and the wiring must translate every admitted external protocol into local protocols within the $L_i$ budgets.

Proof. Replace components one at a time. With all other components fixed, they and the wiring form an admissible randomized controller for the component being replaced. Its replacement changes the external law by at most $\varepsilon_i$. Apply the triangle inequality. ∎

A persistent instance used $L_i$ times incurs one whole-interaction error $\varepsilon_i$, not $L_i\varepsilon_i$.

If there are $c_i$ independently reset instances, each governed by the same per-instance certificate, the bound becomes
$$
\sum_i c_i\varepsilon_i.
\tag{28}
$$

### 6.2 A one-step certificate is different

A guarantee from the initial state at horizon one is not a per-step guarantee.

If instead a stronger contract establishes
$$
\sup_{h,a}
\operatorname{TV}
\bigl(
p_M(\cdot\mid h,a),
p_{\widehat M}(\cdot\mid h,a)
\bigr)
\le\gamma
$$
on all relevant common histories, sequential coupling gives
$$
d_L(M,\widehat M)
\le1-(1-\gamma)^L\le L\gamma.
\tag{29}
$$

The supremum over conditional histories is an additional obligation. It cannot be inferred from a small unconditional $d_1$.

Likewise, no finite-horizon certificate extrapolates automatically to longer interaction. The delayed-output clock example gives $d_L=0$ but $d_{L+1}=1$.

### 6.3 Hiding, parallelism, and conditioning

Observation hiding and other stochastic postprocessing cannot increase total variation.

For independent parallel outputs,
$$
\operatorname{TV}\!\left(\bigotimes_iP_i,\bigotimes_iQ_i\right)
\le
1-\prod_i(1-\operatorname{TV}(P_i,Q_i))
\le
\sum_i\operatorname{TV}(P_i,Q_i).
\tag{30}
$$

Adaptive cross-wiring is covered by the hybrid bound (27), provided it stays within the specified public interface and budgets.

Postselection is different. After a composite error bound $\varepsilon_{\mathrm{comp}}$, conditioning on a branch of probability at least $\tau$ yields a bound
$$
\varepsilon_{\mathrm{comp}}/\tau.
$$
The probability denominator is part of the certificate.

### 6.4 Correlated preparations are not covered by marginal certificates

Two pairs of bits can have identical fair marginals but opposite joint laws:
$$
\tfrac12\delta_{00}+\tfrac12\delta_{11},
\qquad
\tfrac12\delta_{01}+\tfrac12\delta_{10}.
$$
Their marginal error is zero and their joint total variation is one.

Thus arbitrary correlated initialization cannot be justified from component certificates. The joint preparation itself must be estimated or bounded.

This is the same distinction retained in the probabilistic-language note: copying a realized random value and independently rerunning its generator produce different joint laws.

### Confidence and operational error are different quantities

If component guarantees hold with failure probabilities $\delta_i$, then all the compositional bounds hold jointly with probability at least
$$
1-\sum_i\delta_i.
$$
This union bound does not require independent training datasets.

The $\delta_i$ describe uncertainty in the certificate. The $\varepsilon_i$ bound operational discrepancy when the certificate holds. They should not be combined into one informal “error rate.”

---

## 7. Confidence sets retain the unresolved structure

Define
$$
\mathcal C_n
=
\left\{
N\text{ globally positive}:
\operatorname{TV}(Q_N,\widehat Q_n)\le\beta_n
\right\}.
\tag{31}
$$

Under the sampling assumptions,
$$
\Pr(M\in\mathcal C_n)\ge1-\delta.
$$

Every pair of models in $\mathcal C_n$ satisfies
$$
d_L(N,N')\le2\Gamma_L\beta_n.
\tag{32}
$$

Thus the set can contain models with different ranks, hidden-state structures, or positive cones while still supporting nearly identical decisions within the certified horizon.

### When is a single model sufficient?

A representative is sufficient when the requested task depends only on the certified behavior. For any bounded transcript payoff $f\in[0,1]$,
$$
|\mathbb E_M f-\mathbb E_{\widehat M}f|
\le d_L(M,\widehat M).
$$

For claims about long horizons, hidden interventions, exact structure, or rare conditionals, the residual distinctions matter. A confidence set, or an equivalent explicit uncertainty representation, must be retained unless additional assumptions resolve them.

Model-class assumptions are not automatically empirically certified. Intersecting (31) with “at most $r$ hidden states” preserves coverage only if that restriction is justified independently or the true system is otherwise known to belong to it.

### Do not resample the model uncertainty at each step

A member $N\in\mathcal C_n$ represents one fixed mechanism governing the complete episode. Choosing a different compatible model after each observation generally produces behaviors that no member of $\mathcal C_n$ realizes.

For wiring,
$$
W_*(\mathcal C_1,\ldots,\mathcal C_k)
=
\{W(N_1,\ldots,N_k):N_i\in\mathcal C_i\}
\tag{33}
$$
must retain each choice throughout its use. Repeated occurrences of the same unknown component must share the same model parameter.

Replacing this set by independent local uncertainty intervals can be a sound overapproximation, but it discards cross-time constraints and is not an exact reconstruction.

---

## 8. What quantitative comparison squares are justified?

Suppose separate component reconstructions yield $\widehat M_i$ with errors $\varepsilon_i$. Suppose an independent-or merely separately certified-reconstruction of the composite yields $\widehat N$, with
$$
d_{L'}(W(M_i),\widehat N)\le\varepsilon_W.
$$

Then, on the simultaneous confidence event,
$$
\boxed{
d_{L'}\!\left(
\widehat N,\,
W(\widehat M_i)
\right)
\le
\varepsilon_W+\sum_i c_i\varepsilon_i.
}
\tag{34}
$$

This is an operational comparison between “reconstruct after wiring” and “wire reconstructed models.” Its interpretation is exact: every admitted external experiment has output laws differing by at most the displayed budget.

The budgets compose by addition and resource multiplicity. Observation hiding is nonexpansive; conditioning adds a probability-dependent factor.

That is a legitimate quantitative commutation certificate. It is not yet a Beck-Chevalley theorem:

- there need not be a canonical map between the learned latent spaces;
- there need not be an adjunction whose mate is being estimated;
- exact rank, minimality, and positive-cone structure need not be preserved.

The method map’s requirement is precisely that an approximate categorical claim declare its metric and preservation bound. Equation (34) supplies that operational content without asserting an unsupported categorical inverse.

At the confidence-set level, both the directly reconstructed set and the wired component set contain the true composite on the joint confidence event. Neither need be included in the other. Their relationship should remain a comparison of supported behaviors, not be silently upgraded to equality of reconstruction doctrines.

---

## 9. What additional assumptions buy stronger conclusions?

The assumptions are indexed to different objectives.

| Objective                                    | Additional obligation                                                                                     |
| -------------------------------------------- | --------------------------------------------------------------------------------------------------------- |
| Finite-horizon prediction under new policies | Experimental coverage or another quantitative sampling-to-use modulus                                     |
| Compact spectral reconstruction              | A complete core, quantitative conditioning, and controlled propagation of operator errors                 |
| Exact rank recovery                          | A justified global complexity bound/completeness condition and separation from rank-changing alternatives |
| Global positivity of the returned model      | A positive parametrization or verified invariant-cone/lift certificate                                    |
| Accurate rare-event conditionals             | A certified lower bound on the conditioning-event probability                                             |
| Long-horizon conditional prediction          | Suitable observability and filter-stability assumptions                                                   |
| Composition with correlated preparations     | A joint preparation law or joint uncertainty certificate                                                  |
| Structural interpretation of a positive cone | Identifiability and stability in a declared representation class and comparison metric                    |

These conditions are not interchangeable.

For example, filter contraction can stabilize one-step conditional predictions without bounding the total variation of complete transcripts uniformly over all horizons. Even two different i.i.d. Bernoulli processes eventually become perfectly distinguishable.

Existing spectral theory already separates joint-sequence guarantees from conditional guarantees requiring additional stochasticity assumptions. ([arXiv](https://arxiv.org/abs/0811.4413)) The more general algebraic relationship between weighted automata, observable operator models, and PSRs likewise does not eliminate their statistical conditioning requirements. ([Journal of Machine Learning Research](https://www.jmlr.org/papers/v16/thon15a.html))

Computational feasibility remains separate. The causal-tree construction is tractable in the explicitly enumerated transcript space but potentially exponential in horizon. Compact positive fitting is a constrained realization problem. A feasibility witness can be verified without having an efficient algorithm that always discovers one.

---

## Strongest justified conclusion

There is a constructive result:

> With independent reset episodes, known exploratory policies covering the intended actions, and a fixed finite operational horizon, a globally valid positive transducer can be reconstructed with a uniform high-probability prediction bound. That bound survives bounded causal wiring, with explicit resource accounting, and survives conditioning only with the appropriate probability denominator.

There are also sharp negative results:

> No uniformly reliable finite-budget procedure identifies exact Hankel rank across arbitrarily small rank-changing perturbations. Finite-horizon evidence alone does not identify the canonical infinite-horizon positive cone or justify unrestricted extrapolation. Marginal certificates do not control undeclared joint preparations.

The appropriate statistical interface is therefore

$$
\boxed{
\text{experimental data}
\longrightarrow
\text{confidence set of positive behaviors}
\longrightarrow
\text{certified representative and/or robust decisions}.
}
$$

A compact Hankel model can be an effective representative. Its compression, positivity proof, empirical adequacy, and composition certificate are separate obligations.

The property that survives finite noisy evidence is not canonical exact structure. It is a quantified range of admissible behavior under a declared class of uses. A single model is warranted when that range is sufficiently narrow for those uses; otherwise the unresolved family is part of the result, not a failure to finish the reconstruction.
