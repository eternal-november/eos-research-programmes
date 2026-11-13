# Abstract sufficient criterion: adequate CFS comparison-span coherence

**Audit verdict: PASS for fixed-cylinder canonical normalization and its coherent span-comparison law.** This criterion abstracts the proved Isbell construction; it does not replace the independent construction of its tensor, wire objects, or honest network realizations with a preservation assumption.

## Hypotheses and exact orientation

Let K carry a CFS (E,M), with underlying arrow OFS (E₀,M₀). Assume:

1. every cospan consisting of one E₀ arrow and one M₀ arrow has a pullback with the corresponding opposite legs again E₀/M₀;
2. **every commuting square with horizontal M₀ arrows and vertical E₀ arrows is a pullback.**

These are the additional adequacy conditions, not consequences of arbitrary orthogonality. In HHLN's terminology, E₀ are egressives (the LEFT factorization class) and M₀ ingressives (the RIGHT factorization class); mixed/ambigressive squares have horizontal ingressives and vertical egressives. Thus these hypotheses match their Definition 4.2. Class-preserving functors preserve these pullbacks by Remark 4.3. Their standard span category has E-left/M-right legs; the M-left/E-right calculus used here is its opposite, not a reverse OFS. [HHLN, full text](https://arxiv.org/html/2011.11042), [published paper](https://doi.org/10.1017/fms.2023.107).

For example, Set's surjection/injection OFS fails (2): take P a nonempty proper subset of U, the top inclusion P→U, bottom id:1→1, and both vertical maps to 1. The square has the required polarities but is not a pullback.

## 1. Every polarized span map is invertible

Suppose h:U→V satisfies

    m_V h=m_U,      e_V h=e_U,

where m_U,m_V∈M₀ and e_U,e_V∈E₀, with common exterior endpoints X,Y.

The right-class cancellation law gives h∈M₀. For precision, this is the law

    g∈M₀ and gh∈M₀ ⇒ h∈M₀.

It follows directly from lifting: solve a lifting problem against h first against gh; then use uniqueness of lifting against g to verify the required triangle against h.

Now the commuting square

    U --h--> V
    |        |
   e_U      e_V
    |        |
    Y --id-> Y

has horizontal M₀ and vertical E₀ arrows, so is a pullback by (2). The pullback of e_V along id_Y is V itself; hence h is invertible.

**Logical distinction:** invertibility alone does not prove that at most one arbitrary bare span map exists. The fixed-cylinder theorem below needs uniqueness only for realization-compatible canonical comparison maps, which follows directly from CFS orthogonality. No unsupported inference from “all cells invertible” to “all cells unique” is used.

## 2. Canonical normalizer comparison is rigid

Fix an actual cylinder r:D⇒T, its canonical factorization D→R→T, and an honest realization X. Factor its preparation cocone as

    D --a_X∈E--> G_X --b_X∈M₀--> X.

The usual CFS construction supplies c_X:G_X→R in E₀, yielding C_X=(X←G_X→R).

For any compatible M₀/E₀ span X←u U→v R in Fact(r), orthogonality of a_X against u yields a unique eta:G_X→U preserving the preparation cocone and left leg. Orthogonality against the canonical test cone proves v eta=c_X. Thus eta is a polarized span map, and §1 makes it invertible.

Uniqueness is the uniqueness of that CFS filler. In fact, transporting along eta shows that U's preparation cocone is E. Hence any realization-compatible map between two such spans into R is unique, by orthogonality against either M₀ left leg. This is enough for all normalization coherence diagrams.

## 3. Coherent composition and network transport

For a compatible S:X⇝Y in Fact(r), mixed pullback composition supplies S;C_Y:X⇝R. Section 2 gives the unique realization-compatible isomorphism

    C_X ≅ S;C_Y.

Associativity and units hold because competing routes are realization-compatible maps between comparisons into the same R and are therefore equal. Class-preserving assembly functors preserve mixed pullbacks by (2), so these cells can be whiskered through network composition. An n-variable functor separately preserving E₀ and M₀ handles simultaneous projections by changing coordinates one at a time.

The resulting abstract criterion is therefore: **CFS + orthogonal adequacy of its underlying OFS + honest same-cylinder assembly functors preserving the arrow classes ⇒ coherent normalized comparison spans.** Fixed-port Isbell network assembly is a derived instance: its signed components prove adequacy and tensor-class preservation, while cups/caps prove honest realization compatibility.

## Prior-art scope

HHLN's §4 supplies the relevant adequate-factorization framework and explicitly uses right cancellation in the proof of Proposition 4.8. Garner supplies CFS orthogonality and uniqueness: [The Isbell monad](https://arxiv.org/pdf/1410.7108). I did not find the exact fixed-cylinder normalizer criterion stated as a numbered HHLN result; the proof above is a short derived application, not a novelty claim. This note does not claim rigidity of arbitrary context-enlargement spans or compatibility across changed cylinders without a specified bridge.
