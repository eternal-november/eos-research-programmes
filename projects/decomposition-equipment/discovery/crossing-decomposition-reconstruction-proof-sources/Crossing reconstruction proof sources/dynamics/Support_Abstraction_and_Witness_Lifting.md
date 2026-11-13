# Support abstraction and witnessed reconstruction

## Plain language summary

A relational description says which input-output pairs are possible. A witnessed description also records the distinct ways each pair can occur. Forgetting those ways is compatible with composition and interface changes, but reversing that simplification is not automatic.

Two kinds of failure are explicit. The numbers of retained witnesses may make a common decomposition impossible. Even when the numbers fit, the specified matching between the two whole-system decompositions may mix witnesses in a way that no common middle component can explain. This supplies a genuine graph-independent semantic translation for the relative reconstruction problem.

## 1 The abstraction is structure preserving

Let FinSpan be the double category with finite sets as objects, functions as vertical arrows, finite spans A<-E->B as horizontal arrows, and commuting maps of apex sets as cells. Horizontal composition is pullback over the shared interface. Units are identity spans. Cartesian restrictions along f:A'->A and g:B'->B have apex

  {(a',e,b'): f(a')=left(e), g(b')=right(e)}.

Let FinRel have the same objects and vertical functions, relations R subset A x B as horizontal arrows, relational composition, equality relations as units, and cells given by the relevant preservation implication under endpoint functions. Restrictions are inverse images of relations along the endpoint functions.

Define support by

  supp(E)={(a,b): exists e in E with endpoints (a,b)}.

An apex map induces the required implication of supports, so this is defined on cells.

### Proposition 1 Support preserves the equipment operations

Support preserves units, horizontal composition, and chosen cartesian restrictions up to the standard canonical identifications of the span constructions.

Proof. For composition, (a,c) belongs to the support of E x_B F exactly when there are e,f with matching B endpoint, equivalently some b with (a,b) in supp(E) and (b,c) in supp(F). This is relational composition. The identity span has support equality. The displayed restriction apex is nonempty over (a',b') exactly when (f(a'),g(b')) belongs to supp(E), which is inverse-image restriction. The statements on cells and universal comparison cells follow from these identities. QED.

Thus the relevant abstraction is not merely a lax approximation obtained by independently quotienting an intermediate interface. It is a genuine structure-preserving passage from finite witnessed relations to their supports.

## 2 A witnessed crossing square

Fix four parent spans

  L:A->B, R:C->D, V:A->C, W:B->D

and a specified boundary-preserving bijection of whole witnesses

  theta: V x_C R -> L x_B W.

The two sides are the two parent decompositions of the same whole. A coherent common middle realization consists of a span U:B->C and boundary-preserving bijections

  alpha: L x_B U -> V,
  beta: U x_C R -> W,

such that, after canonical tuple regrouping,

  theta(alpha(l,u),r)=(l,beta(u,r))

for every compatible triple (l,u,r).

Taking supports yields the two-sided relational completion problem. But a solution to the support equations does not imply a solution to these witnessed equations and their fixed coherence condition.

## 3 A counting obstruction

Take all four boundary sets to be singletons. Let |L|=|R|=2 and |V|=|W|=1. Both whole witness sets have cardinality 2, so there is a bijection theta between them. Every parent support is the unique nonempty relation, and the support-level middle solution is likewise nonempty.

If a finite U realized the witnessed square, alpha would force

  2 |U| = 1,

which is impossible. Thus the support completion fibre can be nonempty while the finite-witness completion fibre is empty.

This obstruction is independent of the chosen theta. It is a finite cardinality constraint, not a claim that all witness obstructions reduce to counting.

## 4 A matching obstruction when all counts fit

Again use singleton boundary sets, but now let L,R,V,W all have witness set {0,1}. Define

  theta(v,r)=(v, v XOR r).

This is a bijection V x R -> L x W. The cardinality equations permit exactly |U|=1.

Suppose alpha and beta existed. For the single element u of U, write

  alpha(l,u)=a(l), beta(u,r)=b(r),

where a and b are bijections of {0,1}. Coherence would force

  theta(v,r)=(a^{-1}(v), b(r)).

But in the given theta the second coordinate is v XOR r and therefore depends on v. It cannot equal a function b(r) independent of v. No coherent common middle exists.

This is a prescribed-matching obstruction after support feasibility and cardinality feasibility have both passed. Changing theta to a product bijection repairs the square, but changes the supplied identification of the parent whole witnesses. A reconstruction algorithm must not silently make that change.

## 5 No universal finite-witness realization section

There is no identity-on-objects pseudofunctor from FinRel to FinSpan that is a section of support and preserves all horizontal compositions and units up to isomorphism.

Proof. Let 1 be a singleton and 2 a two-element set. Let P:1->2 and Q:2->1 be the total relations. Their relational composite QP is the identity relation on 1. Any span realizing P has at least one witness over each of the two endpoint pairs, as does any span realizing Q. Their pullback composite therefore has at least two witnesses. It cannot be isomorphic to the identity span on 1, which has one witness. This contradicts composition and unit preservation. QED.

The theorem does not prohibit a section at the level of individual relations, nor a lax construction, changing the interface objects, or partial realization on a restricted class. The same elementary argument also rules out an ordinary Set-span section with unchanged identity units; merely allowing infinite apex sets does not avoid it. It says that choosing finite realizations for every relation cannot universally reverse the abstraction while preserving the stated equipment composition.

## 6 Status and integration

The support construction and the elementary counting/product arguments are standard mathematics. Their role here is to give an exact relative setting and falsifiable lifting obligations for the crossing reconstruction program. The full positive criterion for the fixed witnessed square, including possible empty endpoint fibres and genuine realization symmetries, belongs to the companion witnessed-square theorem.

The finite relation synthesis theorem solves the support layer. It must not be labelled a complete witnessed reconstruction result. Conversely, the specified theta is essential input to the witnessed layer; ignoring it loses the distinction demonstrated by the matching example.
