# Exact operator-category baseline and scientific disposition

Author P-level translation for the released target §10, not a new research
obligation or an independent review. Contract v0.1 hash
`47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`;
target hash `2f8cc8b77165ef9d5fe915799e5291089067b10f0683f82d9f878ba1da1c7f7b`.
The purpose is to compare equally informative standard structures, including
nullaries, whole colours, ordered profiles and all arrow tuples. Removing
information from the comparator would manufacture a false increment.

## 1. Typed calculi as ordinary colored multicategories

Let A be any accepted fixed-base path-typed nonsymmetric calculus. Take its
colors to be the COMPLETE components W=(A,B,x∈J(A,B)), not interface names.
For a finite ordered list of colors (X_1,…,X_n) and output W, set its operation
set equal to the given A(W;p) when the list is a composable path p with the
endpoints of W, and empty otherwise. The empty list is allowed exactly when
W's endpoints coincide; its actual operation set is whatever A supplies,
possibly empty. The identity and composition are A's actual ones. If an
outer and every inner operation exist, their output/color matching makes
the expanded list a composable path with the right endpoints. Thus composition
stays within the assigned operation sets. The ordinary multicategory laws
are exactly the accepted occurrence-indexed laws. Conversely restrict this
colored multicategory to its admissible path fibres. Both constructions are
inverse on operations, identities, composition, and fixed-base strict maps.
No interface data or witness multiplicity was erased.

This is the accepted A1 baseline translation, recalled so the following
standard envelope applies to the full intended object, not an untyped proxy.

## 2. The standard monoidal envelope and exact opposite-slice formula

Define Env(A) as the following category. Its objects are finite ordered lists
of colors, whether or not the whole list itself is a composable path. An arrow
from a list q to a list p=(X_1,…,X_k) consists of an ordered division of q into
k consecutive sublists q_i and an A-operation b_i:q_i→X_i for each i. Empty
q_i are allowed when that operation exists. The division is arrow data. The
empty target list allows only the empty source and empty tuple.

Identity uses singleton sublists and the color identities. To compose an
arrow q→p with an arrow r→q, split the second tuple by each q_i and substitute
its entries into b_i. The resulting ordered division of r and tuple are
actual data. A1/B2's pair/triple occurrence identification proves the unit
and associative laws. Concatenation is a strict monoidal product on objects
and tuples. This is the usual free strict monoidal category on a plain
multicategory, not a new construction. Leinster gives it in *Higher Operads,
Higher Categories*, §2.3, pp. 56–57; the plain multicategory conventions of
§§2.1–2.3 permit colors and arities in the nonnegative integers.
[Primary source, §§2.1–2.3](https://arxiv.org/pdf/math/0305049).

Fix the singleton list (W). An object of the ordinary slice Env(A)/(W) is
exactly one operation a:p→W. A slice arrow from a':q→W to a:p→W is a forest
b:q→p with a∘b=a'. In the opposite category it is an arrow a→a', precisely
the full occurrence tuple required by Ref(A;W). The two assignments simply
read the same data, including each q_i and its segmentation; they are inverse.
Identity/composition on both sides is the forest operation just specified.
Consequently

    Ref(A;W) ≅ (Env(A)/(W))^op.                            (2.1)

The formula includes zero-input child operations, repeated identical colors,
and the full output color W. It is not a thin reachability construction.
Nonthin semantic refinement is therefore already standard forest/slice data.
No theorem that slices commute with arbitrary quotients is inferred from (2.1).

## 3. Equation groupoids and the standard forest-with-isomorphism category

Use the actual signature and seven equations of this package, not all
semantic equalities. In every full profile/output fibre form the groupoid
G whose objects are raw trees and whose arrows are contextual equation paths
modulo the LOCAL O relations. The complete ordinary-coherence proof in
Completion_Comparison §§3.1–3.2 gives an arrow t⇒u exactly when t and u are
E-equivalent, and that arrow is unique. This uniqueness was proved from the
local basis and termination, not imposed as a semantic-kernel definition.

Substitution extends to these groupoids. On objects it is raw forest graft.
Given an outer equation path and a tuple of inner equation paths with matching
profiles, A3's substitution-stable congruence gives an equation path between
the substituted terms. Ordinary O coherence makes its class independent of
all chosen paths and interleavings. Define substitution of morphisms by this
unique class. Identity, composite, operadic unit and associativity laws follow
because the corresponding object grafts agree by A1 and each parallel
morphism pair is already equal in G. This makes G a groupoid-valued colored
plain multicategory. It includes genuine nullaries; it is not a
constant-free/uncoloured simplification.

Here is the relevant forest construction explicitly, without requiring the
reader to choose conventions for a lax 2-slice. Fix W. Its objects are raw
operations T. A preliminary arrow T→U consists of:

* a raw forest F on the full ordered frontier of T, with complete child
  profiles whose concatenation is the frontier of U;
* a G-isomorphism z:T[F]⇒U.

Two such pairs (F,z),(H,y) define the same arrow exactly when there is a
pointwise G-isomorphism alpha_i:F_i⇒H_i at every original slot, with

    z = T[alpha]; y.                                    (3.1)

This is not equality of all endpoint composites: the alpha_i keep separate
entry profiles and values. Equation (3.1) is equality in the already built
ordinary equation groupoid. Because G is thin, whenever all alpha_i exist
the compatibility follows; the occurrence profiles still cannot be changed.
Reflexivity, symmetry and transitivity of this relation are supplied by
identity, inverse and composition in each G fibre.

For (F,z):T→U and (H,y):U→V, define the composite pair

    (F⋆H, z[H];y).                                      (3.2)

H is a forest on the shared full frontier of T[F] and U, so the operation is
typed. The groupoid substitution laws prove independence of representative
pairs: pointwise changes in F and H produce the corresponding pointwise
changes in F⋆H; the two terminal morphisms satisfy (3.1) by substitution
functoriality. Associativity follows from raw forest associativity and
associativity of equation-path whiskering; units use identity forests and
identity paths. This yields a category Int(G;W).

This is the elementary forest-plus-operation-isomorphism/opposite-lax-slice
construction for a groupoid-valued multicategory, described completely here
to remove variance and nullary ambiguities. It matches the usual categorical
operad integration pattern, but it is not claimed to be a literal application
of a theorem that excludes our arities or colors.

## 4. Exact comparison with the independently presented Comp

There is a functor A:Comp→Int(G;W). Send an elementary raw insertion to its
forest paired with the identity terminal isomorphism, and an equation edge
e:T→U to (identity forest,e). Raw category relations hold by (3.2); O holds
in G. MOut expresses the equality of the two ways to apply (3.2) with an
outer isomorphism and a forest. Bare MIn is exactly (3.1) for the pointwise
isomorphism at the newly inserted bare template. Therefore all the LOCAL
relations of the independently constructed Comp are respected.

Conversely define B on a pair by

    B(F,z)=R(T,F);z.                                    (4.1)

If (F,z) and (H,y) satisfy (3.1), the derived general MIn theorem gives
R(T,F);T[alpha]=R(T,H). Multiplying by y proves that (4.1) has the same
value for both pair representatives. Here the derivation from seven bare
MIn schemas, not only the existence of a pointwise equation, is essential.
Formula (3.2) is respected by B because the derived arbitrary-forest MOut
law moves z past R(U,H), and the raw composition law combines forests.
Identities are immediate.

The composite B A fixes each raw and equation generator, hence all Comp
arrows. The composite A B returns (F,z) using (3.2), hence every Int arrow.
Thus these are inverse identity-on-raw-object functors:

    Comp ≅ Int(G;W).                                    (4.2)

This comparison isolates the actual technical verification: seven bare
forest-entry relations plus elementary outer whiskering present the same
entrywise operation-isomorphism identifications as the standard construction.
It is not a second semantic-kernel definition of Comp. The result would be
unproved if general mixed compatibility were merely assumed.

Finally, passing each forest entry to its connected component in G gives
an arrow tuple in Q with the required endpoint; conversely raw representatives
of the Q entries and the terminal equation path give a pair. Pointwise
connected-component equality is exactly the relation (3.1). This recovers
Int(G;W)≃Ref(Q;W), and under Phi, Ref(D;W). It is the same explicit hom
comparison as Completion_Comparison §6, now displayed against the strongest
operator baseline. The raw objects still give only an equivalence with Ref(Q),
not an object-bijective isomorphism.

## 5. Literature boundaries and the actual significance finding

Mimram's published abstract coherent-Newman and zigzag theorems apply directly
to the ordinary equation groupoids: the local peak fillers and well-founded
order are verified here. Those principles are not new. His normal-object
lemma is for groupoids; the full-normal-object subcategory of Comp also uses
the elementary general-category fact that every object is isomorphic to a
chosen object. Noninvertible raw grafts are not erroneously treated as
invertible rewrite edges.
[Published source, §3.2](https://lmcs.episciences.org/16103/pdf).

Trnka's *Integration of a categorical operad*, Definition 5 and Proposition 9,
uses forests plus internal operation morphisms and entrywise 2-cells, with
the corresponding factorization. Its stated setting is uncoloured,
nonsymmetric and constant-free, so it is not a direct citation for our
colored/nullary local presentation. The proof in §§3–4 supplies its own exact
conventions rather than borrowing an inapplicable theorem. The fact that this
one source excludes a case does not make that case novel: the colored/plain
monoidal envelope above already includes nullaries.
[Primary version, Definition 5/Proposition 9](https://arxiv.org/html/2506.12399v2).

The complete picture is therefore:

1. The graph-cut object calculus is inherited restriction-species/operad
   infrastructure with retained data.
2. The M enrichment is exactly the typed scalar product, and its Ref category
   exactly the corresponding full-profile pullback. Hom/product/fibre formulas
   are automatic coordinate consequences.
3. Pure O coherence is a checked application/reproof of standard coherence.
4. The remaining syntactic theorem is a complete, useful specialized local
   presentation of the standard forest/operator construction in (4.2), with
   algorithmic normal forms and edge-case checks. It is NOT evidence for a new
   general categorical construction or a major independent result.
5. Omitting MIn breaks that chosen deficient presentation; the unbounded
   vertex-count obstruction diagnoses the missing relation. Standard operator
   categories already include entrywise compatibility, so it is not a new
   obstruction to those constructions.

No genuine mathematical increment beyond this explicit specialization,
integration and checked implementation has been established. An absence of
one publication with the entire sentence is not a novelty argument. This
package can pass technical correctness and provide useful baseline
infrastructure while failing to establish the program's intended scientific
significance. The honest disposition is to record that shortfall and obtain
the required Gate 2 direction decision, not count labels or bookkeeping as
a major contribution, weaken the target, or activate later work to rescue it.
The full §3.6 bundle independently still includes the unactivated B4, and no
F/D/E/G/I obligation is promoted by these translations.
