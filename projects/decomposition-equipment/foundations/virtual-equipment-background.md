# Decomposing virtual equipments

The Cruttwell–Shulman notion of a virtual equipment has a particularly clean decomposition:

\\[ \boxed{ \mathbf{vEquip} \lhook\joinrel\longrightarrow \mathbf{vDbl}\_{\mathrm{unit}} \longrightarrow \mathbf{vDbl}. } \\]

Here:

- \\(\mathbf{vDbl}\\) is the 2-category of virtual double categories.
- \\(\mathbf{vDbl}\_{\mathrm{unit}}\\) consists of virtual double categories admitting universal horizontal units, with normal functors as morphisms.
- \\(\mathbf{vEquip}\\) consists of those unital virtual double categories that also admit all restrictions.

Cruttwell and Shulman's Definition 7.6 identifies virtual equipments as virtual double categories with units and restrictions. Their Theorem 7.24 establishes something stronger: every functor between virtual equipments automatically preserves restrictions. Consequently, \\(\mathbf{vEquip}\\) is a full sub-2-category of \\(\mathbf{vDbl}\_{\mathrm{unit}}\\), although the latter is not full in \\(\mathbf{vDbl}\\).


Studylib


This is already a meaningful result about the decomposition: restrictions impose an additional condition on objects without requiring a further preservation condition on normal morphisms.

The central issue is whether the two layers have intrinsic universal characterizations, how they interact, and whether a more canonical decomposition should be a diagram rather than a linear tower.

## 1. The two universal layers

Write \\(\mathbb D\\) for a virtual double category. It has a category of objects and vertical arrows, horizontal arrows \\(J:A\nrightarrow B\\), and multicells of the form

\\[ \alpha\in \operatorname{Cell}\_{f,g} (J_1,\ldots,J_n;K), \\]

with composable horizontal source

\\[ A_0\xrightarrow{J_1}A_1 \longrightarrow\cdots \xrightarrow{J_n}A_n \\]

and horizontal target \\(K:B_0\nrightarrow B_1\\), framed by vertical arrows \\(f:A_0\to B_0\\) and \\(g:A_n\to B_1\\).

The source may have length zero. Multicells admit identities and substitution, but horizontal arrows need not have binary composites or identities.

### Layer U: universal horizontal units

For every object \\(A\\), require a horizontal arrow

\\[ U_A:A\nrightarrow A \\]

and a nullary cell

\\[ \eta_A:()\Rightarrow U_A. \\]

The requirement is that \\(\eta_A\\) be opcartesian: substituting it into any multicell gives a unique factorization through a cell with the corresponding occurrence of \\(U_A\\).

This is representability of empty horizontal strings, not simply the presence of nullary cells.

The units, when they exist, are unique up to unique compatible isomorphism. Consequently, the choice of units is not substantive structure at the level of equivalence.

A consequence is that the category of vertical arrows acquires a canonical 2-categorical structure. Vertical transformations can be represented by cells between horizontal units, and this construction is functorial for normal functors.


Studylib

### Layer R: universal restrictions

Let

\\[ J:A\nrightarrow B,\qquad f:A'\to A,\qquad g:B'\to B. \\]

Require a horizontal arrow \\(J(g,f):A'\nrightarrow B'\\), equipped with a cartesian cell

\\[ \begin{array}{ccc} A'&\xrightarrow{J(g,f)}&B'\\\ {\scriptstyle f}\downarrow&\Downarrow\rho&\downarrow{\scriptstyle g}\\\ A&\xrightarrow{J}&B. \end{array} \\]

Its defining property is the bijection

\\[ \boxed{ \operatorname{Cell}\_{h,k} (P_1,\ldots,P_n;J(g,f)) \\;\cong\\; \operatorname{Cell}\_{fh,gk} (P_1,\ldots,P_n;J) } \\]

for every compatible horizontal string and vertical boundaries \\(h,k\\), naturally with respect to multicell substitution.

Notice that this universal property quantifies over all arities \\(n\geq0\\). An ordinary cartesian-lifting condition on the category of horizontal arrows and unary cells alone would not express the complete requirement.

Restrictions are likewise unique up to unique compatible isomorphism. Their universal property forces coherent comparisons

\\[ J(1_B,1_A)\cong J \\]

and

\\[ \bigl(J(g,f)\bigr)(g',f') \cong J(gg',ff'). \\]

Thus reindexing along vertical arrows is pseudofunctorial, rather than needing separately specified coherence axioms.


Studylib

## 2. The more canonical object is a square

Units and restrictions are logically independent conditions on virtual double categories. Neither must be introduced before the other.

Define \\(\mathbf{vDbl}\_r\\) to be the 2-category of virtual double categories with restrictions and restriction-preserving functors. Let \\(\mathbf{vDbl}\_n\\) denote the unital virtual double categories and normal functors.

Then the natural decomposition is the following square:

\\[ \begin{array}{ccc} \mathbf{vEquip}&\longrightarrow&\mathbf{vDbl}\_r\\\ \downarrow&&\downarrow\\\ \mathbf{vDbl}\_n&\longrightarrow&\mathbf{vDbl}. \end{array} \\]

With the conventional choices of morphisms, this describes the intersection of the two classes of structures, equivalently a corresponding 2-categorical pullback up to the usual coherence choices.

Choosing a route through this square produces a tower of displayed categories. The square itself does not privilege either order.

In particular, the two requirements should be regarded as universal properties defining substructures, while their chosen witnesses provide convenient displayed-category presentations.

## 3. Their interaction reconstructs companions, conjoints, and base change

This is where the decomposition becomes more interesting than an intersection of two properties.

Let \\(f:A\to B\\) be a vertical arrow. Define

\\[ \boxed{ f\_\*:=U_B(1_B,f):A\nrightarrow B } \\]

and

\\[ \boxed{ f^\*:=U_B(f,1_B):B\nrightarrow A. } \\]

These are the companion and conjoint of \\(f\\).

They are derived from units and restrictions. Their comparison cells and companion–conjoint identities follow from the universal properties; they are not an additional independent displayed layer.

Even more importantly, although arbitrary horizontal composites may fail to exist, particular composites involving companions and conjoints necessarily exist.

Given

\\[ J:A\nrightarrow B,\quad f:A'\to A,\quad g:B'\to B, \\]

the horizontal string

\\[ A'\xrightarrow{f\_\*}A \xrightarrow{J}B \xrightarrow{g^\*}B' \\]

has an opcartesian composite, canonically isomorphic to

\\[ \boxed{J(g,f).} \\]

This is Cruttwell–Shulman, Theorem 7.16.


Studylib

So the combined universal properties guarantee a restricted form of horizontal composition, even when arbitrary composition is unavailable.

There is another reconstruction consequence. Every framed multicell can be represented by a globular multicell (one whose vertical boundaries are identities):

\\[ \operatorname{Cell}\_{f,g} (P_1,\ldots,P_n;J) \cong \operatorname{Cell}\_{1,1} (P_1,\ldots,P_n;J(g,f)). \\]

Hence the non-globular cell data are recoverable from globular multicells together with restriction.

This suggests a different presentation of a virtual equipment: a vertical category \\(\mathcal V\\), an indexed family of categories of proarrows

\\[ \mathcal H: (\mathcal V\times\mathcal V)^{\mathrm{op}} \longrightarrow\mathbf{Cat}, \\]

globular multicell operations with coherent substitution/reindexing, and representable nullary units. The indexing pseudofunctor comes from restriction, and the framed multicells can be reconstructed using the bijection above.

That is a potentially more valuable decomposition if the objective is a normal form for the structure rather than simply a tower of axioms.

## 4. The optional representability layer

A virtual equipment is not necessarily an ordinary equipment.

The next possible condition is:

> Every finite composable horizontal string admits an opcartesian composite.

Once this holds, the virtual double category is equivalent to a pseudo double category. For virtual equipments this recovers ordinary equipments (also called framed bicategories).


Studylib

There is therefore an extended hierarchy

\\[ \boxed{ \mathbf{Equip} \longrightarrow \mathbf{vEquip} \longrightarrow \mathbf{vDbl}\_n \longrightarrow \mathbf{vDbl}. } \\]

The first arrow forgets full horizontal representability. Its inclusion should be interpreted with the appropriate strong, rather than merely normal, morphisms if preservation of the chosen composites is required.

### Why the extra layer is not redundant

Consider the multicategory obtained by restricting the usual cartesian multicategory of finite sets to just three objects, of cardinalities \\(1,2,3\\).

Its multimorphisms are functions

\\[ (X_1,\ldots,X_n)\longrightarrow Y \quad\equiv\quad X_1\times\cdots\times X_n\longrightarrow Y. \\]

Regard it as a one-vertical-object virtual double category.

It has a horizontal unit, represented by the singleton. Its restrictions exist trivially, since the only vertical arrow is the identity. Thus it is a virtual equipment.

But the horizontal string \\((2,2)\\) has no representing composite. If it were represented by an object \\(Q\\) among \\(1,2,3\\), then taking target \\(Y=2\\) would require

\\[ |\operatorname{Hom}(Q,2)| = |\operatorname{Multi}(2,2;2)| =16. \\]

However, \\(|\operatorname{Hom}(Q,2)|=2^{|Q|}\leq8\\).

Hence this virtual equipment is not an ordinary equipment.

The last representability layer therefore detects a genuine obstruction.

## 5. What downstream problems does this support?

The most compelling application is the construction of equipments of generalized algebraic structures.

For a virtual double category \\(\mathbb X\\), the construction

\\[ \operatorname{Mod}(\mathbb X) \\]

has monoids as objects and bimodules as horizontal arrows. It always has universal horizontal units. Moreover, if \\(\mathbb X\\) admits restrictions, then \\(\operatorname{Mod}(\mathbb X)\\) admits restrictions.

Thus

\\[ \boxed{ \operatorname{Mod}: \mathbf{vDbl}\_r\longrightarrow\mathbf{vEquip} } \\]

is a systematic construction of virtual equipments from restriction-bearing virtual double categories.

There is even a universal property: \\(\operatorname{Mod}\\) is right pseudo-adjoint to the forgetful 2-functor from unital virtual double categories with normal functors to virtual double categories.


Studylib


For example, starting with spans in a category \\(\mathcal C\\) with pullbacks gives

\\[ \operatorname{Mod}(\operatorname{Span}(\mathcal C)) \simeq \operatorname{Prof}(\mathcal C), \\]

the virtual equipment of internal categories, internal functors, internal profunctors, and multicells.

Crucially, this construction does not require all internal profunctors to be composable; suitable coequalizers are needed to guarantee those composites.


Studylib

For a monad \\(T\\) on a virtual double category with restrictions, Cruttwell–Shulman similarly construct

\\[ \operatorname{KMod}(\mathbb X,T) = \operatorname{Mod}(\operatorname{H\\!-\\!Kl}(\mathbb X,T)), \\]

and show that it is a virtual equipment. This supports generalized multicategories, their morphisms, modules, and normalization constructions.

## 6. The canonicity assessment

The distinctions can be summarized as follows.

| Construction                                           | Status                                                                |
| ------------------------------------------------------ | --------------------------------------------------------------------- |
| Vertical and horizontal data, multicells, substitution | Defining structure of a virtual double category                       |
| Universal horizontal units                             | Intrinsic existence property; choices unique up to unique isomorphism |
| Universal restrictions                                 | Intrinsic existence property; choices unique up to unique isomorphism |
| Companions and conjoints                               | Canonically derived from units and restrictions                       |
| Reindexing and its coherence                           | Canonically derived from restrictions                                 |
| Special composites implementing restrictions           | Guaranteed by the equipment axioms                                    |
| Arbitrary horizontal composites                        | Independent additional representability condition                     |
| Ordering units before restrictions                     | Presentation choice, not an intrinsic necessity                       |

This is a more informative decomposition than a field-by-field algebraic definition because it exposes several theorems connecting the layers.

There are two promising formulations of a canonical answer:

The first is the square of universal-property completions, keeping units and restrictions independent while retaining their compatibility.

The second is a reconstruction from indexed proarrows and globular multicells, with arbitrary framing eliminated by the restriction universal property.

The second seems especially worth pursuing. It would support a precise recognition or reconstruction problem: characterize exactly which indexed multicategorical data extend to a virtual equipment, which coherence conditions are necessary, and whether the resulting reconstruction is an equivalence of appropriate 2-categories.

That is a stronger target than merely observing that virtual equipment axioms can be staged.

Primary reference: G. S. H. Cruttwell and Michael A. Shulman, [A Unified Framework for Generalized Multicategories](https://arxiv.org/abs/0907.2460) (2010), especially Sections 5–7, Theorems 7.16 and 7.24, and Proposition 5.14.


---


Virtual equipments admit a formulation by sketches, and the sketch formulation can expose their structure more directly than a tower of displayed categories. The appropriate starting point is a finite-limit sketch, equivalently an essentially algebraic presentation, with universal units and restrictions encoded by representability conditions.

There is an important distinction between two possible targets:

1. A presentation of virtual equipments with chosen universal witnesses. This can be given by a small finite-limit sketch with countably many arity-indexed sorts and axioms.
2. An intrinsic characterization of virtual equipments as in Cruttwell–Shulman. This should not depend on particular choices of units or restrictions. Recovering the original 2-category requires morphisms that preserve the relevant universal structure up to canonical isomorphism, rather than demanding literal equality of chosen witnesses.

The second is the more canonical target. It is also where a sketch formulation becomes more than a different notation for displayed categories.

The construction below uses Cruttwell–Shulman's Definitions 2.1, 5.1, 7.1, and 7.6, together with their Theorem 7.24.


Studylib


## 1. The underlying finite-limit sketch

Let \\(\mathcal S\_{\mathrm{vDbl}}\\) denote a sketch whose Set-valued models are small virtual double categories.

Begin with three basic sorts:

\\[ O,\qquad V,\qquad H, \\]

representing objects, vertical arrows, and horizontal arrows. Equip \\(V\\) with source, target, identity, and composition operations satisfying the category axioms. Equip \\(H\\) with source and target maps to \\(O\\), but do not specify horizontal composition.

For every \\(n\geq 0\\), introduce a sort \\(P_n\\) of composable horizontal strings, with distinguished finite-limit cones specifying

\\[ P_0=O, \qquad P_n= \underbrace{H\times_O H\times_O\cdots\times_O H}\_{n\text{ factors}} \quad(n\geq1). \\]

For every \\(n\\), define a further finite-limit sort of cell boundaries:

\\[ B_n= \left\\{ (\vec J,K,f,g) \ \middle|\ \begin{array}{l} \vec J\in P_n,\quad K\in H,\\\ f:s(\vec J)\to s(K),\\\ g:t(\vec J)\to t(K) \end{array} \right\\}. \\]

Introduce a sort \\(C_n\\) of \\(n\\)-ary cells, with a boundary map

\\[ b_n:C_n\longrightarrow B_n. \\]

The fiber of this map is written

\\[ b_n^{-1}(\vec J,K,f,g) = \operatorname{Cell}\_{f,g}(\vec J;K). \\]

For \\(n=0\\), the empty string has a single object as both endpoints. Thus \\(C_0\\) includes the nullary cells needed to express horizontal units.

The remaining structure of \\(\mathcal S\_{\mathrm{vDbl}}\\) consists of identity-cell operations and multicell-substitution operations. Each substitution operation has a domain given by a finite pullback specifying the compatible horizontal and vertical boundaries. The sketch imposes the usual associativity, identity, and pasting equations.

This is an essentially algebraic presentation: every operation has finitely many inputs, with its domain determined by finite boundary-matching equations.

In particular,

\\[ \boxed{ \operatorname{Mod}\_{\mathbf{Set}} (\mathcal S\_{\mathrm{vDbl}}) \cong \mathbf{vDbl}\_{\mathrm{str}} } \\]

where the right-hand side denotes the underlying category of small virtual double categories and virtual double functors.

## 2. Extend the sketch by universal horizontal units

Define an extension

\\[ \mathcal S_U\supseteq\mathcal S\_{\mathrm{vDbl}}. \\]

Add operations

\\[ U:O\longrightarrow H, \qquad \eta:O\longrightarrow C_0, \\]

with boundary equations ensuring that, for every \\(A\in O\\),

\\[ U_A:A\nrightarrow A, \qquad \eta_A:()\Rightarrow U_A \\]

and that \\(\eta_A\\) has identity vertical boundaries.

The essential part is the universal property.

Given horizontal strings \\(\vec L,\vec R\\), a compatible target \\(K\\), and vertical boundaries \\(a,b\\), substitution of \\(\eta_A\\) into the indicated slot defines

\\[ \Phi^U\_{\vec L,\vec R}: \operatorname{Cell}\_{a,b} (\vec L,U_A,\vec R;K) \longrightarrow \operatorname{Cell}\_{a,b} (\vec L,\vec R;K). \\]

Require this map to be a bijection for every admissible context \\(\vec L,\vec R,K,a,b\\), including empty strings.

In the sketch, bijectivity can be presented entirely algebraically. For each pair of surrounding arities \\(p,q\geq0\\), introduce an inverse operation

\\[ \Psi^U\_{p,q}=(\Phi^U\_{p,q})^{-1} \\]

between the corresponding finite-limit sorts of compatible cells, and impose

\\[ \Phi^U\_{p,q}\Psi^U\_{p,q}=1, \qquad \Psi^U\_{p,q}\Phi^U\_{p,q}=1. \\]

These are ordinary equations in a finite-limit sketch. The inverse operations are uniquely determined whenever they exist.

This gives precisely the opcartesianness of the nullary cells in Cruttwell–Shulman's definition.

No arbitrary horizontal composites are introduced. The only representability imposed is that of empty horizontal strings.

## 3. Extend the sketch by universal restrictions

Independently define

\\[ \mathcal S_R\supseteq\mathcal S\_{\mathrm{vDbl}}. \\]

Introduce the finite-limit sort

\\[ T= \left\\{ (J,f,g) \ \middle|\ J:A\nrightarrow B,\\; f:A'\to A,\\; g:B'\to B \right\\}. \\]

Add operations

\\[ r:T\longrightarrow H, \qquad \rho:T\longrightarrow C_1. \\]

Their boundary equations specify

\\[ r(J,f,g)=J(g,f):A'\nrightarrow B' \\]

together with a unary cell

\\[ \begin{array}{ccc} A'&\xrightarrow{J(g,f)}&B'\\\ {\scriptstyle f}\downarrow& \Downarrow\rho\_{J,f,g}& \downarrow{\scriptstyle g}\\\ A&\xrightarrow{J}&B. \end{array} \\]

For every \\(n\geq0\\), composition with \\(\rho\_{J,f,g}\\) induces

\\[ \boxed{ \Phi^R_n: \operatorname{Cell}\_{h,k} (\vec P;J(g,f)) \longrightarrow \operatorname{Cell}\_{fh,gk} (\vec P;J). } \\]

The cartesian restriction property is precisely the assertion that \\(\Phi^R_n\\) is bijective for every compatible choice of data.

As before, introduce inverse operations \\(\Psi^R_n\\) and impose

\\[ \Phi^R_n\Psi^R_n=1, \qquad \Psi^R_n\Phi^R_n=1 \qquad(n\geq0). \\]

This is a countable family of finitary equations on finite-limit-defined domains.

It is essential to include every arity \\(n\\). Requiring bijectivity only for unary cells produces a fibration-like restriction property, but does not establish cartesianness relative to arbitrary multicells. That weaker sketch would not characterize virtual equipments.

Notice also what has not been imposed: no equations requiring strict functoriality of restriction, such as

\\[ (J(g,f))(g',f')=J(gg',ff'). \\]

The defining universal property instead produces canonical, coherent isomorphisms. Imposing strict equalities would specify an additional splitting condition, rather than simply presenting the original structure.

## 4. The virtual-equipment sketch is the amalgamation of the two extensions

Define

\\[ \boxed{ \mathcal S\_{\mathrm{vEquip}} = \mathcal S_U \amalg\_{\mathcal S\_{\mathrm{vDbl}}} \mathcal S_R. } \\]

This gives a square of sketch presentations:

\\[ \begin{array}{ccc} \mathcal S\_{\mathrm{vDbl}} &\longrightarrow&\mathcal S_U\\\\[4pt] \downarrow&&\downarrow\\\\[4pt] \mathcal S_R &\longrightarrow&\mathcal S\_{\mathrm{vEquip}} \end{array} \qquad \text{(pushout).} \\]

This reverses the direction of the corresponding forgetful square of categories in the attached document.

Pasted text(20261021-211344).txt

Since models are contravariant in sketch extensions, applying Set-valued model semantics gives

\\[ \boxed{ \begin{aligned} \operatorname{Mod}(\mathcal S\_{\mathrm{vEquip}}) \simeq{}& \operatorname{Mod}(\mathcal S_U)\\\ &\times\_{\operatorname{Mod}(\mathcal S\_{\mathrm{vDbl}})} \operatorname{Mod}(\mathcal S_R). \end{aligned} } \\]

The pullback here is at the level of chosen structures and strict sketch morphisms.

This realizes the independence of the two universal-property layers syntactically. The extensions have the same base sketch, but their new generators and equations can be introduced independently.

No separate interaction axiom is needed to obtain companions, conjoints, or the canonical base-change composites. Those follow from the conjunction of the two universal properties.

For instance, given a vertical arrow \\(f:A\to B\\), the sketch determines

\\[ f\_\*:=U_B(1_B,f), \qquad f^\*:=U_B(f,1_B). \\]

And for a horizontal arrow \\(J:A\nrightarrow B\\), its restriction along \\(f:A'\to A\\) and \\(g:B'\to B\\) is canonically the opcartesian composite

\\[ \boxed{ J(g,f)\cong f\_\*\odot J\odot g^\*. } \\]

Here \\(\odot\\) denotes the particular composite supplied by the universal properties, not an everywhere-defined horizontal composition operation. This is the content of the base-change result in Cruttwell–Shulman, Theorem 7.16.


Studylib

Thus the sketch's modularity does not imply that its two extensions are semantically disconnected: their interaction produces additional structure.

## 5. Recovery of virtual equipments: the morphism issue

There is a precise objectwise recognition statement.

Recognition

For a small virtual double category \\(\mathbb D\\), assuming the relevant choices can be made,

\\[ \boxed{ \begin{aligned} \mathbb D\text{ is a virtual equipment} \quad\Longleftrightarrow\quad \mathbb D\text{ admits an expansion}\\\ \text{to a model of }\mathcal S\_{\mathrm{vEquip}}. \end{aligned} } \\]

In the forward direction, select units and cartesian restrictions; their universal properties supply the unique inverse operations required by the sketch. In the reverse direction, the sketch axioms directly establish the existence of universal units and restrictions.

The model category with strict sketch homomorphisms, however, is not literally the original \\(\mathbf{vEquip}\\).

A strict sketch homomorphism must satisfy equalities such as

\\[ F(U_A)=U\_{FA} \\]

and

\\[ F(J(g,f))=(FJ)(Fg,Ff). \\]

A normal virtual-double functor need not satisfy those equalities for the particular representatives selected in the sketch. It instead preserves units and restrictions up to canonical compatible isomorphisms.

Cruttwell–Shulman's Theorem 7.24 supplies the crucial result: every virtual-double functor between virtual equipments preserves cartesian restrictions, while normality supplies preservation of units.


Studylib

Consequently, the appropriate 2-categorical semantics has:

- Models as virtual equipments with chosen universal witnesses.
- Normal virtual-double functors as 1-cells, with canonical comparison isomorphisms for those witnesses.
- Cruttwell–Shulman transformations as 2-cells.

With these morphisms, forgetting the choices gives a biequivalence with the original 2-category \\(\mathbf{vEquip}\\). The reason is that the groupoid of admissible choices on any fixed virtual equipment is contractible: any two chosen universal witnesses admit a unique compatible comparison isomorphism.

This distinguishes the valid assertion

\\[ \mathbf{vEquip} \simeq\_{\mathrm{bieq}} \mathbf{Mod}\_{\mathrm{weak}} (\mathcal S\_{\mathrm{vEquip}}) \\]

from the generally unjustified assertion that the original 2-category is literally the ordinary category of strict Set-models.

## 6. A more economical indexed sketch

The preceding sketch retains the entire virtual-double-category signature, including framed multicells. The attached document suggests eliminating this redundancy by using restrictions to reconstruct the framed cells from globular cells.

Pasted text(20261021-211344).txt

That leads to a second, potentially more intrinsic presentation.

Start with a vertical category \\(\mathcal V\\) and a pseudofunctor

\\[ \mathcal H: (\mathcal V\times\mathcal V)^{\mathrm{op}} \longrightarrow \mathbf{Cat}. \\]

The category \\(\mathcal H(A,B)\\) contains horizontal arrows \\(A\nrightarrow B\\) and globular unary cells between them. Reindexing is the action of the pseudofunctor.

For each \\(n\geq0\\), introduce globular multicell sets

\\[ M_n(J_1,\ldots,J_n;K) \\]

with composable source arrows and a target \\(K:A_0\nrightarrow A_n\\).

These must be equipped with multicell-substitution operations and compatible actions of vertical reindexing.

In particular, for vertical arrows \\(f_i:A_i'\to A_i\\), an appropriate reindexing operation has type

\\[ \begin{aligned} M_n(J_1,\ldots,J_n;K) \longrightarrow M_n\bigl(&J_1(f_1,f_0),\ldots,\\\ &J_n(f_n,f\_{n-1});K(f_n,f_0)\bigr). \end{aligned} \\]

Its construction in a virtual equipment is explicit: paste the cartesian restriction cells into the horizontal inputs, then factor the resulting framed cell through the cartesian restriction of \\(K\\).

The fundamental decoding operation is

\\[ \boxed{ \operatorname{Cell}\_{f,g} (J_1,\ldots,J_n;K) \cong M_n(J_1,\ldots,J_n;K(g,f)). } \\]

This is what makes the indexed presentation plausible.

There is nevertheless a nontrivial reconstruction obligation. A pseudofunctor \\(\mathcal H\\) and arbitrary globular multicell sets are not sufficient. The reindexing of multicells must be natural in the horizontal variables and compatible with substitution, including the comparison isomorphisms for iterated restrictions.

Without those conditions, the reconstructed framed cells need not admit associative substitution.

Therefore, the indexed formulation is a reconstruction blueprint whose exact coherence axioms must be specified before claiming an equivalence of model 2-categories. The direct finite-limit sketch above already gives the recognition result without this unresolved reduction.

## 7. The optional sketch for ordinary equipments

The formulation also accommodates the distinction between virtual and ordinary equipments.

Starting from \\(\mathcal S\_{\mathrm{vEquip}}\\), one can add chosen representing composites for all finite composable horizontal strings, together with the corresponding opcartesian factorization inverses.

This produces a further sketch extension

\\[ \mathcal S\_{\mathrm{vDbl}} \longrightarrow \mathcal S\_{\mathrm{vEquip}} \longrightarrow \mathcal S\_{\mathrm{Equip}}. \\]

Under model semantics, the arrows become forgetful functors in the opposite direction.

The last extension must remain optional. Adding arbitrary horizontal composition to \\(\mathcal S\_{\mathrm{vEquip}}\\) would exclude genuine virtual equipments that do not have all horizontal composites.

## Conclusion

The sketch formulation is mathematically viable, and its direct form is:

\\[ \boxed{ \mathcal S\_{\mathrm{vEquip}} = \mathcal S\_{\mathrm{vDbl}} + \left\\{ \begin{array}{l} \text{chosen nullary universal units}\\\ \text{with all opcartesian factorization inverses} \end{array} \right\\} + \left\\{ \begin{array}{l} \text{chosen restrictions}\\\ \text{with all cartesian factorization inverses} \end{array} \right\\}. } \\]

This is an essentially algebraic specification by finite-limit-defined sorts, operations, and equations. Each arity requires only finite data, although the complete sketch has countably many arity-indexed axioms.

There are two distinct mathematical achievements here. The direct sketch provides a concrete recognition and presentation theorem for virtual equipments with chosen universals. The indexed sketch offers a more substantial reduction of structural data, potentially eliminating framed multicells altogether.

For the objective of replacing the displayed-category decomposition, the direct sketch and its pushout square are sufficient. For the stronger objective identified at the end of the document—finding a canonical normal form with a reconstruction equivalence—the indexed sketch is the relevant next target, and compatibility between reindexing and multicell substitution is the central proof obligation.

---

A particularly natural example is decomposing the forgetful functor from monoidal categories to categories into a tower of displayed categories.

The important qualification is that the tower is canonical relative to a presentation of the structure, not intrinsically determined by the forgetful functor. The interesting part is that each layer has a distinct mathematical role, including its own morphism data and lifting conditions.

## 1. The factorization problem

Consider

\\[ U:\mathbf{MonCat}\_{\mathrm{strong}}\longrightarrow\mathbf{Cat}, \\]

where the domain consists of monoidal categories and strong monoidal functors.

The problem is to factor \\(U\\) through categories of partial monoidal structures, so that every intermediate projection forgets exactly one layer of structure or coherence.

The answer takes the form

\\[ \boxed{ \mathbf{MonCat}\_{\mathrm{strong}} \simeq E_4\longrightarrow E_3 \longrightarrow E_2\longrightarrow E_1 \longrightarrow E_0=\mathbf{Cat}. } \\]

More precisely, each \\(E\_{i+1}\\) is the total category of a displayed category \\(\mathcal D_i\\) over \\(E_i\\):

\\[ E\_{i+1}=\int\_{E_i}\mathcal D_i. \\]

## 2. What the layers classify

\\(E_0\\)

Categories

Objects are categories \\(\mathcal C\\); morphisms are functors \\(F:\mathcal C\to\mathcal D\\).

\\(E_1\\)

Add a tensor

A displayed object over \\(\mathcal C\\) is a functor \\(\otimes\_{\mathcal C}:\mathcal C\times\mathcal C\to\mathcal C\\).

Over a functor \\(F:\mathcal C\to\mathcal D\\), a displayed morphism is a natural isomorphism

\\[ \phi\_{x,y}:Fx\otimes\_{\mathcal D}Fy \xrightarrow{\sim}F(x\otimes\_{\mathcal C}y). \\]

\\(E_2\\)

Add a unit

A displayed object over \\((\mathcal C,\otimes)\\) is an object \\(I\_{\mathcal C}\in\mathcal C\\).

A displayed morphism adds an isomorphism

\\[ \phi_0:I\_{\mathcal D}\xrightarrow{\sim}F(I\_{\mathcal C}). \\]

\\(E_3\\)

Add coherence isomorphisms

A displayed object consists of an associator and two unitors:

\\[ \begin{aligned} \alpha &: (x\otimes y)\otimes z\cong x\otimes(y\otimes z),\\\ \lambda &: I\otimes x\cong x,\\\ \rho &: x\otimes I\cong x. \end{aligned} \\]

Displayed morphisms are proofs that \\(\phi\_{x,y}\\) and \\(\phi_0\\) respect these isomorphisms.

\\(E_4\\)

Impose coherence laws

The displayed objects are proofs of the pentagon and triangle identities.

The displayed morphisms introduce no additional data: preservation of the constraints was already enforced at \\(E_3\\).

Thus \\(E_4\\) is equivalent to the category of monoidal categories and strong monoidal functors.

## 3. Why this is a substantive decomposition

The tower does more than split a long definition into short definitions.

It turns the problem of constructing a monoidal structure into a sequence of relative extension problems:

\\[ \text{tensor} \\;\rightsquigarrow\\; \text{unit} \\;\rightsquigarrow\\; \text{constraints} \\;\rightsquigarrow\\; \text{coherence}. \\]

At each stage, given an object of \\(E_i\\), the fiber of \\(E\_{i+1}\to E_i\\) describes the possible extensions.

These fibers can be empty, have multiple objects, or contain morphisms between different choices. In particular, the final fiber is either empty or contains essentially just a proof of coherence (in a setting where the laws are propositions).

A concrete obstruction exists. Take the one-object category \\(B(\mathbb Z/2)\\), with tensor given by addition on morphisms, identity unitors, and associator given by the nonzero element \\(a=1\in\mathbb Z/2\\). This defines an object in \\(E_3\\), but the pentagon requires \\(2a=3a\\), which fails. Hence it does not lift to \\(E_4\\).

The displayed morphisms also matter. Simply requiring the underlying functor to preserve the tensor strictly would replace strong monoidal functors with a different class of morphisms. The tensor and unit comparison isomorphisms must appear as data in the tower.

## 4. What is canonical here?

There are three distinct claims:

1. Factorization: The composite of the displayed-category projections recovers \\(U\\), up to equivalence.
2. Classification: Each intermediate total category classifies a specified kind of partial monoidal structure, including its appropriate morphisms.
3. Canonicity: The dependency structure motivates the layers, but does not uniquely determine their order or granularity. For instance, tensor and unit can be introduced simultaneously, and the associator and unitors can be introduced independently before imposing the coherence laws.

The first two claims are mathematically substantive. The third is relative to a chosen presentation; there is no uniqueness theorem for this particular tower merely from specifying \\(U\\).

## 5. This is also an actual formalized construction

Wullaert, Matthes, and Ahrens construct the bicategory of monoidal categories by stacking displayed bicategories over \\(\mathbf{Cat}\\), introducing the tensor, unit, associator, unitors, coherence laws, and finally strongness of monoidal functors. The bicategorical version retains monoidal natural transformations as 2-cells.


DROPS


The paper is [Univalent Monoidal Categories](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.TYPES.2022.15), particularly Section 2 and Figure 1.

The broader framework is due to Ahrens and Lumsdaine, [Displayed Categories](https://lmcs.episciences.org/5252).


Displayed Categories

The general pattern is: given a structured category \\(\mathcal S\\) with a forgetful functor \\(\mathcal S\to\mathcal B\\), and a dependency-stratified presentation of the structure, construct a tower of displayed categories whose total category recovers \\(\mathcal S\\). Each fiber solves one relative structure-extension problem, and each displayed morphism records the corresponding preservation or comparison data.

That is a setting in which a tower of displayed categories is not merely a convenient encoding: it is the natural modular solution to the decomposition problem.