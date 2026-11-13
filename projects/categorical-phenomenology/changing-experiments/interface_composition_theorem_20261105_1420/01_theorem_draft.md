# Exact change of experimental interface versus composition

## 1. Supplied data and variance

All indexing categories are small. For a fixed arity n≥1, supply categories A_0,…,A_n and B_0,…,B_n, composition functors W:∏A_i→A_0 and V:∏B_i→B_0, interface translations u_i:A_i→B_i (including i=0), and a natural transformation

    χ: V ∘ (∏u_i) ⇒ u_0 ∘ W.

The direction of χ is essential. Its component is an actual admitted comparison V(u_i a_i)→u_0(W(a_i)); invertibility is not assumed. This data is a square with a directed cell, not a contextad. Native associativity and higher cells would require further supplied structure.

A Set-valued partial-characterization diagram X_i:B_i→Set transports an admitted piece of evidence along an interface refinement. No claim is made that every characterization in the prior programme has this variance. Contravariant experiment semantics can be handled by explicitly taking opposite categories. Model-vocabulary reducts have their own, opposite-to-program-compiler variance: a reduct R:M_new→M_old is applied to model-indexed diagrams before this theorem, not confused with u_i.

Define composition by the pointwise left Kan extension

    Comp_V(X_1,…,X_n) = Lan_V(⊠X_i),
    (⊠X_i)(b_1,…,b_n)=∏X_i(b_i).

At b∈B_0 it is the colimit over the decomposition category (V↓b). Its objects are tuples (b_i,f:V(b_i)→b), and an arrow β:(b_i,f)→(b'_i,f') is a tuple β_i:b_i→b'_i with f=f' V(β_i). Thus no unstated independence or free copying is asserted: the composition functor and its admitted decompositions are part of the source data.

There is a canonical comparison

    Θ_X: Lan_W(⊠u_i*X_i) ⇒ u_0*Lan_V(⊠X_i).

This is change-then-compose → compose-then-change. At a∈A_0 it is induced by the functor

    K_a:(W↓a)→(V↓u_0a),
    (a_i,k) ↦ (u_i a_i, u_0(k) χ_(a_i)).

The naturality of χ makes K_a a functor. The diagram in the source colimit is exactly the target diagram precomposed by K_a. Hence Θ exists without any exactness assumption.

## 2. Concrete lifting categories

For a tuple b_i∈B_i and f:V(b_i)→u_0a, define Fact_a(b_i,f) as follows.

Objects are tuples (a_i,h_i:b_i→u_i a_i,k:W(a_i)→a) satisfying

    f = u_0(k) χ_(a_i) V(h_i).

A morphism from (a_i,h_i,k) to (a'_i,h'_i,k') is a tuple α_i:a_i→a'_i satisfying

    h'_i=u_i(α_i)h_i,     k=k'W(α_i).

These conditions ensure the same f by naturality of χ. This category is precisely ((b_i,f)↓K_a). Connected means that the underlying undirected graph has one connected component, not that the arrows are invertible.

## 3. Main theorem, Set-valued version

The following are equivalent.

1. Θ_X is an isomorphism for every family X_i:B_i→Set.
2. For every a, K_a is final.
3. Every Fact_a(b_i,f) is nonempty and connected.

The equivalence of 2 and 3 is the ordinary comma-category criterion for finality. The content needed for this application is that the restricted class of external-product diagrams in 1 detects this criterion.

### Proof

For 2⇒1, finality preserves colimits of all Set-valued diagrams on (V↓u_0a), in particular the diagrams (b_i,f)↦∏X_i(b_i).

For 1⇒3, take covariant representables X_i=B_i(b_i,−). The co-Yoneda lemma gives

    (Lan_V ⊠X_i)(u_0a) ≅ B_0(V(b_i),u_0a).

An elementary proof avoids any variance ambiguity: a colimit representative (b'_i,g,x_i:b_i→b'_i) maps to g V(x_i). Every arrow f is represented by (b_i,f,id), and every such representative has the arrow from this canonical representative that identifies them in the colimit.

A source representative is (a_i,k,h_i:b_i→u_i a_i), and Θ maps it to u_0(k)χ V(h_i). Colimit identifications are generated exactly by the displayed morphisms in Fact. They cannot connect representatives with different composite f. Consequently the fiber of the map Θ over f is exactly π_0 Fact_a(b_i,f), the set of connected components of that category. Bijectivity says precisely that each such fiber is a singleton. This means nonempty and connected, proving 3.

This proof also isolates the exact failures. An empty factorization category is a missing compatible experiment, causing failure of surjectivity on a representable test. Two or more components are incompatible ways of realizing the same changed experiment that no admitted refinement connects, causing failure of injectivity. Merely proving that every experiment lifts is insufficient.

## 4. Logical existence and retained witnesses are different doctrines

For Bool-valued diagrams, viewed as monotone truth values, composition is the corresponding join of finite meets. Then universal exactness is equivalent to the following weaker existence condition: whenever B_0(V(b_i),u_0a) is nonempty, the disjoint union over its arrows f of the objects of Fact_a(b_i,f) is nonempty. Necessity uses representable truth predicates, true at b' iff an arrow b→b' exists. Sufficiency: any true target composite supplies true inputs at some b_i and an arrow f; the condition supplies some (possibly different) arrow with a lift. Its h_i makes the input truths true at u_i a_i by monotonicity, giving a true source composite. The reverse implication is supplied by Θ. In thin categories, there is at most one f and this reduces to nonemptiness of each Fact category. This Bool statement does not assert that arbitrary witnesses have been identified correctly.

For native categorical witnesses, choose strict functors E_i:B_i→Cat and retain the Grothendieck category

    WComp_V(E_i)(b) = ∫_(V↓b) ∏E_i(b_i).

An object consists of a decomposition and actual evidence objects. A morphism includes the admitted decomposition arrow and the actual arrows E_i(β_i)e_i→e'_i. These arrows may be genuinely noninvertible. This is a witness-retaining category, not a claim that its objects are a category of all physical executions without further semantics.

K_a induces a canonical functor J_E between the source and target Grothendieck categories. For every a, the following are equivalent:

1. J_E is an equivalence of categories for every E_i:B_i→Cat.
2. K_a is an equivalence of categories.

Necessity uses all E_i=1, for which J_E=K_a. For sufficiency, an equivalence K admits a quasi-inverse L and natural isomorphisms LK≅id, KL≅id. Applying the target diagram to those isomorphisms and using the ordinary Grothendieck construction gives quasi-inverse total-category functors and their natural isomorphisms. Alternatively fully faithfulness follows from that of K and the unchanged vertical hom sets; essential surjectivity is obtained by transporting each evidence object along an isomorphism from an object in K's image.

Finality is therefore sufficient for extensional Set-colimits but not for retaining witnesses up to equivalence. Even contractibility of each factorization category is not a witness-equivalence theorem. One must not invert noninvertible arrows simply because their connected component is a singleton.

## 5. Coherence

For a second square (B,V)→(D,Z) with maps v_i and ψ:Z(v_i−)⇒v_0V, the composite cell is

    Z(v_i u_i−) --ψ_(u_i−)→ v_0V(u_i−) --v_0χ→ v_0u_0W.

Its induced decomposition functor equals K^v_(u_0a) K^u_a. Consequently the composite mate is the composite of the two mates after the evident reindexings. This can be checked directly on a representative (a_i,k,x_i): the image arrow is v_0u_0(k) v_0χ ψ, and naturality of ψ identifies the two routes. Identity squares give identity mates; associativity of three stages is ordinary associativity of these composites. Finality and equivalence are closed under composition, so exact interface changes compose in their respective doctrines.

This proves coherence for the supplied composition square and successive interface changes. A many-operation operad, feedback, or contextad is not obtained for free. If a family of W,V and χ is supplied coherently for an operad, the same uniqueness/representative calculation verifies the inherited finite substitution coherences.

## 6. Attribution and separation from the prior project

The general mechanism is standard pointwise Kan extension, co-Yoneda, final functors, and Beck–Chevalley/Guitart exactness. These should be credited as established mathematics. The project-specific payoff is the actual interface square, its exact lift categories, the resource classification below, and the separation of feasibility, extensional characterizations, and retained witness categories.

This is not the prior regular-image quotient/wiring theorem. That theorem starts from a fixed experimental semantics, quotients state carriers, and compares realizable reduced profiles with exterior behavioral states. Here the input is a changed category of admitted experimental decompositions, and the obstruction can exist before any state quotient. Nor is it the prior reconstruction-of-operations theorem, whose naturality ends can fail to commute with a change of enrichment. Nor is it the manufacture/join comparison: addition-budget convolution has a different exactness criterion.
