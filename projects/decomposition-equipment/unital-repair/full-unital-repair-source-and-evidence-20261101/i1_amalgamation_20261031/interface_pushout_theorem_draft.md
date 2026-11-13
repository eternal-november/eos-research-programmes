# Bare finite-monoid interface pushouts: exact collapse and sharp repair

## Scope

This is a coefficient-level theorem, not a standalone occurrence-forest/coherence theorem. It supplies genuine bare pushouts, not a quotient obtained by imposing a separately chosen mixed law. Any graph lift remains conditional on the independently proved graph/certificate companion theorem.

Composition is `fg = f ∘ g`. Fix an integer m≥0, let D={*,1,…,m}, E={z}, and regard all maps below as partial maps on D⊔E. Write 0 for the empty map and 1 for the identity on D⊔E. Let

- y_S be the partial identity on {*}∪S, for S⊆[m];
- p=y_∅;
- e=id_E;
- c:z↦*.

Then A_m={0,1,e,c}∪{y_S:S⊆[m]} is a monoid of order 2^m+4. Its nontrivial rules are

    y_S y_T = y_(S∩T),   y_S c = c,   c y_S = 0,
    e y_S = y_S e = 0,   c e = c,   e c = c² = 0,
    e²=e,

with 0 absorbing and 1 the identity.

Let C={0,1,e,d,c} be the five-element monoid with d²=d, dc=c, ce=c, e²=e, and all other products among {e,d,c} zero. Let B={0,1,e,d,c,u} be the two-by-two matrix-unit monoid with external identity: on {*,z}, d=id_{*}, e=id_z, c:z↦*, u:*↦z. In particular cu=d, uc=e, du=0, ud=u, eu=u, ue=0, u²=0.

For each J⊆[m], the assignment d↦y_J, fixing 0,1,e,c, defines an injective monoid homomorphism i_J:C→A_m. The other leg is the evident inclusion C→B. Both input theories admit finite convergent multiplication-table presentations: take all nonidentity elements as generators and replace each adjacent pair by its product (the empty word if the product is 1). Length strictly decreases; associativity resolves all length-three overlaps; normal forms are the empty word or a single nonidentity generator.

## Theorem

The bare monoid pushout P_J=A_m ⊔_C B has exactly

    |P_J| = 2^m − 2^|J| + 6

 elements. Its canonical A_m map identifies precisely the elements in

    I_J={y_S:S⊆J}

with each other, and makes no other identifications. Its canonical B map is injective. Consequently the two input maps are both injective exactly when J=∅. For J=∅ their images intersect exactly in the common C-image.

### Step 1: the repaired pushout P_∅ is concrete

Adjoin to the partial-map monoid A_m the single partial map u:*↦z. The set

    M=A_m∪{u}

is closed, with |M|=2^m+5. Besides the input products its only new products are

    u y_S = u,   y_S u = 0,   cu=p,   uc=e,
    eu=u,   ue=0,   u²=0,

and the identity/zero products. Thus A_m embeds literally, while B embeds by d↦p and the indicated maps for its other elements.

To prove universality, let f:A_m→H and g:B→H agree on C for the embedding d↦p. A function M→H extending f and g is unique because M is their set-theoretic union. All products within each input are respected. The only remaining pairs are y_S,u in either order, and their products are forced:

    g(u) f(y_S) = g(u) f(p) f(y_S) = g(u) f(p) = g(u),
    f(y_S) g(u) = f(y_S) g(e) g(u) = f(0) g(u) = g(0).

Here up=u, py_S=p, eu=u, y_Se=0, and the common 0 is also B's zero. This proves that the extension is a homomorphism and proves the pushout property. No assumption that f or g sends its zero to a globally absorbing element of H is needed.

### Step 2: exact quotient for arbitrary J

On M put the equivalence relation that collapses I_J to one class and leaves every other element a singleton. It is a monoid congruence: multiplication by y_T sends every member of I_J to a member of I_J; multiplication on either side by c,e,u,0,1 either gives a fixed value independent of S or stays inside I_J. Explicitly, for y_S∈I_J the c-products are c and 0, the e-products are both 0, and the u-products are 0 and u. Denote the quotient by Q_J.

A_m→Q_J and B→Q_J (sending d to [p]=[y_J]) agree on C. Conversely, given any compatible f:A_m→H and g:B→H for i_J, the input equations force

    f(p)=f(p y_J)=f(p)g(c)g(u)=g(c)g(u)=f(y_J),

where pc=c. Therefore for every S⊆J,

    f(y_S)=f(y_S y_J)=f(y_S)f(p)=f(p).

Also f(p)=g(d), so the same f,g are compatible for i_∅. Step 1 gives a unique homomorphism M→H, and the preceding identities show that it factors uniquely through Q_J. Thus Q_J is the required pushout P_J. The explicitly defined quotient has only the stated identifications. Counting gives |Q_J|=(2^m+5)−(2^|J|−1).

**Important distinction.** This is an ideal collapse in the meet-semilattice, not deletion of the coordinates in J. For example with m=2 and J={1}, y_∅=y_{1}, but y_{2} and y_{1,2} remain distinct.

## Full-interface failure and same-theory repair

For J=[m] and m≥1, all 2^m distinct y_S collapse. The pushout is isomorphic to B and has order 6. This failure is arbitrarily large even though each input has a finite convergent multiplication-table presentation and the shared interface is the same nontrivial five-element monoid.

The obstruction is already a mixed peak in the literal union of those presentations:

    y_S c u  →  c u  →  d,
    y_S c u  →  y_S d  →  y_S.

For S≠[m], d and y_S are distinct pure-A normal forms. Their equality in the pushout is forced solely by identifying the common C generators; no additional mixed equation was imposed.

Keep exactly the same abstract A_m, B and C theories, but change the embedding C→A_m from d↦y_[m] to d↦p. Then the pushout is the concrete M above, and both inputs embed faithfully. In the displayed peak the right branch now ends at y_Sp=p, so it joins the left branch. This is a repair of the interface embedding, not a claim that all possible interface embeddings are safe.

The exact criterion in this family is J=∅. The J≠∅ obstruction always includes p≠y_J in A_m but p=y_J in P_J. The repaired case also has an elementary finite convergent global multiplication-table presentation. These coefficient facts alone do not establish refinement-path coherence, retained-forest certificates, cut fullness, or interface reflection for a graph formalism.
