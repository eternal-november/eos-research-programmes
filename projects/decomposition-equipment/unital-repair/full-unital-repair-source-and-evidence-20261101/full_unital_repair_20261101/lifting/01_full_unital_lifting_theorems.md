# Full unital lifting and coefficient transport

## Purpose and conclusion

This repair keeps the authorized full cut grammar, including the vertex-free identity tree. For a unital monoid homomorphism, preservation of identities does not imply sourcewise lifting of that tree. The exact general test is the existing correlated shared-parent lifting condition **and identity reflection**. In the full branching coefficient model this becomes a sharper theorem: lifting at every source for every tree is equivalent to an injective map with factor-closed image. Proper quotient compression therefore fails in that model for all monoids, not merely groups. This does not rule out non-surjective interfaces or nontrivial compression in a genuinely nonbranching graph subfamily.

All assertions are over the same exact old records as the I1 and I2 sources. Full profiles, ordered occurrences, empty inputs, interfaces, retained intermediate factors and prescribed old cut trees remain data. Original files have not been changed.

## Fixed definitions

Let P be the old ordered-partition graph calculus. For a monoid D, P[D] has operations (a,(x_j)) with one D-coordinate per nonempty input occurrence. Composition multiplies coefficients along each active root-to-final-leaf path, with one common coefficient on an edge above several descendants. Empty input occurrences carry no coefficient. In this geometry every active edge has an active final descendant; a nonempty graph cannot disappear into empty inputs. Nullaries occur at the empty graph.

For an actual old finite tree T and prescribed decorated source x, write W_D(T,x) for all literal coefficient arrays on its operation-input edges whose evaluation is x. The tree determines every retained intermediate composite; equivalently these composites may be recorded explicitly and checked against the array. A forest record uses compatible such arrays at all marked entries. The notation does not identify different trees or erase intermediate factors merely because their total composites agree.

A vertex-free tree has no operation-input edges. At a nonempty color H it is unary and evaluates to (id_H,1_D), not to an arbitrary decorated unary operation (id_H,x). Thus

    W_D(unit_H,x) = {()} if x=1_D, and is empty otherwise.       (U)

At an empty color there is no coefficient and its actual vertex-free identity has the unique empty array. A nullary operation vertex and a unary operation vertex with old operation id_H are both different trees from unit_H.

Let h:D->E be a unital monoid homomorphism, applied uniformly to all active coordinates. The old geometry is unchanged throughout the main coefficient theorem. The same argument applies over an independently supplied source-fixed old-tree lift with the needed occurrence compatibility; coefficient tests cannot provide that geometric lift themselves.

The full lifting property means: for every allowed T, every concrete source x, and every prescribed E-array w in W_E(T,h(x)), there is an array v in W_D(T,x) with h(v)=w entrywise, including every retained intermediate entry. It is existential source-fixed lifting, not endpointwise unique lifting unless uniqueness is proved separately.

## Old skeleton lifting with the correct base case

For a positive-vertex actual old tree T and any source label tuple, decorate each active edge incident with a final active input by that input's prescribed coefficient and every other active edge by 1. Each active path has such a final edge and evaluates to the prescribed coefficient. This proves the old-skeleton lift for every monoid, without inverses.

For a vertex-free old tree there is no such edge. Its lift exists exactly at the actual decorated identity, by (U). Forgetting coefficients always takes an existing decorated cut to the old cut. The all-unit section preserves and reflects old cut existence for every tree, including vertex-free trees. The stronger claim that every decorated source over the same old identity admits that zero-tree is false. Adding a unary operation vertex changes T and is not a repair of its fibre.

## The exact correlated monoid criterion

For q,r in E and x in D with h(x)=qr define

    L_h(q;x,r) = {p in D : h(p)=q and some v in D has
                            h(v)=r and pv=x}.

A realizable shared-parent instance consists of one prescribed target outer coefficient q, target child coefficients r_1,...,r_k, and independently prescribed concrete descendant source coefficients x_1,...,x_k, where h(x_j)=q r_j. Its exact lifting condition is

    intersection over j of L_h(q;x_j,r_j) is nonempty.         (SP)

Here k is positive: the nonerasing old geometry gives an active descendant to every active parent. Inactive and empty positions remain in the old record but contribute no invented coefficient condition.

**Theorem 1.** Assume all the indicated local shared-parent instances occur among the allowed two-level cuts, and that actual old unary identities admit the vertex-free tree. Then h has full lifting if and only if:

1. (SP) holds for every geometrically realizable shared-parent instance; and
2. h^{-1}(1_E)={1_D}.                                         (IR)

For a restricted old class, interpret (SP) only on its actual instances. Testing all formal tuples is a sufficient condition, but failure on a nonrealizable tuple is not a counterexample to that restricted class.

**Proof of necessity.** A lifted instance supplies a single parent p in every displayed L-set. At the old nonempty unary identity, if h(x)=1, the target vertex-free tree exists. Its source lift is vertex-free and therefore has source 1 by (U). Hence x=1.

**Proof of sufficiency.** Induct on a target tree, keeping its exact old skeleton. For a zero tree, (IR) and (U) give its unique source lift. A one-vertex tree lifts by its prescribed source coefficients. At a positive composite, collapse the chosen immediate child subtrees to their target composites. For each active input of the top vertex, use (SP) to choose one shared concrete parent p and concrete child root coefficients v_j satisfying p v_j=x_j and h(v_j)=r_j. Distinct input groups are disjoint occurrences. For each child subtree recurse at these very concrete root coefficients, rather than at unrelated representatives. If a child subtree is vertex-free, (IR) makes its chosen coefficient 1, so the induction base applies without inserting a new vertex. Empty/nullary positions invoke the exact old record and no label choice. Every vertex and retained intermediate composite is kept. This constructs one compatible array for the entire target tree. Finite forests and nested marked records follow by the same occurrencewise gluing, provided their only sharing is the declared tree incidence. Extra cross-sibling equations would require additional constraints and are not asserted here. QED.

For finite D,E, the uniform all-tuples test is finite. For fixed q only the at most |D||E| distinct admissible pairs (x,r) matter; repeating a constraint does not change an intersection. Check every nonempty subset of these constraints and (IR). This can be exponential but covers every finite arity. When only certain arities or geometries occur, the exact necessary-and-sufficient test uses the realizable constraint lists. The finite sufficient all-tuples test does not solve an unrelated presentation-realizability problem.

## The branching theorem and its sharp meaning

Assume the old class contains a nonempty graph with an actual partition into two nonempty inputs. Allow arbitrary coefficient tuples on that old operation, the outer unary old identity above it, and unrestricted unary binary factorizations at a nonempty color. These hypotheses hold in the original graph class once graph size at least two is available.

Call a submonoid I of E factor-closed when

    ab in I implies a in I and b in I.                         (FC)

**Theorem 2.** In this branching class, the following are equivalent:

(a) h has full source-fixed lifting for every actual finite cut tree;
(b) h is injective and h(D) is factor-closed in E.

Every lift in (a) is then unique on coefficients. Surjectivity is not required.

**Proof of (a) implies (b).** Theorem 1 gives (IR). If h(x)=h(y)=q, decorate the chosen two-input old source by (x,y). In the target use outer unary coefficient q and the chosen inner two-input operation with both coefficients 1_E. Its composite is (q,q), so it is an actual target cut at h(x,y). In a lift, the two child coefficients v,w have h(v)=h(w)=1; (IR) forces v=w=1. The single shared parent p consequently satisfies p=x and p=y. Thus x=y. This proves injectivity; it is not an extra assumption smuggled into an existential property.

If ab=h(x), the target unary two-factor cut (a,b) at h(x) has a lift (p,v). Hence a=h(p), b=h(v) both belong to the image. This proves (FC).

**Proof of (b) implies (a).** On every active root-to-final-leaf path the product of the prescribed target factors is h(x_j), an image element. Iterating (FC) shows that every factor on that path is in h(D). Every active edge lies on such a path. Apply the unique inverse of h on its image to each active edge. The path products map to h(x_j), and injectivity makes their concrete products equal x_j. This lifts all shared edges consistently, all intermediate composites and all marked records. For the vertex-free case injectivity and h(1)=1 give (IR). Inactive/empty positions are unchanged. Uniqueness follows edgewise from injectivity. QED.

**Consequences.** A surjective coefficient quotient in this branching class has full lifting exactly when it is an isomorphism. This is a theorem for arbitrary monoids. It does not assert that every profile-dependent observational quotient must be discrete: that larger claim would need a separate proof, because a zero-tree predicate applies to an actual identity old record, not indiscriminately to every multi-input coefficient tuple.

A nontrivial non-surjective full-unital interface remains possible. For any monoid D, let B={1,0}, with 0 absorbing, and use

    i:D -> D x B,             i(d)=(d,1).

The map is injective. If (a,b)(c,d) belongs to D x {1}, then bd=1; in B this forces b=d=1, so its image is factor-closed. Theorem 2 gives unique all-tree lifting at every source in its image, including units. For finite nontrivial D this is a finite, noninvertible interface preserving all full records. This replaces the invalid blanket suggestion that all useful noninvertible maps can be proper group quotients.

An injective map without factor closure still preserves all records and reflects records whose factors are all local, but need not lift foreign-factor cuts. The I1 embedded-module theorem remains exactly that filtered statement. It should not be strengthened to unrestricted fullness.

## Groups and the explicit failed compression

For groups, positive-tree lifting at all sources is equivalent to surjectivity. Necessity uses the target binary factorization 1=q q^{-1} at concrete source 1. For sufficiency, for any shared-parent constraints choose p in h^{-1}(q) and put v_j=p^{-1}x_j. Then h(v_j)=r_j and one p works for all descendants.

Full-unital lifting additionally requires (IR), which for groups is trivial kernel. It is therefore equivalent to an isomorphism, even in the nonbranching unary geometry. This unary group result does not require Theorem 2's branching hypothesis.

For h:C4^2->C2^2 given by componentwise reduction modulo two, the concrete old unary identity with source label (2,0) maps to the target identity (0,0). Its target zero-tree fibre is {()}, whereas its concrete zero-tree fibre is empty. Concrete source (0,0) has fibre {()} and has the same h-image. Thus no cut relation at the shared encoded state can satisfy I2 equation (E) at both representatives. This is an exact-may failure even when no concrete factor endpoints are prescribed.

## Coherent forward transport and the retained twisted comparison

Every unital homomorphism maps coefficient arrays entrywise. Products are preserved, so it maps existing cuts and retained intermediate entries to valid target records. It commutes with tree insertion, contraction, forest composition and reindexing of unchanged ordered occurrences. Its zero-tree map is the unique map on the empty array at the actual identity. These assertions are preservation statements and need no (IR).

When Theorem 2 applies, its unique inverse on every source fibre commutes with these tree maps wherever their sources and targets are defined: applying h to both possible composites gives the same target record, and coefficientwise injectivity identifies them. This includes inserting/deleting genuine units and the zero-tree base. For general noninjective maps satisfying Theorem 1, surjectivity of these fibre maps alone does not license a coherently chosen inverse; the existence proof must not be advertised as such a choice.

The I1 semidirect comparison is unaffected. Let C=A semidirect B under alpha:B->Aut(A), with (a,b)(c,d)=(a alpha_b(c),bd). For an active edge e let beta_e be its strict ancestor B-product and set t_e=alpha_(beta_e)(a_e). The existing path expansion and edgewise inverse give

    W_C(T,(x,y)) ~= W_A(T,x) x W_B(T,y).

For a vertex-free tree both sides are singleton precisely when x=1_A and y=1_B, and empty otherwise. For an empty color all three coefficient arrays are empty and the same old feasibility guard applies. Thus this is genuinely an all-tree bijection, not a positive-only one.

For insertion below ancestor prefix gamma, transport every inserted intrinsic A-coordinate by alpha_gamma. A unit insertion has intrinsic coefficient 1 and alpha_gamma(1)=1. A vertex-free identity inserts no operation-input edges and changes no prefix. For contraction,

    alpha_gamma(a) alpha_(gamma b)(c)
       = alpha_gamma(a alpha_b(c)),

while B-coordinates multiply to bd. A unit contraction is its identity instance. If contraction deliberately forgets a marked factorization, the resulting map need not be injective; it still commutes with the comparison. No normalization crosses a retained marked boundary. These identities retain all previous I1 insertion, flattening and refinement-certificate proofs, and add the missing zero-tree base rather than changing their statement to a smaller grammar.

For coefficient interface pairs f,g, the existing conditions that f,g are unital homomorphisms and f alpha_b=alpha'_(g(b)) f still give forward transport. All old full-profile, occurrence, grade, interface and substitution squares must still be checked. For full source-fixed reflection apply Theorem 1 to the actual combined monoid map, and Theorem 2 when its branching hypotheses hold. Composition of full-lifting maps again has full lifting by successive source-fixed lifts; identities do as well. Identity reflection and the finite tests must therefore be recorded separately from the old preservation/equivariance conditions.
