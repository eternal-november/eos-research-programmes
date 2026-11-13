# Exact scalar memory in original C5 cut trees

Author proof candidate, 29 October 2026.

## Abstract

The quotient classified in the companion theorem preserves actual refinement lifting, but that does not mean a prescribed normalized cut lifts with all its inner labels still equal to one. A missing unit scalar may have to be placed at an intermediate component. For a fixed original cut tree we calculate exactly all such placements, and retain the actual original invertible scalar operations as comparisons between them. The resulting groupoid is contractible, while its set of actual factorizations can have arbitrarily many distinct elements. Empty components carry no such freedom. This isolates precisely the scalar information a cut repair must retain; it does not fix the independent coefficient obstruction under noninvertible interface changes.

## 1. Fixed objects, not inferred trees

Use the original C5 presentation and subgroup H<=M^× from `C5_Fixed_Endpoint_Kernel_Classification.md`. Fix an ACTUAL flattened original operation

    w=(G; ordered partition pi; full grade path; m).

Fix a finite rooted planar cut tree T factoring its ordered occurrences. The tree retains all actual occurrence locations, including empty and repeated components; every intermediate component is the induced graph on the union of its descendant blocks, with the composite of their contiguous grade path. Nullary vertices are permitted only at the original empty/id profiles. Unary vertices are permitted. Leaves are the original external occurrences, not internal scalar-decorated nodes.

At each internal vertex v the graph-cut partition and complete profile are fixed by this data and the original increasing-enumeration rules. Thus only scalar labels vary. Let root denote the root internal vertex. The normalized factorization has root scalar m and every nonroot internal scalar 1. It evaluates to w by the original R,UL,UR,DA,DL,DR laws. We do not identify an empty-color external leaf with a nullary node.

A **lift of its normalized quotient factorization** means an actual scalar-labeled factorization of w whose labels at each vertex belong to the specified quotient classes: the root lies in [m], and each nonroot internal label lies in [1] for its output graph. This fixes the flattened actual root witness w. It does NOT additionally fix the scalar of the outermost factor operation.

If there are no internal vertices, there is only the given identity factorization, and no scalar-choice statement is needed.

## 2. Exact object fibre

Let V_+(T) be the nonroot internal vertices whose output graphs are nonempty, and r=|V_+(T)|.

**Theorem 1.** The actual lift set is canonically parametrized by H^r. Choose h_v in H at each v in V_+(T); put scalar 1 at every other nonroot internal vertex; put

    x_root = m (product_(v in V_+(T)) h_v)^(-1).           (1)

These and only these are the actual lifts. For finite H their number is |H|^r.

**Proof.** The scalar class of 1 is H at positive graph grade and {1} at zero graph grade, by the classification. The original scalar evaluation of any tree is the product of its vertex scalars, derived by DA and repeated DL/DR, with units removed by UL/UR without deleting scalar-bearing old nullaries. All nonroot variable factors are units. Requiring total product m therefore forces exactly (1), without cancellation by m. Conversely the displayed labels multiply to m and the root belongs to [m] whenever G is nonempty. If G is empty, every descendant graph is empty, r=0 and all labels are fixed. QED.

If the OUTERMOST factor scalar is also fixed to m, then the allowed markings instead satisfy

    product_v h_v in Stab_H(m)={h in H : mh=m}.             (2)

For r>0 this subset has size |H|^(r-1)|Stab_H(m)| when H is finite. For r=0 it is a singleton. One must not replace (2) by product h_v=1 unless the H action at m is free. For example an absorbing m is fixed by every h in H.

## 3. The actual original gauge arrows

For every positive intermediate component W, the original unary D(W,g), g in H, is invertible with inverse D(W,g^-1), by DA and D0. It remains an ACTUAL comparison, not a quotient identity, in this section.

Assign g_v in H to each positive internal edge, equivalently each v in V_+(T). Put g_v=1 on every zero-grade internal edge and g_root=1. A gauge transforms vertex scalar labels by

    x'_v = x_v g_v (product_(c internal child of v) g_c)^(-1).
                                                               (3)

For the root use g_root=1. An external leaf has no gauge. Positive children cannot have zero-grade parents, because actual graph cuts conserve the vertex sum. Therefore nonroot zero-grade vertices remain scalar 1 under (3), while a zero-grade root retains its supplied scalar m.

Equation (3) is precisely the nodewise naturality equation for the original unary comparisons D(W,g_v). Move a child's scalar through the binary assembly by DL or DR, and combine by DA; R makes the resulting equation independent of the binary bracketing of a higher-arity node. The unit equations cover nullary/empty insertions. No span coefficient generator or new horizontal is used.

**Theorem 2.** Gauge arrows (3) make the lift set a contractible groupoid: there is exactly one arrow between any two marked lifts.

**Proof.** Composition multiplies each edge's g; identities and inverses follow from the subgroup laws and (3). Given two lifts x,x', solve for g_v starting at deepest positive nonroot vertices:

    g_v = x'_v x_v^(-1) product_(c internal child) g_c.     (4)

All nonroot positive labels are units. This determines a unique edge tuple. The root equation follows because the total products of x and x' are the same m and the product of nonroot unit labels determines each root label by (1). This argument does NOT cancel m. Thus an arrow exists uniquely. In particular an automorphism of a marked object has every g_v=1. QED.

Although the number of marked objects can be |H|^r, their groupoid has no nontrivial automorphisms. If one first collapses all those objects to the quotient-normalized factorization but still retains all H^r gauge tuples as distinguishable endomorphisms, one instead obtains a one-object groupoid with automorphism group H^r. That is a different construction, not an equivalent repair. If both objects and arrows are collapsed, one loses the actual original lift choices altogether. The retained-mark groupoid avoids both confusions.

## 4. Contractions, expansions, rotations, and grafting

Contract an internal child vertex into its parent. Its scalar multiplies into the parent scalar; all other scalar labels remain. The graph blocks and grade arrows compose by the actual original increasing-enumeration and category-composition formulas. The total scalar stays m. On gauges delete the contracted edge's g. Formula (3) proves functoriality: the deleted child's g cancels between child and parent. If the child has zero grade, its label and gauge were both 1.

Conversely split a specified contiguous block of a vertex's inputs by inserting a new intermediate vertex, assign that vertex scalar 1, and leave the parent's scalar unchanged. This is an actual original cut expansion. On a gauge arrow set the new edge gauge equal to the product of gauges at the internal children moved under that new vertex. Formula (3) then makes the new vertex's scalar remain 1 and makes its parent's equation exactly the old one. If the inserted graph is empty, all moved child gauges are 1, so this is consistent with the mandatory zero-grade rule.

Contraction after this normalized expansion is strictly identity. Expansion after contraction is naturally isomorphic to identity by the unique gauge of Theorem 2. Repeated contraction orders agree literally by scalar multiplication and the original R law with the actual vertex embeddings. General rotations are spans of these contraction/expansion equivalences, not assertions that marking sets have the same cardinality: inserting an empty-related intermediate graph can change r.

All comparison diagrams between such functors commute up to UNIQUE natural isomorphism in the fixed-witness groupoids. The uniqueness in Theorem 2 proves every higher compatibility equation between those natural isomorphisms. This is a coherent groupoid-valued statement, not a claim that every rotation path leaves the same literal scalar marking.

Admissible grafting replaces a vertex operation by a lift of that operation's NORMALIZED QUOTIENT factorization: every inserted positive nonroot label is required to lie in H, and every inserted zero-grade nonroot label is required to be 1. The inserted root label is then forced by the replaced actual label and the product of those nonroot units. Inserted labels multiply to the replaced label; flattening consequently remains w. At a nonroot positive vertex the replaced scalar lies in H, so the forced inserted root label also lies in H; at a nonroot zero-grade vertex all these labels are 1. If the replaced vertex is the overall root, the inserted root retains the replaced scalar after the displayed unit adjustment; in zero grade this scalar is m, while every inserted nonroot label is 1. Arbitrary factorizations are not admissible here: in additive C4 with H={0,2}, the identity 0 can factor as 1+3 outside H. Under the stated normalized-quotient restriction, grafting the scalar/gauge formulas is exactly original occurrence-wise substitution. Associativity follows from original tree substitution and multiplication; nodewise comparison equations compose by DL/DR/DA. Nullary grafts keep their actual occurrence and scalar type. Graft/cut comparison natural isomorphisms are again unique within the resulting fixed-witness groupoid.

## 5. Explicit normalized-cut failure

Take M=H=C2, with nontrivial unit h, and a whole having an ordered binary cut with at least one nonempty child. Fix the outer cut scalar to 1 and the inner normalized scalar labels to 1. In the quotient, the flattened scalar-1 result and flattened scalar-h result coincide. But the SAME normalized actual factors evaluate to scalar 1, not h. Recovering the specified scalar-h target requires changing an actual factor, for example inserting D(h) on a positive child. Universal refinement lifting therefore does not imply that normalized inner-scalar-one cuts lift with their actual normalization unchanged.

The marked theory resolves this honestly: fix the actual flattened target, allow the explicitly enumerated unit markings, and retain their original D(g) comparison arrows. If the specification forbids such markings, this example is an obstruction rather than a successful lift.

## 6. Transport and scope

A functor on the original interface category K carries every full grade path and its composites to the transported path, while retaining ordered graph blocks. It consequently carries the marked cut constructions and all gauge equations directly. A monoid homomorphism M→M' taking H into H' carries marks and gauges similarly, but need not be faithful on the actual marking set.

In the concrete graph-span extensions, interface restrictions preserve graph grade and scalar labels. Hence the scalar calculations commute with whatever typed coefficient comparison is supplied by the restriction construction, even for noninvertible vertical maps. This does NOT make that coefficient comparison invertible, nor prove that an exact transported scalar-marked factorization is an exact coefficient factorization. The known noninjective nullary diagonal obstruction is untouched. The free-envelope bridge likewise does not supply missing coefficient-exact cut witnesses.

This theorem applies to fixed finite planar original cut trees of arbitrary size and depth, with actual original intermediate components. It does not infer a tree, compare arbitrary reordered crossings, establish a new complete 2-Segal structure, or claim a nontrivial scalar decoration mechanism is novel. It isolates an exact original-C5 witness-memory obligation that a bare fixed-endpoint lifting theorem would miss.
