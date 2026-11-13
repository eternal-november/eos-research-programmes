# Located coordinates versus the A1/A3 graph-cut presentation

Status: explicit P-level comparison accompanying the independently checked representative. A1–A3 have now been accepted by root; A3_LOCAL_COMPARISON.md supplies the exact linkage to their actual public signature, generated congruence and quotient APIs, independently reviewed as LOCAL_VERIFIED on 2026-10-24. No public Lean adapter is claimed or required for this P comparison. Full A4 acceptance remains OPEN for the external scientific bundle/use gates.

## 1. Precisely compared classes

Fix an ambient ordered simple graph G on Fin 6, root support S, and root interfaces a <= b in the three-object chain. The canonical whole is the ordered induced graph G|S with arrow a -> b. Let Raw(G,S;a,b) be the fibre of seed-style planar trees on THEOREM.md's graph-cut signature, with this whole, allowing any ordered frontier, and decoration monoid Z/3. Every internal edge has its canonical ordered graph and arrow colour; each binary vertex retains its full graph bipartition and arrow factorization.

Let Located(G,S;a,b) be the valid terms of RewriteFragmentCandidate.lean. The term has endpoint indices and an arbitrary planar shape. Its leaf payload is an ambient vertex subset, not its component colour. Validity says the ordered leaf subsets partition S. At any subtree t, write V(t) for the union of its descendant leaf subsets; a nullary has V(t)=empty. The component colour of that edge is the standardized ordered graph G|V(t), with the subtree's endpoint arrow. The location V(t) is retained inclusion data. In particular disjoint subsets can be equal component colours, as proved by `GraphCoordinates.repeated_component`.

## 2. Raw to located

Traverse a raw tree together with an increasing embedding e of its outgoing graph's canonical vertex set into Fin 6. At the root e is i_S.

- An identity leaf becomes the located leaf with block image(e) and its same arrow.
- A designated nullary unit becomes `Term.unit`; its graph is empty, so its image is empty, and its interfaces coincide.
- A decorator keeps its value and recursively converts its child with the same e.
- A binary cut labelled by the canonical ordered bipartition (U,V) recursively converts the left child with e composed with i_U and the right child with e composed with i_V, and uses `Term.cut` with the same intermediate interface.

The restriction equality from THEOREM.md section 1 gives exactly the colours needed at each recursive call. Every vertex is sent to one leaf occurrence; disjointness and coverage follow by induction over the cut tree, including empty and nullary cases. Thus the output is a member of Located(G,S;a,b). Different occurrences with the same standardized component still receive different root-coordinate subsets whenever their supports differ; repeated empty occurrences are distinguished by their ordered positions, not by payload equality.

## 3. Located to raw

At each located subtree t use output graph G|V(t) and its endpoint arrow. The valid-cut decomposition theorem supplies disjoint supports V(x),V(y) and V(x) union V(y)=V(t) for every binary node.

- A leaf becomes the identity tree on G|V(t), retaining the arrow.
- A nullary unit becomes the designated nullary generator, never an identity leaf.
- A decorator becomes the corresponding unary graph-colour generator.
- A cut becomes the binary generator with whole G|V(t), partition `(rank_(V(t))(V(x)), rank_(V(t))(V(y)))`, and the two child arrows. Recursively converted children have exactly the input colours, because increasing enumeration commutes with restriction.

No cut label is inferred from only the two isolated input graphs. The retained ambient G supplies all cross-child edges of the parent graph. The two child supports supply the actual partition and its inclusions. This is why the construction distinguishes different retained whole graphs with identical restricted pieces.

## 4. Inverse laws and equations

For a raw tree, converting out and back recovers each binary partition since i_(image e) is its increasing enumeration and rank is its inverse. Restriction composition recovers the same canonical child graphs; the typed term retains each intermediate interface and decoration. An induction on the raw tree proves the round trip is identical to the original tree (up to the implementation's equality transports for canonical relabeling).

For a located tree, converting out and back recovers each leaf subset by `recover_rankBlock`, because validity proves it is a subset of the current root support. Binary shape, intermediate interfaces, unit vertices and decoration values are unchanged. Induction on the located tree therefore proves this round trip is the original located tree. The equality is not merely equal flat semantics.

Under these maps each of the seven equation schemas corresponds to the identically named schema. For rotations, support unions associate, rank/inclusion composition identifies the three induced child colours, and the chain's arrow composites associate. Unit and decoration equations preserve the same support sets and typed frontiers. Thus the maps descend to inverse maps on the locally generated quotients. The checked `equiv_iff_standard_cut_eq` theorem then concerns exactly the complete standardized graph-cut witness, not an over-refined notion where locations have secretly become colours.

## 5. Occurrence substitutions

A valid raw graft forest at the original ordered leaf positions converts each replacement subtree using that leaf's existing embedding into G. Its converted leaves partition the original leaf support. Conversely a located replacement whose leaves partition that support converts to a raw replacement with the same output graph/arrow. Each original occurrence is treated independently, even when its colour or support equals another occurrence's.

The checked `frontierDispatch_at` theorem recovers each supplied replacement at its specified finite frontier index; this alone was insufficient to justify recursive dispatch. The repaired `Term.allLeaves_iff_entries` theorem proves that recursive leaf traversal at every arbitrary offset matches the actual `Spine.entries` indices. Using that exact correspondence, `frontierDispatch_valid` derives `ValidSubstitution` from the separately supplied graph validity of every finite forest entry, and `valid_frontierForest_graft` proves end-to-end validity of the independently chosen graft. Thus the complete chain, not recovery-at-index alone, covers every finite typed forest including different replacements at repeated/empty component occurrences. The coordinate comparison commutes with grafting by induction: the raw route composes inclusions e i_U i_V, while the located route uses the same nested root-coordinate subsets. Ordered traversal uses the same concatenation of frontier occurrence lists.

This is the representative syntax/equation/substitution comparison. The exact comparison with `Presentation.Derives S E_G` and `Presentation.quotient E_G` is supplied in A3_LOCAL_COMPARISON.md. Neither document establishes the B3 categorical quotient of raw refinement arrows, cartesian restrictions, interface descent, or 2-Segal lifting. The optional public Lean adapter is not supplied; these P proofs must be reviewed on their own merits rather than called kernel-checked.
