# F2: explicit instantiation on the original discrete graph-cut model

2026-10-31. This is a reuse/instantiation of the cited proofs, not a new general theorem or an acceptance verdict. It addresses original F2 for every fixed N≥6 and the actual three-object category K=[2]. No scalar quotient, graph-orbit quotient, cluster-family restriction, or I4 construction is made.

## 1. Frozen proofs and trust/status boundary

SHA-256 of sources read:

- `/workspace/shared/contract_revision_20261028/structural_extracted/proof/Global_Cut_Repair.md` (CUT), `2329adbd1844a9a62bfefe2094526d490c302acc639116a062590dd2d31ca449`.
- `/workspace/shared/contract_revision_20261028/extracted/witnessed_decompositions/research/workstream_C1/proof/C1_Model_Theorem.md` (C1), `8a05992fe26c456ed1a5c61c5512e7939ed625da76263b58f61940e1a3a0cd7c`.
- `/workspace/shared/f1_f3_recognition_20261031/recognition_theorem.md` (REC), `fb2fb7440d73a54f49acabd296834cbdb2c4e2f5770e92ef97cffc5778b1ca7c`.

CUT §§1–5 proves the larger exact span groupoid and original discrete recovery, but expressly does not accept original obligations. C1 supplies operations, substitution and syntax comparison and expressly leaves downstream F2 open. REC's current theorem has a general R/E-family branch; here use **all** simple ordered graphs of size≤N and H_G={id} for every G, with M=1. R/E hold literally, each orbit is a singleton and every new orbit-collapse L rule is absent. The principal cluster example and its finite verifier are not used to restrict this instantiation. Historical status statements in imported files remain historical; current F2 acceptance must be a separate attributable decision.

## 2. Literal finite levels and all simplicial maps

Write G=(v,E), vertices {0,…,v−1}, 0≤v≤N, with every subset of unordered distinct pairs allowed. For n≥0, X_n consists of G, an ordered partition (U_1,…,U_n) of its vertices (empty and noncontiguous blocks allowed), and a weakly increasing sequence a_0≤…≤a_n in {0,1,2}. Equivalently the latter is the full composable arrow string in [2]. For n=0 the partition forces G empty, so X_0 has exactly three elements. Equality is literal graph, actual blocks and full interface path equality.

For α:[m]→[n] monotone, set V=union_{α(0)<r≤α(m)}U_r; let e_V be its increasing enumeration. The action sends the record to

    (G|V, (e_V^{-1}(union_{α(j−1)<r≤α(j)} U_r))_{1≤j≤m},
     (a_{α(0)},…,a_{α(m)})).

Thus inner faces merge adjacent blocks and compose actual arrows; outer faces discard the corresponding outside block and take the induced graph on the remainder; degeneracies insert an empty block and identity arrow at the repeated boundary. Constant maps and degree zero are included. For β:[l]→[m], selected vertex subsets compose via their increasing enumerations and (G|V)|W=G|e_V(W) (C1 §2/CUT §2). Unions and arrow indices therefore give X(β)X(α)=X(αβ) literally, and identity maps act identically. This proves all simplicial identities, not only those in the finite checker.

Each level has cardinality

    |X_n| = binomial(n+3,2) sum_{v=0}^N 2^{v(v−1)/2} n^v,

using 0^0=1. It is finite for each n. Repeated degeneracies of the empty graph identity path exist in all degrees, so this is not a finite-degree truncation.

## 3. All-triangulation bijection and explicit closure of the original slice

For a triangulation T of the polygon 0,…,n, form its set of compatible triangle records, matched on their literal edge components (induced graph, endpoints and actual arrow). The comparison restricts a full record to those triangles.

Construct its inverse by the same root-triangle recursion as CUT §3 and REC §§1,6. The unique triangle incident to edge (0,n), with third vertex k, retains the **entire whole G** and a bipartition (L,R). The left subtriangulation's long edge is exactly the standardized induced graph G|L with the actual arrow a_0→a_k; the right is G|R with a_k→a_n. Recursively reconstruct their unique ordered local block lists, lift them through e_L and e_R and concatenate. The root retains every cross-edge between L and R, so no edges are guessed from isolated pieces. On the category coordinate the boundary principal edges give the actual composable path; each triangle's long arrow is its composite, and category associativity forces the remaining diagonal arrows. Empty blocks cause no ambiguity: they retain their positions, and lifts of empty subsets are unique. The degree-one base is its sole whole block; degree-zero is the named interface.

Restriction of this reconstructed record gives the supplied triangles: this follows inductively by induced restriction transitivity and equality of the matching diagonals. Conversely recursion applied to triangles of an original record returns its original blocks, whole and full path. Hence the comparison is a bijection for every T and n. All rotation/pentagon/higher comparisons commute because each route is restriction and this unique inverse on the same full record.

This also proves the point not supplied by full faithfulness alone in CUT §4: **gluing stays inside the original discrete slice**. In CUT's faithful tagged graph-span realization, each principal edge is the graph span of an actual K arrow. Flat composition is canonically the graph span of the composite actual arrow. All triangle bijections are the unique endpoint-compatible ones, so root recursion and canonical interval extension have precisely original K-arrow graph spans, not arbitrary new spans. Graphs remain induced restrictions of the retained G and remain bounded by N. Thus the groupoid gluing equivalence specializes to the literal set bijection above; no inheritance claim from an arbitrary fully faithful subobject is needed.

## 4. Unitality

A principal edge is a degenerate edge exactly when its graph block is empty and its arrow is id_A (so both endpoints are the same A). For the pullback of that edge map along X_0→X_1, delete the empty block and its repeated boundary. This produces a unique n-simplex. Inserting the same empty/id block recovers the original record exactly, and deleting an inserted block is identity. This holds at both endpoints and every internal position, for every degree, proving the unital pullback bijections. An empty graph edge with nonidentity arrow is not a unit. The latter exists in [2], e.g. the empty graph graded 0→1.

## 5. Operations, grafting and actual presentation comparison

For a prescribed full composable profile p=((G_i,h_i))_{i=1}^n and output c=(G,h), the fibre of X_n at its principal edges p and long edge c is exactly C1's `FlatCut.Operation c p`: actual ordered blocks U_i with G_i=G|U_i and h=h_n…h_1. No whole or block embedding is forgotten. In arity zero it is the unique nullary cut only on (empty,id_A).

Given an outer cut U_i and an independently supplied child cut (V_{i,j}) at each original occurrence, its flattened blocks are e_{U_i}(V_{i,j}) in lexicographic (i,j) order. Its arrow string is the concatenation of the actual child strings; the whole G is unchanged. This is both the triangulation/tree inverse construction and C1 §4 substitution. C1 §5 proves its identities and associativity at full witness equality. Repeated equal components still have separate i-indices and can receive different children. Consequently the simplex-operation identification strictly respects occurrence-wise substitution, rather than merely matching frontiers.

C1 §7 gives a direct syntax link: the binary/nullary signature S_bin maps actual graph-cut generators into these operation fibres; Tree.extend is the strict evaluation homomorphism. Rotations and designated unit eliminations are parallel and sound, so Presentation.extend factors evaluation. That source explicitly claims soundness/universal factorization, not C5 completeness.

For the stronger existing presentation/refinement integration, use REC §4 and §6 on F=all graphs≤N, H_G={id}, M=1. Its general R/E-family argument applies; singleton orbits create **no additional L equations**. The original C,U,D presentation and seven templates reduce to its M=1 instance. Canonical interval cut uniqueness gives unique semantic right-comb normal forms, hence sound-and-complete evaluation for the stated original presentation. The existing O/MOut/MIn coherence completion yields the refinement comparison with full occurrence tuples. REC §7.3 gives the commuting presentation/refinement square on its specified maps. These are reused theorem conclusions on the original unquotiented family, not an inference from the narrower cluster computation or a new claim about arbitrary presentation theories.

## 6. Required nondegeneracy and evidence boundary

The exact six-vertex C1 §8 graph, four-block cut and path (0,1,1,1,2) belong to X_4 for every N≥6. Both id1 middle component occurrences agree but receive forward/reverse distinct local cuts, with final block order ({0},{1},{3},{4},{2},{5}). Adding edge05 preserves the four principal edges and changes the whole, proving ordinary Segal noninjectivity while leaving all 2-Segal bijections valid. Outer restriction can erase this cross-edge; it never erases it in the retained whole when evaluating a cut. These are the precise model phenomena, not a one-object nerve sanity check.

The all-degree P argument above reuses known graph restriction/nerve infrastructure and makes no novelty claim for F2 alone. Finite enumeration, exact [2] factorization accounting, mutation controls and independent acceptance are separate artifacts. This note supplies neither a Lean certificate nor a declaration that the larger F1–F3 scientific floor follows from taking a product.
