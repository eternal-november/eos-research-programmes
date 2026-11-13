# Structural partition-erasure theorem (supplement to scalar candidate)

Author proof candidate; not acceptance. Uses the original C5 calculus, without adding vertex colours or enlarging equipment carriers.

## 1. Selected unbounded class

Let H be any nonempty induced-closed collection of finite ordered simple graphs, with each degree bounded by N in a finite instance. Work in the original C5 calculus at M=1, restricted to components whose graphs belong to H, and any nonempty finite interface category K. Binary generators, units and rotations remain well typed because H is induced closed. Require the empty graph and singleton graph in principal instances. Varying N gives unbounded graph sizes and all profiles/tree depths remain unbounded.

Define a parallel congruence P by identifying all operations with the SAME whole and SAME full ordered input profile. Thus only the actual ordered vertex partition is forgotten; input graph types, arrow string, endpoints and retained whole are unchanged. This is a substitution congruence: substitution of parallel operations and parallel child tuples produces parallel composites. The quotient is the existence calculus: it has one operation on a profile precisely when that profile can be realized as an induced ordered partition of the retained whole. It does not infer the whole from the pieces.

## 2. Sharp recognition theorem

**Theorem.** Every full proper contiguous-interval factorization map of this quotient is bijective if and only if every graph in H is complete or edgeless.

**Necessity.** Suppose G contains an edge {a,b} and a nonedge {c,d}. Then |G|=r≥3. At an object A of K use a profile of r identical singleton components with identity grades. Every ordering of singleton blocks is a valid operation before quotient, and all have the same profile and whole, so P identifies them. Select the first two input positions as the proper interval. One representative places {a},{b} there; another places {c},{d} there. Their inherited original factorizations yield quotient factorizations of the same quotient operation, but through intermediate components (edge,id_A) and (two-vertex-edgeless,id_A). These components are distinct and retained by P, so the factors are distinct members of the actual disjoint union over K in F1. Thus injectivity fails. No failure of cross-edge recovery or undefined nerve is substituted for the failed comparison: this is the literal, defined factorization map. QED.

**Sufficiency.** Let G be complete or edgeless. At any interval let s be the sum of the input vertex counts. Every s-subset of G induces the same standard ordered graph H_s: complete when G is complete, edgeless when G is edgeless; at s=0,1 these coincide. The intermediate grade is the composite interval grade, so its whole component is forced. The outer and inner profile are consequently forced, and each quotient operation fibre is at most a singleton. Existence follows by cutting any representing partition. Thus exactly one factor pair exists. QED.

Empty blocks, repeated equal singleton inputs and all boundary interfaces are retained. Unary operations in the quotient are only identities, since a one-block partition forces input=whole and M=1. Nullaries exist only on empty/id and are unique. Genuine unit insertion at a named boundary inserts empty/id. Therefore the same restriction/size formulas give every unit and all coherent iterations without modifying F1's original candidate.

This is a structural classification of a quotient on a broad declared family, not the old scalar multiplication-fibre calculation. Full placement erasure is allowed on homogeneous families and obstructed as soon as a graph has both an edge and a nonedge. An orbit quotient retaining more information can avoid this obstruction; that is the distinct richer cluster/occupancy route.

## 3. Original local equations present the positive quotient

In the homogeneous case, each binary cut with block sizes a,b has the same input/output components as the cut whose left block is the first a vertices and whose right block is the last b vertices. Add the finite local equation schema

    L: c_(U,V)(x,y) → c_([a],{a+1,...,a+b})(x,y)

for noncanonical tags, retaining all arrow labels. This is an actual equation between parallel original C5 operations. All cuts with a=0 or b=0 already have the unique canonical partition. Do not change, delete, or permute external occurrences.

Together with original R,UL,UR (and D0,DA,DL,DR if using the M=1 presentation with explicit d_1), L presents exactly P. Soundness is immediate. For completeness, normalize any raw tree by original rotations/units and then canonicalize every binary cut. Its normal form is the canonical right comb with the same ordered input components and grades, retained whole, and contiguous blocks of their sizes. In homogeneous graphs all these tags are well typed. Every two parallel represented operations have this same normal form. Conversely no equation changes whole or profile. Thus the least declared congruence is exactly P, not an assumed quotient by all semantic equalities.

For a formal terminating system use the existing original shape/decoration termination tuple, followed by the number of noncanonical binary tags. Original steps strictly decrease the old tuple; L changes no tree shape or decoration placement and strictly decreases the final count. Original reduced right combs with all canonical labels are exactly the described irreducibles. This proves termination and confluence by the unique normal-form description. It is essential that canonicalization preserves typing; arbitrary nonhomogeneous graph families fail that hypothesis.

## 4. Independent B3 completion and actual arrows

At each fixed finite N,K the original rule set plus L is finite and all rules are frontier-linear and frontier-preserving. Its nonvariable critical overlaps are effectively enumerated by matching the finite left-hand sides at their finitely many nonvariable positions, with finite type/label assignments. To specify ordinary coherence independently, choose each critical pair's two deterministic reduction paths to its common canonical normal form. This is an effective syntactic finite table, not a relation saying all semantically equal paths agree. Include context/substitution instances and disjoint/variable squares.

Define Comp_P from raw elementary grafts and invertible equation edges with raw forest/interchange laws; the just-described O_P critical paths; and MOut/MIn for each of the old rules and L. The original Completion_Comparison proof §§3–5 now applies with the following checked hypotheses: termination, a join for every typed nonvariable peak, disjoint/variable transport, and occurrence-linearity. Its well-founded first-edge induction proves all pure normalization paths equal; MOut pushes original equations past subsequent grafts; MIn normalizes the individual inserted forest entries. Every arrow is therefore uniquely its full tuple of normalized original-slot entries followed by the target normalizing path. This yields

    Comp_P ≃ Ref(C5/P).

Forward evaluates each original forest entry to its quotient operation. Reverse chooses the canonical right comb per object/entry, grafts at each distinct original slot, and normalizes. Their inverse/coherence laws are the same explicit tuple/path-normal-form argument, not assumed fullness or faithfulness.

Thus the quotient identifies placements INSIDE a child operation, but arrows still remember every original slot, the complete child profile and its length (including zero), and every grade and component. Two refinement tuples are equal iff these data agree entrywise. Equality of eventual target does not collapse different slot segmentations.

## 5. Discrete comparison and information loss

The positive quotient's n-simplex is a retained homogeneous whole G, a composable grade path of length n, and an ordered size vector (s_1,...,s_n) summing to |G|. Its principal input graphs are the uniquely induced homogeneous graphs of those sizes. For any monotone α, retain the graph of size the sum over the selected range, group the sizes over each run, and compose the arrows. Empty runs insert size 0/id. Because the induced graph is determined by size, all operators descend from the original graph-cut object. The graph-kind restriction maps are consistent at sizes 0 and 1, where complete and edgeless coincide. Induced restriction and addition prove the simplicial identities.

Triangulation reconstruction adds the indicated sizes recursively and retains the whole graph at the root; the intermediate graph is forced by its size. This is the explicit unique factorization above in every tree, so every comparison is bijective, with genuine units. Operation↔simplex maps read the same size vector, whole and full grade path. Grafting substitutes size vectors at distinct occurrences; inverse comparison is the canonical contiguous partition. Two original whole graphs on two vertices (edge versus noedge) have the same singleton input components, so composition remains genuinely multivalued. The positive object is not an ordinary single-valued category nerve.

On maps, require actual calculus/simplicial maps to retain whole graph and sizes and to have a graph-independent grade map. The empty-graph unit and binary triangles force this grade map to preserve identities and composition, so it is precisely a functor of interface categories. Every principal edge then forces the full arrow string, proving the forward/reverse hom bijection exactly as in the scalar candidate, not by defining all maps to be parameter maps. Finite bound inclusions and induced-closed homogeneous subfamily inclusions are allowed. No reconstruction of forgotten actual partitions is claimed.

## 6. Limits and evidence status

This supplements rather than replaces the original scalar boundary. On arbitrary H the quotient is legitimate, but the F1 map fails exactly at nonhomogeneous graphs; no claim of a well-defined simplicial outer-face quotient is needed to prove that failure. The positive family gives actual all-degree simplicial maps and an independent local C5/B3 completion. The exact critical-pair table is effectively specified, as B3 allows, but a concrete generated table and finite independent checks would strengthen reproducibility. Original scientific acceptance and broader F1/F3 negative-control/literature requirements remain reviewer decisions. The richer block-symmetry/occupancy quotient may give a wider positive class without full placement erasure.
