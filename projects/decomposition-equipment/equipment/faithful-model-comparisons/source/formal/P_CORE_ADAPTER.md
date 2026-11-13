# Exact P adapter for the checked E3 core instance

## Scope and evidence levels

`E3GraphGroupoidCore.lean` and `E3FiniteExamples.lean` are a checked typed
core-facing instance, NOT a mechanization of the complete E3 equipment or of
the graph–span comparison. The complete uniform P arguments are in
`../theorem.md`, especially §§2–7. This adapter spells out the mathematical
identification needed to use the L fragment; statements below are P unless
an exact Lean name is given. There is no identity-map “faithfulness evidence.”
The actual new core morphism `eraseScalar` is deliberately NONfaithful and its
loss is exhibited by `scalar_erasure_nonfaithful`.

## 1. The actual finite parameter instance

The three interfaces are a new wrapper around `Fin 3`. For every ordered pair
of interfaces the vertical hom-set is `Grade = Equiv.Perm (Fin 3)`; composition
is permutation multiplication with the right factor applied first, identity
is 1 and inverse is permutation inverse. Thus K has three objects, six arrows
in each hom-set, and 54 arrows in total. It is not the old three-object chain.
`nonidentity_automorphism` and `noncommuting_changes` check genuine automorphisms
and noncommutative composition. The scalar monoid is
`Multiplicative (ZMod 2)`: Lean writes its operation additively, so Lean scalar
0 denotes multiplicative identity 1 in the P notation, and Lean scalar 1
denotes the other group element. Both scalars are units. No nonunit-scalar
obstruction is claimed for this L instance; the finite C suite and P family
include monoids with nonunits separately.

Graph colours are the unchanged original `GraphCut.GraphColour`. Their DATA
are the vertex count r≤6 and the full row-major adjacency matrix. The
existential ambient realization in `GraphCoordinates.Graph` on `Fin 6` is
proof-irrelevant, not an ambient-location colour. Every ordered simple graph
on r≤6 vertices occurs: realize it on the initial segment of `Fin 6` and fill
all remaining adjacency entries with false. Conversely every certified code
is exactly such a graph. The increasing enumeration identifies matrix
coordinates with [r], so this is a bijection of actual ordered graph values,
not of isomorphism classes. This is the same P coordinate identification as
the inherited C1 `Adapter_Comparison.md` §§1–2.

`Horizontal a b` is exactly (graph, actual S3 grade), retaining both endpoints
in the surrounding actual `Quiver.Path`. The entire path, including all
intermediate interfaces, ordered repetitions and grades, is kept; it is
never replaced by the list `pathGraphs` used in the graph-validity predicate.
`pathGrade` multiplies grades in path order h_n…h_1 and sends nil to 1.

## 2. Full cell and restriction comparison

For each fixed path p, target (G,h) and boundaries f,g, `Cell p H f g` stores:

* `cut.blocks`, the ordered lists of canonical whole-graph vertices;
* an actual scalar in `ZMod 2`;
* proof of the graph-partition condition and square g·grade(p)=h·f.

The graph-partition condition says that some ambient G0/support s and ordered
partition bs realize the target whole, every input graph, and the local block
lists `bs.map (localBlock s)`. Because increasing enumeration of s is a
bijection, this is equivalent to the P condition that the stored blocks form
an ordered disjoint exhaustive partition of [r] and induce the input graph
at each occurrence. One direction transports bs through that bijection; the
other realizes G on an initial segment and transports the proposed blocks
back. Graph restriction respects those increasing bijections. Hence this is
an exact full-cell fibre correspondence, not a sufficient-only validation
or an extra ambient witness. Proof irrelevance and `Cell.ext` show that equality
compares the full ordered partition and scalar in the fixed full profile.

`restrictionEquiv` is checked for EVERY typed path, including nil, and every
boundary pair and preceding changes u,v. Its equivalence sends (U,m) to the
same (U,m), using

    (g v) grade(p) = h (f u)  iff  v grade(p) = (g⁻¹ h f) u.

The selected horizontal `restrict` keeps the graph and sets its grade to
`g⁻¹ h f`. Both inverse laws, factorization, uniqueness, payload retention,
identity restriction and two-change horizontal coherence are checked.
`restrictionCompose` is the inverse of this equivalence. It is not separately
implemented as general multicell substitution in Lean. Its identification
with actual composition through κ is P: κ has the singleton full block and
scalar identity, so the increasing inclusion is identity and its scalar is
neutral. Therefore actual substitution keeps U,m and changes exactly the
boundary square, which is the implemented inverse. This proves the exact
comparison with Theorem 3.1, without claiming a second formal substitution
implementation or formal all-context naturality theorem.

## 3. Original Signature/Tree instance and semantic evaluation

The signature has all valid binary graph partitions with actual a,b,c and
S3 grades, and a scalar in `ZMod 2`, together with nullary empty-graph identity-
grade primitives carrying either scalar. The binary proof predicate eliminates
invalid partition/input combinations. Its data carry no old chain endpoints.
`primitiveCell` checks EVERY primitive as an actual semantic `Cell`, with its
full partition and scalar. A nonzero nullary primitive here is allowed and is
not the chosen unit merely because it has arity zero.

`coreCalc = Tree.freeCalc signature` is the unmodified original accepted
A-calculus construction. `evaluate` keeps the whole indexed by the output,
the actual A frontier, recursively lifted canonical blocks, and the sum of
primitive scalar values reduced in `ZMod 2`. `scalar_substitution` is the
accepted original `Tree.weight_profileGraft`, followed by the canonical
Nat→ZMod2 additive map. Thus the displayed cast of the Nat occurrence sum is
exactly the sum of all the retained finite scalars, including repeated slots.
The actual original identity, graft and association laws are checked.

Here is the P proof that evaluation lands in the semantic graph core and is a
strict core morphism, not merely an assignment of unvalidated records. Induct
on the original Tree constructors. A leaf contributes its whole vertex range,
its one horizontal occurrence, and scalar 0. A nullary contributes the empty
graph, empty partition/path and its declared scalar. For a binary generator,
its valid partition gives increasing inclusions i_U,i_V. The two induction
hypotheses give partitions in the child coordinates, correct induced graphs,
composable full child paths and their output grades. Applying i_U/i_V and
concatenating yields a disjoint exhaustive partition of the parent; induced
restriction is transitive, so every actual frontier graph is correct. The
child output grades multiply to the binary output grade. The additive scalar
is exactly the parent scalar plus both child totals. This also proves that
every indexed list lookup in `generatorBlock`/`liftBlock` is in range; fallback
values are unreachable on valid trees.

For substitution into an arbitrary occurrence, its inclusion into the root
is the composite of the increasing inclusions along its ancestor chain.
Substitution first inside the child and then at the root, or in a single
expanded occurrence family, gives the same composite function on every
vertex and the same ordered concatenation. Scalar equality is associativity
of addition; typed profile equality is the original frontier-graft theorem.
Therefore evaluation preserves identities and substitution into the semantic
Calc of Theorem §6. It need not reflect syntax equality: two differently
bracketed trees can have the same complete cut. That is expected presentation
semantics, not claimed faithful semantics on free trees.

The generic landing/substitution proof in the preceding two paragraphs is P,
not a Lean theorem about `evaluate`. The substantial concrete bridge IS
checked: `actual_core_semantic_bridge` equates the actual N=6 tree evaluation's
whole, complete typed profile, blocks and scalar with the certified
`principalCell 0`. `parallel_semantic_witnesses` retains distinct scalar
witnesses; `nonglobular_factorization` and `nonglobular_full_payload` check a
nonidentity-interface lift with the full nonempty N=6 partition and scalar.

## 4. C1 profile embedding and actual scalar-forgetting morphism

Map the old C1 chain objects 0,1,2 to the three new objects. Set potentials
s_0=1, s_1=τ=(01), s_2=σ τ with σ=(12), and send its unique i≤j arrow to
s_j s_i⁻¹. Composition telescopes, identities are 1; each hom-map is injective
because the source hom is empty or singleton. It is NOT full vertically and
does NOT reflect invertibility. It sends 0→1 to τ, 1→2 to σ and 0→2 to στ.
Whole graph values and all local block coordinates are unchanged, scalars
are identity. Therefore on each ORIGINAL full operation profile the semantic
cut map is injective and surjective onto the declared image fibre; it preserves
and reflects equality of ordered cut witnesses and occurrence-indexed
refinement tuples. It does not assert equality of chain and groupoid vertical
categories or claim restrictions in the old chain.

The new N=6 fixture uses precisely this grade assignment. Its two nonempty
middle graph components coincide, but the opposite local binary partitions
[[0],[1]] and [[1],[0]] remain distinct and are assigned independently to the
two actual occurrences. Their graft has blocks [[0],[1],[3],[4],[2],[5]]. The
old whole altered by the 0–5 cross-edge remains different with the same
component graphs. No endpoint-only or graph-only profile is substituted in
any claimed comparison.

`eraseScalar` is a real `Calc.Hom` built with original `Tree.extend` and a typed
assignment replacing each primitive scalar by 0 without changing its full
binary cut or nullary type. The hom laws and complete profile preservation
are checked by the original extension API, and it induces the actual B2
`SemanticRefinement.functor`. Induction shows it preserves every generator's
whole and block lift, hence every evaluated partition. It sends every evaluated
scalar to 0. `scalar_pair_distinct` and `scalar_erasure_nonfaithful` explicitly
show that this Calc.Hom is not injective on operation fibres. No conclusion
about faithfulness on the local hom-sets of its induced refinement functor is
asserted from that operation collapse. At the semantic level the scalar-erasing
map has equality kernel given by equality of full profiles and partitions,
with scalar forgotten. Since every scalar in this finite group is a unit,
Theorem 7.1 says this particular erasure preserves AND reflects the intrinsic
opcartesian marking Ex_op. It does NOT reflect the normalized Ex_op^1 or
Ex_coeff marking: additive scalar 1 maps to additive 0 (multiplicative identity),
so normalization can be created. These statements use the P classification,
not a new Lean marking theorem.

## 5. Exact role of the reused noninvertible relational core

`E1RelationEquipment.lean` and `E1FiniteExamples.lean` are byte-identical to the
accepted E1 files and freshly compiled with the unchanged original API. They
use arbitrary functions on interface carriers, actual natural-number scalar
cell witnesses, inverse-image restrictions, all-context unit substitution,
and actual `coreCalc`, `coreFiberEquiv`, `forgetScalar`, `exactLift` and B2
refinement morphisms. Their finite three-interface Bool example includes a
constant noninjective map; `genuinely_noninvertible_interface` checks that fact
again. This is not a groupoid transport model and is not asserted to equal the
primary finite-scalar graph model or the full graph–span model.

The exact comparison from the second E3 graph–span model S(N,M) is as follows.
Keep every finite interface carrier and every function. Send a graph-labelled
span to its support relation R(x,y) iff an apex point has left leg x and right
leg y. Send a cell (U,m,φ) to the E1 relation cell of weight 0. If a source path
has an apex tuple witnessing its support relation, φ sends it to a target
apex with endpoints f(x),g(y), proving precisely the E1 `valid` predicate.
This retains the full typed profile OF THE IMAGES; it does not pretend to
retain original graph/span profiles injectively. Identity and substitution
preserve validity by composition of apex maps and send all scalars to 0;
0+sum(0)=0. Pullback-span support is exactly inverse image of the target
support relation, and the identity-span support is equality, so restrictions
and units are preserved (using the explicit span pullback comparison).
This support morphism forgets whole graphs, partitions, original scalars and
apex multiplicity/map data, is not faithful, and need not reflect exactness or
nonrepresentability. Those losses are declared, not used as an E3 substitute.
The separate graph–span FULL-cell comparison in theorem §5.2 retains the
witness data and is proved P, with independent C tests. The E1 source is
supplementary checked noninvertible-interface/core evidence linked by the
specific support map above, not a claim that checking Rel alone passes E3.
