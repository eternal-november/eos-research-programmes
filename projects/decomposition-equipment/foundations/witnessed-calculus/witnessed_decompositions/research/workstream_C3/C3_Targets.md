# C3 exact target freeze — pre-attempt review candidate

Prepared 2026-10-25. TARGET PREPARATION ONLY. No proof attempt starts before
parent and non-author hash-bound release. Contract v0.1 unchanged,
`research/CompletionContract.md`, SHA256
`47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
C3 ONLY is authorized. A4/C5/B3/B4/D/E/F/G/I are not activated.

## Complete binding C3 acceptance clause

**Class and claim:** M. Prove which distinctions the models separate and which
reconstruction claims they refute.

**Inputs:** C1–C2 and the semantic comparison definitions.

**Artifact:** A separation matrix with proof or explicit counterexample for:
same frontier versus same tree; same tree shape versus same primitive labels;
same leaf types versus same whole; same whole versus same witness; same
evaluated witness versus same presentation; and same observation versus same
semantic object.

**Discharge:** P and X. Each entry must name the domain and map in question.
The nonreconstruction result must quantify over a meaningful family, not merely
state that one graph edge was deleted. For graph cuts, characterize the fibre
of the map that retains only the induced block graphs: cross-block edges give
freely varying missing data in the unrestricted simple-graph family.

**Tests:** Exhaustive checks on all ordered simple graphs up to four vertices
and their relevant ordered partitions, plus independently verified six-vertex
repeated-component examples and cross-block families of arbitrary size in the
proof. Check that any claimed injectivity disappears in the intended negative
control.

**Dependencies:** B2, C1, C2. **Minimum passing floor:** Determine the full
missing-cross-edge fibre and distinguish whole, witness, and presentation maps.
A two-vertex counterexample alone or a matrix of unsupported yes/no claims does
not pass. Branch: M positive only; negative examples are required conclusions
of the positive separation theorem, not an alternative obstruction discharge.

Section 3.4 requires complete proofs, actual map domains, a non-author cheapest
solution check, independent verification and separate correctness/scope verdicts.
Section 13 permits P/X with executable support for these model/observation
limits; optional Lean does not replace them or enlarge scientific credit.

## Frozen inputs and hypotheses

Use C1's literal ordered simple graphs G=(m,E), vertices [m], canonical increasing
enumerations epsilon_B, arbitrary finite category K with actual arrows, and
components (G,a). All finite graph sizes and all finite arities are included in
the P theorem. Partitions are ordered, disjoint, exhaustive tuples of possibly
empty blocks; block order need not follow ambient vertex order. No graph
isomorphism quotient, permutation rule, exchange or implicit reconstruction.
The N-bounded C1 instances are closed under substitution but NOT finite over
all arities. Nullaries require empty graph and identity loop grade as in C1.

Use C2's arbitrary finite carrier family X_i, literal relations R subset X_i x
X_j, independent whole W, containment cell C(p) subset W and separate exact
cell C(p)=W. Fixed-(p,W) semantic cell fibres are empty/singleton. A primitive
symbol, semantic cell and existential realizing tuple are distinct notions.

Use accepted B2's actual semantic refinement object/tuple maps induced by a
strict calculus interpretation. Object equality reflection is not inferred
from raw hom-faithfulness; tuple entries retain their profiles and occurrences.
No new quotient completion or refinement classification is attempted.

A1–A3 and B1–B2 are accepted inputs. C1/C2 local verified constructions are
usable inputs; full C1 remains OPEN for C5/F2 and full C2 for D2/E. A4 remains
locally verified/OPEN. All 578 baseline files are preserved byte-for-byte.

## Exact domains and maps

Let Cut_K be the disjoint union of C1 total witnesses w=(G,a,p,B), with all
finite graph sizes, arities and typed arrow strings; p lists (G|B_i,a_i), and
a is the composite of the a_i. Let Whole(w)=(G,a), Leaves(w)=p and Blocks(w)=B.
These are different actual maps. Let Cut_K(p) be the exact Leaves fibre.

Let S_bin be the C1 binary-cut and designated-nullary signature, and T_K the
disjoint union over whole components of its accepted finite raw typed trees.
Ev_G:T_K->Cut_K is the A2 strict extension of the primitive assignment.
Front:T_K->typed ordered paths is the full frontier; Out:T_K->components is
the root component; Shape:T_K->finite planar rooted arity trees forgets all
component and primitive labels but retains every leaf and nullary node.
Lab(T) is the finite partial function from internal planar addresses to actual
primitive generators. Enc(T)=(Out(T),Shape(T),Lab(T)). Identity trees have no
internal label, so Out cannot be silently dropped from this encoding.

For C2 choose an explicit signature S_rel assigning two distinct parallel
binary symbols to the SAME admissible containment cell, plus the typed
components needed for a genuine three-interface unequal-cardinality example.
Ev_R:F(S_rel)->M_le is its A2 strict extension. Symbol identity is retained in
the source, not stipulated equal by semantics. The proof will also state the
general fact that arbitrary parallel trees evaluate equally in fixed (p,W)
fibres of M_le, while distinct fixed-profile whole relations remain different.

For the observation row only, fix interfaces i,j and define the LOCAL map
Obs_ij:P(X_i x X_j)->P(X_i) x P(X_j), R |-> (dom R, ran R). Its semantic domain
is the C2 component fibre Rel_X(i,j), NOT syntax, cells, latent realizing
tuples, or an unspecified observation theory. Define Truth_ij(R) to be the
complete Boolean relation matrix. This is a local comparison of two expressly
chosen observables; no G/I minimization, context theorem, general empirical
identifiability or transport claim is made.

## Quantified target statements (P/X)

**T1 Anchored full fibre.** For every m,k, ordered partition B of [m], and
tuple H_i of ordered simple graphs on [|B_i|], define rho_B(G)=(G|B_i)_i on
ALL graphs on [m]. Let X_B be the unordered vertex pairs whose endpoints lie
in different blocks. Give an explicit bijection rho_B^{-1}(H) <-> P(X_B),
with BOTH inverse laws and all validity checks. Therefore its cardinality is
2^{|X_B|}, where |X_B|=sum_{i<j}|B_i||B_j|. Include k=0, m=0, empty blocks
and the injectivity boundary X_B=empty, equivalently at most one nonempty block.
When two blocks are nonempty, no function of the ordered induced block graphs
can reconstruct every graph in this full anchored family.

**T2 Unanchored full leaf-only fibre and exact repair.** For every fixed typed
path p=((H_i,a_i)) with n_i=|H_i| and m=sum_i n_i, describe the ENTIRE fibre
Cut_K(p) as the disjoint union over all ordered partitions B of [m] with
|B_i|=n_i of P(X_B). The whole grade is forced by p; graph edges and ambient
block embeddings are not. Prove the cardinality
(m! / product_i n_i!) * 2^{sum_{i<j} n_i*n_j}, including empty cases. This counts
total witnesses, NOT distinct wholes after quotienting away B. Prove that the
record (p,B,E_G intersect X_B) reconstructs w uniquely and explicitly. Dropping
cross-edge data or dropping B loses injectivity in named nondegenerate examples.
No minimal-recovery theorem for arbitrary models or probes is claimed.

**T3 Six-row separation matrix.** For every map the table names source,
codomain, positive implication/repair and an actual counterexample to the
relevant converse. Prove Enc injective on all finite typed trees by structural
reconstruction. Use C1's mixed four-leaf, six-vertex T_bal/T_right for
Front noninjectivity and Ev_G noninjectivity. Same-shape/different-label
corollas use the two opposite ordered singleton cuts of the same edge graph,
having equal whole and profile; show primitive-label data are genuinely lost.
Leaves fails to determine Whole by T1/T2, and Whole fails to determine a cut
witness even at fixed full profile via those two opposite cuts. Keep all three
Whole, cut-witness and raw-presentation equalities separate. Also show C2
parallel primitive collapse under Ev_R and fixed-(p,W) thinness, without
quotienting the syntax or asserting all total cells with one whole are equal.

**T4 Local observation separation.** For all finite X,Y, Truth is injective;
Obs determines only endpoint supports. Characterize existence and the simple
injectivity boundary of the fixed-support fibre: it is empty unless supports
D,R are both empty or both nonempty; for nonempty D,R its elements are exactly
subsets of D x R with no empty row or column. It is singleton if min(|D|,|R|)=1,
and non-singleton if both sizes are at least 2. Empty supports force empty
relation. Exhibit an explicit unequal-cardinality 2-by-3 certificate with equal
Obs and distinct full relations; deletion of relation bits from Truth into Obs
must destroy injectivity. No claim that Obs is a calculus morphism.

**T5 B2 linkage.** Instantiate the existing strict interpretation comparison on
Ev_G and Ev_R, identify its object map and occurrence-tuple arrow map, and
explain the exact equality-loss implications of T3. Include the six-vertex
different middle-occurrence substitutions with their actual distinct entries.
Do not infer object injectivity from raw-source hom-faithfulness, classify
refinement fibres, or activate B3/B4/C5.

## Frozen finite domains, independent checks and negative controls

Graph suite: every ordered simple graph on m=0,1,2,3,4 and EVERY assignment
[m]->[k] for each k=0,1,2,3,4,5. Missing labels retain empty blocks; k=0 admits
the unique empty assignment only when m=0. Thus all partitions without empty
blocks are included, and empty-slot cases are exhaustive to declared arity 5.
There are infinitely many higher-arity empty paddings; NO finite claim covers
them. The all-arity P proof covers them. For each (m,k,B), group graphs by exact
ordered induced graphs, compare the full enumerated fibre to independently
generated cross-edge subsets, and check the size and inverse maps. Group all
(G,B) by Leaves to verify the unanchored fibre and formula as well.

Interfaces: K=[2] with all weakly increasing object strings of length k+1,
every actual composable arrow string. Graph/arrow checking may factor only
after documenting the product argument; physically executed and represented
product counts must be separated. Do not omit intermediate interfaces.

Six-vertex suite: G edges {01,12,13,24,34,45}, blocks ({0},{1,3},{2,4},{5}),
object path 0,1,1,1,2, forward/reverse middle cuts; independent recursive tree
evaluation for both groupings, actual refined final blocks
({0},{1},{3},{4},{2},{5}). Exhaust all 2^13 cross-edge choices for these fixed
blocks and fixed internal edges, not just the one-edge toggle. The theorem
covers arbitrary sizes. A non-author implementation independently checks this.

Relation observation suite: all relations on [a] x [b], a=0..2 and b=0..3,
grouped by actual (dom,ran), verifying the fixed-support description/boundary,
Truth injectivity and the declared 2-by-3 collision. Named S_rel certificate
uses three distinct labels with unequal carrier sizes and nonempty composition.

Mutation-sensitive controls execute actual wrong maps/predicates: omit a cross
edge in reconstruction; drop B from repaired record; use unordered instead of
ordered blocks; deduplicate equal component occurrences; erase primitive labels;
claim Ev injective; collapse Truth to Obs. Each must fail against an explicit
valid witness or independent recomputation, not a constant expected-failure flag.
Independent review must inspect arguments and run separately implemented finite
checks, followed by a fresh additive-source reproduction and baseline hash check.

## Nonpassing shortcuts and reporting boundary

No tiny example in place of the all-size fibre; no fixed-B formula falsely
advertised as the total Leaves fibre; no unsupported yes/no matrix; no graph
isomorphism quotient or hidden block embedding; no arity infinity concealed by
finite enumeration; no empty middle blocks as principal repeated-component
certificate; no C2 realization tuple confused with its thin semantic cell;
no raw hom-faithfulness misreported as object recovery; no build-only acceptance;
no new novelty, C4 literature comparison, or later-workstream achievement claim.

Deliver full P proofs, X matrix, author and independent C sources/results,
hash-bound reviews, baseline-preservation record, fresh reproduction evidence,
plain TXT report and additive source checkpoint. Parent owns acceptance and
delivery. Agent-managed review/correlated-model limits are disclosed; external
human certification is not claimed. Standard coordinate decomposition and
finite-relation support facts are credited as elementary infrastructure, not
invented research novelty.

## Pre-attempt gate

Pending non-author cheapest-solution/depth review and parent clearance.
