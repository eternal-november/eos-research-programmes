# B1 — tree prefixes, unique forests, and all finite graft chronologies

Contract v0.1, SHA256 `47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
This is the P-evidence portion of B1, under the independently cleared target
`B1_B2_Targets.md`. It does not assert acceptance. Definitions below are independent
finite-address data applied to the accepted A1 planar tree syntax. B1 is mandatory
positive; no obstruction branch or contract amendment is used.

## 1. Generality and conventions

Fix any type of interfaces I, any directed family J(A,B), and any signature S.
Generators may be nullary, unary, or of any finite arity. Neither I, J nor S must
be finite or have decidable equality. A generator g has its exact ordered typed
path of inputs and an output component with the same exterior endpoints. Work
in one output fibre c; the total construction is the disjoint union of these
fibres. All statements quantify over every finite tree in this syntax, not just
binary or positive trees. A child occurrence is an ordinal in the generator's
ordered input path. Its ordinal is NOT its component label.

Write ε for the empty word, juxtaposition for concatenation of finite words of
natural numbers, and a ≺ b when a is a proper word-prefix of b. A1 identifies the
finite ordered path slots with these ordinals, preserving their components.
This is only a coordinatization of actual occurrences, not a quotient of them.

For a tree T define finite edge addresses E(T), internal vertex addresses V(T),
leaf addresses L(T), generator labels γ_T, and edge components χ_T recursively:

* If T is the identity leaf c, E(T)={ε}, V(T)=∅, L(T)={ε}, and χ_T(ε)=c.
* If T=g(T_0,…,T_{n−1}), E(T)={ε} ∪ ⋃_{i<n} iE(T_i),
  V(T)={ε} ∪ ⋃_{i<n} iV(T_i), and L(T)=⋃_{i<n} iL(T_i).
  Put γ_T(ε)=g and γ_T(ia)=γ_{T_i}(a). The root component is S.result(g)
  and χ_T(ia)=χ_{T_i}(a).

Here iA denotes the words obtained by prepending the one-letter word i. In
particular a nullary node has a root edge and vertex but no leaves. The empty
word in V(T) denotes the vertex incident to T's output edge; it is not a new
identity vertex. Every listed address is checked against the relevant arity,
so an integer word alone is not an occurrence unless it passes these checks.

**Address lemma.** E(T)=V(T) ⊔ L(T). The leaf addresses form a prefix-free set.
Every nonroot address has a unique immediate predecessor in V(T). For a∈E(T)
the subtree T|a exists uniquely and has output χ_T(a). If two trees with the
same output have the same sets V and the same γ labels, they are equal.

**Proof.** The first three assertions follow directly by induction in the two
constructors: the i-prefixed sets are disjoint, and ε is internal exactly in
the node case. For subtrees, traverse the word: at ε use T; at ia, the membership
condition supplies a root node with i<n and recurse into T_i. The last assertion
has no extensionality hidden in it. If V is empty, both trees are the identity
leaf of the prescribed output. Otherwise ε is in both sets, their generators
are equal by the root label, and hence their arities, child types and input
orders agree. Strip i from the common descendant addresses and apply induction
to each child; dependent function extensionality gives equality of the nodes. ∎

The left-to-right frontier order is the lexicographic order on the prefix-free
leaf words, comparing child ordinals at the first difference. It agrees with
the recursive ordered concatenation in A1, also for children having no leaves.
No total order on generator labels or components is used.

## 2. Forest arrows and independent prefix criterion

For a source T, a forest F supplies a typed tree F_l with output χ_T(l) at each
l∈L(T). By A1's `substitutionEquiv`, this is exactly `Tree.Substitution T`.
Its graft T[F] is the recursive leaf graft in the accepted Lean implementation.
The actual arrow T→U is a forest F together with equality T[F]=U. The equality
is a proposition; the forest is data. This is not a mere reachability arrow.

Define the independent, address-based relation T ⪯ U by

    V(T) ⊆ V(U), and γ_U(a)=γ_T(a) for every a∈V(T).

The trees have the same fixed output component. The definition does not mention
forests, substitutions, evaluation, or existence of a refinement arrow.

**Prefix/reconstruction theorem.** For all T,U of output c, the following are
equivalent:

1. T ⪯ U.
2. There exists a typed leaf forest F with T[F]=U.
3. There exists exactly one such F.

When they hold, E(T)⊆E(U), χ_U agrees with χ_T on E(T), and

    F_l = U|l     for every l∈L(T).

**Proof.** First prove (1)⇒(2), the assertions about edge addresses, and the
formula simultaneously by structural induction on T.

If T is a leaf c, it has no internal addresses, so the prefix condition imposes
no requirement on U beyond its fixed output c. The forest has one entry, namely
U at ε. Its graft is U, its output is c, and the assertions about E and χ hold.

If T=g(T_i)_{i<n}, its root is internal. The prefix hypothesis forces U's root
to be internal with precisely generator g, not just the same output or arity.
Thus U=g(U_i)_{i<n}, with the same ordered child components. For every i<n,
stripping the first letter gives T_i ⪯ U_i. Apply induction to each child and
combine the resulting forests. The constructor equation for graft proves
T[F]=U. The inductive edge-component statements plus the common root prove the
edge assertions. Source leaf addresses are exactly il for l∈L(T_i), and the
formula reduces to the inductive formula U_i|l. For n=0 there are no children
or forest entries: both trees are exactly the same nullary node, not arbitrary
closed trees.

For (2)⇒(1), structural induction on T shows that graft changes no existing
internal vertex or its witness; all changes are at its original leaves. The
same induction establishes the sharper address formulas in §3 below.

For uniqueness, induction on T is independent of the mere existence proof.
At a leaf, graft is the identity function on the sole forest entry. At a node,
equality of grafted nodes gives equality of every grafted child by constructor
injectivity; apply the induction hypothesis at each child and dependent function
extensionality. Thus F↦T[F] is injective. This proves (2)⇒(3); the reverse is
immediate. The explicit recovered entry U|l was already identified. ∎

**Antisymmetry.** If arrows exist both T→U and U→T, then T=U.
Indeed the theorem gives identical internal address sets and generator labels;
the address lemma gives literal tree equality. This includes unary chains and
nullary closed trees. No assumption that every strict extension grows its number
of leaves is made; such an assumption would fail for both unary and nullary
vertices.

**Raw category and poset identification.** Identity forests put an identity leaf
at every source leaf. For F:T→U and G:U→W, compose by grafting into every F_l
exactly the entries of G at the final leaves descending from l. A1's typed
occurrence correspondence identifies these leaves without choosing by component
label. Its graft is W by associativity, so it is an arrow T→W. The mandatory
Lean construction proves this endpoint fact and category laws on the actual
forest subtype. Unique forest recovery makes every hom subsingleton. Combined
with antisymmetry, the functor sending a forest arrow to the proof T⪯U has an
inverse: reconstruct U|l. Both composites are identities on objects and arrows.
Thus the raw category is precisely a poset category, not a richer category with
chronological arrows. Propositional proof irrelevance affects only equality
certificates, not the retained forest data.

## 3. Exact occurrence and address transport

For arbitrary T and F, the graft has

    V(T[F]) = V(T) ⊔ ⋃_{l∈L(T)} lV(F_l),
    L(T[F]) = ⊔_{l∈L(T)} lL(F_l).

The unions are disjoint because L(T) is prefix-free, and no source internal
address extends a source leaf. Labels and edge components are transported by
concatenation: at la use the corresponding data of F_l. Source internal labels
are unchanged. These formulas follow by structural induction on T; at a leaf
they reduce to εa=a, and at a node to associativity of prepending i.

Consequently the correspondence

    Leaf(T[F]) ↔ Σ l∈Leaf(T), Leaf(F_l)

is explicitly (l,a)↦la. Its inverse strips the unique source leaf prefix from
the final leaf address. Every final leaf has one such prefix by the displayed
formula, and prefix-freeness proves uniqueness. Its edge component is exactly
the component of a in F_l. These are arbitrary typed occurrences, including
several different l having equal component labels. If F_l is nullary the l
summand is empty, not identified with some other occurrence.

Given a second forest G on T[F], define G_l at a∈L(F_l) by G_l(a)=G(la).
Then the composed forest has

    (F;G)_l = F_l[G_l].

This is an equality of typed trees, not only their frontiers; it is the
leaf-reading equation for the structural `Tree.compose` implementation.
For a third layer the two occurrence identifications both send (l,a,b) to
(la)b=l(ab). Thus they have the same inverse and preserve the same component.
No coherence beyond ordinary equality elimination is assumed. At the profile
level, list the source leaves in their planar order, then the leaves of each
F_l in their planar order: this is exactly the ordered block expansion used by
`Path.slotExpand`. The A1 `frontierLeafEquiv` takes each profile slot to that
listed leaf. Thus the square with `slotExpand`, the graft-leaf correspondence,
and these frontier/leaf equivalences commutes, including empty blocks. Its
three-level version is the same triple correspondence, not merely equality of
lengths. The corresponding statements are part of the B1 mandatory Lean slice.

### Changing ordinal frontier indices

Stable addresses do not renumber under an unrelated graft. Ordinal indices do.
Let the current leaves be l_0,…,l_{m−1} in order. Graft F_i at l_i and put
r_i=|L(F_i)|. The new leaf l_i a_j (j-th leaf of F_i) has zero-based index

    new_index(i,j) = r_0+⋯+r_{i−1}+j,       0≤j<r_i.       (1)

This follows by induction on ordered concatenation of the leaf lists: all
leaves in blocks before i occur first, and exactly j leaves of block i precede
its j-th leaf. The images of the blocks are disjoint consecutive intervals and
exhaust the new indices, proving agreement with the A1 occurrence bijection.
If r_i=0 there is no j and no index in that block.

For a single corolla event at old index k with arity n, all other forest entries
are identities. Formula (1) says: indices <k stay fixed; the old leaf k is
replaced by k,…,k+n−1; old indices r>k become r+n−1. This last expression is an
integer equality with r≥k+1, so it is nonnegative even when n=0. For n=0 the
old leaf at ordinal k disappears from the frontier; its stable address remains
as the new internal vertex/edge address, and each later ordinal decreases by
one. For n=1 the index
is unchanged but a genuine internal vertex is added. These facts prevent both
nullary erasure and unary nonprogress from being mistaken for identity events.

## 4. Independent definition of executions

A legal atomic step on a current tree X consists of an address a∈L(X) and a
primitive generator g whose output is χ_X(a). Replace exactly that leaf by the
corolla g, keeping the other leaves as identity replacements. The step records
(a,g). It cannot replace an existing internal vertex: a∈L(X) is a premise,
and E=V⊔L is disjoint. A finite legal atomic execution is a finite sequence of
such steps, each checked in the current tree produced by its predecessors.
The empty sequence is allowed. An identity forest is not a primitive event and
adds no step. This definition does NOT presuppose a chosen final forest, an
ancestor order, or a linear extension.

Each step creates its one new internal vertex at a. Its new leaves are exactly
ai for 0≤i<arity(g); all other leaf addresses survive. That vertex can never be
removed or relabelled by later legal steps. Therefore no address can occur as
an event twice. A descendant ai… cannot be used before the event at a that
creates the edge ai. Events occurring at different incomparable addresses
cannot change each other's legality or typed output component.

**Local interchange lemma.** Suppose two consecutive steps at addresses a,b
are incomparable in word-prefix order. Interchanging them is legal, has the
same two recorded events, and has exactly the same resulting tree.

**Proof.** The first event alters only the leaf at a and its extensions. Since
b is incomparable, its leaf, component and ancestor path are unchanged; b was
already a leaf before the first event. Symmetrically a remains a leaf after the
b event. Both resulting trees keep the original structure and insert the two
specified corollas at disjoint leaf occurrences, so their recursive children
are equal. This is the simultaneous two-entry graft in either order, with its
full typed data. If ordinal indices rather than addresses are used, convert
both steps using formula (1); incorrectly keeping the second numeric index
fixed would be a different execution. ∎

If a is a proper ancestor of b, the event at b is not legal before the necessary
ancestor event at a: the edge leading to b has not yet been created. Such a pair
cannot be interchanged. A nullary event has no descendants, but still may be
independent of events in other branches.

## 5. The finite event poset and its execution correspondence

Fix T and a forest F. Its event set is

    E_F = { (l,a) | l∈L(T), a∈V(F_l) }.

The event's absolute address is la and its label is γ_{F_l}(a). Define
(l,a)≤(l',b) iff l=l' and a is a (possibly equal) word-prefix of b. Reflexivity
and transitivity are word-prefix properties. Antisymmetry follows because two
finite words prefixing each other are equal, and the tags agree. Thus this is
a finite poset: finite many source leaves, each containing finite many vertices.
Events from different tags are incomparable; within one tag, independence is
exactly incomparability of addresses, not merely inequality of labels.

A down-set D⊆E_F determines a partial forest F|D as follows. At each planned
vertex a of F_l, retain that vertex iff (l,a)∈D; when a is not retained, replace
its entire subtree by an identity leaf of its output component. Retain each
original leaf. Downward closure ensures that a retained vertex never has an
omitted ancestor. This recursive prescription is well-defined, typed, and
unique. Write T_D=T[F|D].

**Available-event lemma.** For e=(l,a)∈E_F\D, its absolute address la is a leaf
of T_D iff every strict predecessor of e belongs to D. In that case inserting
its corolla transforms T_D into T_{D∪{e}}.

**Proof.** Traverse the finite ancestor chain of a in F_l. If some earlier
planned vertex is absent, truncation stops at that ancestor leaf and a is not
an edge address. If all earlier vertices are retained, traversal reaches a;
a itself is absent, so it is exactly the truncation leaf with its prescribed
output. Inserting its corolla retains a and produces its child boundary leaves;
all later planned vertices remain truncated. This is precisely the recursive
definition for D∪{e}. ∎

A linear extension is a list containing each element of E_F exactly once, with
every strict predecessor occurring earlier. Linear extensions exist: repeatedly
choose a minimal element of the finite remaining poset (a minimal element
exists by following strict predecessors, which cannot continue in a finite
set). This uses only finite induction; computational decidable equality is not
required for the existence assertion.

**Execution/linear-extension theorem.** Legal complete atomic executions from T
to T[F] are in bijection with the linear extensions of E_F, recording the same
event labels and absolute addresses.

**Proof, from extensions to executions.** Given an extension e_1,…,e_N, let D_k
be its first k entries. D_k is a down-set by the defining order condition. The
available-event lemma makes e_{k+1} legal on T_{D_k} and identifies the new tree
as T_{D_{k+1}}. At k=0 all planned nodes are truncated and the tree is T. At k=N
all are retained and the tree is T[F]. This constructs a complete execution.

**Proof, from executions to extensions.** Each legal event adds exactly its
recorded internal vertex, and no later step removes it. The final internal
vertices outside V(T) are therefore exactly the event addresses, each once.
The graft address formula identifies these with precisely lV(F_l), so unique
prefix stripping identifies every event with a unique element of E_F and fixes
its generator label. Every ancestor event must occur first because otherwise
traversal cannot reach the descendant leaf. Thus the resulting event list is
a linear extension. Inductively the current tree after any k events is exactly
T_{D_k}: both constructions insert the same corolla at the same typed leaf.
Consequently the two constructions are inverse, not merely surjections. ∎

No final-state predicate has been substituted for execution legality: legality
was defined in §4, and the theorem proves its exact equivalence with the order.

## 6. Precisely which histories differ by independent interchange

**Finite-poset connectivity lemma.** Any two linear extensions of a finite
poset differ by a finite sequence of adjacent swaps of incomparable elements.

**Proof.** Induct on the number N of elements. For N=0 there is nothing to do.
Let x be the first element of the target extension and locate it in the other
extension. Every element y before x there is incomparable with x: y<x is
impossible because x occurs first in the target extension, and x<y is
impossible because the other extension places y before x. Swap x successively
left past those elements. Every swap preserves the linear-extension condition
because the swapped pair is incomparable and no other relative order changes.
Both lists now begin with x. Delete x and apply induction to the induced poset
on the remaining elements, then prepend x to each intermediate list. ∎

**All-history interchange theorem.** For any two legal complete atomic
executions starting at the same T, the following are equivalent:

1. their graft forests (the composites of their actual step forests) are equal;
2. their final trees are equal;
3. after the canonical source-leaf/address identification of events, their
   recorded executions are connected by adjacent swaps of independent events.

**Proof.** (1)⇒(2) follows by grafting. (2)⇒(1) is unique forest recovery, not
an assumption that a history is an arrow. If (1) holds with forest F, the
execution theorem converts both lists to linear extensions of E_F. Apply
connectivity, then the local interchange lemma converts every adjacent swap
back to a legal typed execution with the same endpoints. Thus (1)⇒(3).
Conversely each independent swap preserves its resulting tree by local
interchange; steps after the swap see literally the same current tree and
remain legal. Hence any finite sequence of swaps preserves the final tree,
proving (3)⇒(2). Dependent events cannot be swapped as proved in §4. ∎

This is a statement about all finite forests and all complete histories, not
only two demonstrations of commutativity. It identifies precisely what the raw
arrow forgets: interleaving of independent primitive additions. It does not
claim that different dependency orders or generator labels disappear.

## 7. Macro graft schedules and the boundary of the chronology claim

A finite macro schedule inserts an arbitrary finite forest at each stage.
For each macro forest, use its event poset and any linear extension to replace
that stage by atomic corolla events. The execution theorem (with that stage's
current tree as source) proves this expansion has exactly the same endpoint.
Concatenate the expanded stages. The resulting atomic execution therefore has
the same composite forest as the original schedule, by unique recovery.
Absolute event addresses in each stage are transported by concatenation at its
current source leaves. Repeating stages gives a word with parentheses erased;
concatenation associativity makes it the same final absolute address regardless
of staged presentation. Ordinal frontier positions are recalculated by (1).

A fixed arbitrary depth-first/preorder traversal of the finite forest is a
canonical legal expansion, since ancestors occur before descendants. Different
legal expansions of the same stage differ by the independent swaps of §6.
Thus all complete atomic expansions of macro schedules with the same composite
forest are interchange equivalent. Identity macro stages expand to no events.

There is deliberately no claim that a one-step macro schedule and a two-step
macro schedule can be related by swaps of macro steps: swaps preserve the
number of steps, and that claim would be false. The theorem compares their
proved atomic expansions. This distinction is essential when a macro insertion
contains both ancestors and descendants.

## 8. Discriminating phenomena and evidence boundaries

The general proofs include these cases without extra assumptions:

* Equal component labels at two source leaves give distinct tags l and l', so
  replacements may differ and independent events are not identified.
* A parent then child execution is legal; reversing it fails because the child
  address is not yet an edge. Two incomparable branch events are swappable.
* Nullary nodes remove one current leaf and create none; they remain genuine
  events. Closed source trees have the unique empty forest and no further raw
  extensions. Unary chains change internal structure without increasing arity.
* A proposed internal-vertex replacement is not an elementary refinement and
  generally violates prefix preservation; a leaf-only execution cannot realize
  it. This is a typed legality rejection, not a missing implementation feature.
* Three-stage nesting and arbitrary interleavings use the same occurrence
  concatenation and full-component transports, not repeated label matching.

L evidence is supplied by `RawRefinement.lean` and accepted A1 imports for the
category, actual forest composition and core occurrence correspondence. This
file supplies P evidence for the independent address-prefix theorem and the
full execution comparison. `B1_ChronologyChecks.py` supplies only finite C
regressions, independently comparing address executions, tree grafting and
linear-extension/interchange enumeration; it is not a proof of the unrestricted
theorem. Exact theorem locations and axiom/build evidence are indexed separately.

The standard free-tree prefix order and the finite-poset linear-extension
connectivity argument are established infrastructure. Their typed, occurrence-
retaining integration is the claimed B1 implementation/proof scope, not a
claim of a new general combinatorial theorem or completion of B3/B4.
