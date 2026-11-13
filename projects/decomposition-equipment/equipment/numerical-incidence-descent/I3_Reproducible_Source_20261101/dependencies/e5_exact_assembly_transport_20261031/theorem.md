# E5 — Marked exact assemblies and sharp local-to-global transport

31 October 2026. Author mathematical P theorem for original E5, contract lines
482–498. This is a bounded, parameterized theorem, not a claim that every
virtual equipment has this exactness doctrine. Finite executable C evidence,
independent review and acceptance are separate artifacts. No new full Lean
formalization or completion of the entire original contract is asserted.

## Result and provenance first

Inside the **full** graph–finite-span equipment `S(N,M)`, an actual assembly is
coefficient-exact precisely when every target witness has exactly one source
tuple above it, with the declared scalar condition. For a retained finite tree,
this must be checked at every named assembly, not merely at the evaluated root.
Internal interface transport additionally requires exactly one lift of every
feasible old tuple at every named composite run; nullary units require the
separate injectivity test. These finite-table conditions are necessary and
sufficient for the specified componentwise exact comparison and give coherent
transport through arbitrary finite substitution trees. Proper supported-subset
inclusions give a genuinely noninvertible, all-arity positive family.

The quotient boundary is equally concrete. Unit-subgroup scalar equations retain
coefficient-exactness and actual opcartesianness, but not literal scalar-one
normalization. Graph-activated coefficient section equations preserve the full
virtual equipment while destroying actual-bijection marking at every active
graph. Retaining the missing actual intermediate bijections gives the already
proved coherent repair; the exact unmarked alternative is endpoint-thinness of
all active realizable runs. Neither repair reconstructs missing cross-edges or
removes nonexact cells from the equipment.

**Substantial inherited results, not new claims:** SPAN and E3 construct the
full model and classify actual opcartesian cells; CUT §§5–10 already prove the
actual-certificate tree system, arbitrary finite coherence, exact graft action
and lift-fibre/nullary restriction theorem; ACT §§2–7 already prove the activated
quotient, generated equations and sharp memory repair; D2 distinguishes relation
support from actual span witnesses; E1 §9.3 already proves the UL-certified
all-tree marking-preserving action and supported-subset/unit positive family;
I4 distinguishes all retained stages from an evaluated semantic occurrence tuple. The work here assembles their exact E5
consequences, makes the faithful-assembly test and mark hierarchy explicit, and
proves the combined primitive-equation classification in §6. Exact source paths,
sections and hashes are in the companion source map/inventory.

## 1. Bounded input, full equipment and three distinct marks

Fix `N≥0`, the full family of ordered simple graphs on `[r]`, `r≤N`, and a finite
commutative monoid `M`. All finite tagged interface sets, including empty sets,
and **all** functions between them are allowed. A horizontal is `(G,S)` with
`S=(A←l E→r B)` an actual finite span. A path has every actual intermediate
interface and occurrence retained, including repeated types and empty graphs.
There is no bound on arity, number of empty occurrences or finite tree depth.

For a path `p=(S_1,…,S_n)` write

    P(p)={(a_0,e_1,a_1,…,e_n,a_n):
           l_i(e_i)=a_(i−1), r_i(e_i)=a_i},
    P(()_A)=A.

A cell is `(U,φ,m)`: `U` is an actual ordered partition of the retained output
graph G inducing its source graphs, `φ:P(p)→E` is an endpoint-compatible function,
and `m∈M`. For sides `f,g`, compatibility is `lφ=fπ_0`, `rφ=gπ_n`. Nullaries
require output graph empty, retain their map `A→E`, both sides and scalar; they
are not identified with empty syntax. Substitution lifts child subsets through
their increasing enumerations, substitutes their actual tuple maps and
multiplies every vertex scalar. SPAN §§1–5/E3 §§2–4 prove the laws, all cartesian
restrictions and contextual universal units for every such cell.

The following marks are on **globular** cells, i.e. identity exterior sides:

    Ex_c^1(α)  iff φ is bijective and m=1;
    Ex_c^×(α)  iff φ is bijective and m∈M^×;
    Ex_op(α)   iff α is contextually opcartesian.

For the full graph family, E3 Theorem 7.1 and Corollary 7.2 prove

    Ex_op(α) iff s(p)≤1, φ bijective, m∈M^×,              (1.1)

where `s(p)` counts nonempty **graph entries**, regardless of span support.
Thus `Ex_c^1` is normalized coefficient exactness, not universal composition.
The scalar-one universal mark adds `s(p)≤1` to `Ex_c^1`. A cartesian restriction
cell is a different universal property and its apex projection need not be a
bijection; it is not assigned either coefficient mark for that reason.

All three are predicates on cells of the full equipment. Nonbijective maps,
nonunit scalars and cross-edge-dependent nonuniversal assemblies remain valid
cells. For nonglobular comparisons first factor through the stated cartesian
restriction, and test the resulting map over the **same new exterior objects**;
a raw bijection merely covering noninjective endpoint maps does not suffice.

The chosen restriction has apex

    E[f,g]={(a′,e,b′): f(a′)=l(e), g(b′)=r(e)}.

An endpoint-preserving map `φ` pulls back to `(a′,z,b′)↦(a′,φ(z),b′)`.
Pullback preserves bijectivity, although it may hide a defect outside its
image and need not reflect bijectivity. This is distinct from separately
restricting each source component and composing them, examined in §4.

## 2. Faithful exact assembly from primitive witness tables

A finite planar tree retains its actual leaf path, every intermediate graph
and span, every local partition and coefficient table `t_v:P(children_v)→E_v`,
and every scalar `m_v`. Child outputs literally match their parent occurrences.
All cells in this section are globular. Every intermediate graph is the induced
graph on its descendant retained vertex blocks. The two elementary checks of
validity are ordinary finite endpoint/table typing and the partition equations;
these precede any exactness test.

Flattening the descendants of v gives a specific map

    d_v:P(leaves_below_v)→E_v,
    d_v=t_v P(d_children) ρ_v^(-1),                       (2.1)

where `ρ_v:P(P(leaf_runs))→P(all_leaves_below_v)` is tuple flattening. On an
external leaf use its unary identity identification. An empty run uses its
specified boundary coordinate. These functions are computed from the supplied
tables, not chosen from equal cardinalities.

Call the retained assembly **coefficient-faithful** when every named d_v is an
endpoint-preserving bijection. It is normalized exact when, in addition, every
named local scalar is 1; the unit-scalar variant requires each local scalar
in `M^×`. This is a fibrewise reconstruction assertion about **actual span
witnesses**. It is not reconstruction of an output graph from its pieces, not
faithfulness of the graph-forgetting functor, and not a claim that a refinement
forest itself has an inverse. Keeping all local tables/occurrences is part of
the specified information, so a root-only observation is a different doctrine.

### Theorem 2.1 — structural faithful-assembly criterion

For any valid finite retained tree, coefficient-faithfulness is equivalent to

    n_v(y):=|{z∈P(children_v):t_v(z)=y}|=1
    for every named vertex v and every y∈E_v.            (2.2)

Add the individual scalar-one or unit table tests for the respective exact
mark. Thus the criterion is independently checkable from finite leg/function
and monoid tables. If all requested intermediate assemblies are actual
opcartesian cells, the further necessary and sufficient condition at each
vertex is `s(children_v)≤1`.

**Proof.** A total finite function is bijective iff each of its target fibres
has one element. At fixed interface objects, P sends a family of endpoint-
preserving bijections to a bijection: apply their inverses to the same apex
coordinates, preserving all shared endpoint equalities. If (2.2) holds,
induction in (2.1) proves every d_v bijective. Conversely suppose every named
d_v is bijective. Starting at the leaves, solve

    t_v=d_v ρ_v P(d_children)^(-1).

The right side is a bijection, proving (2.2) at each vertex. This necessity uses
all retained children; a root-only inverse would not justify it. Scalar tests
are on the supplied local labels, and (1.1) proves the final clause. ∎

Empty-to-empty passes (2.2) vacuously; empty-to-nonempty fails. A purported
nonempty-to-empty total function is invalid input. An empty tuple carrier does
not erase the graph, local scalar, or occurrence. An old nullary map still has
domain its actual boundary set, not automatically a singleton.

**Sharp root limitation.** Over singleton endpoints, the tree with local maps
`{*}→{0,1}→{*}`, first selecting 0 and then collapsing, has bijective flattened
root map and two failed local tests. For scalars a nontrivial unit `h` and
`h^(-1)` have aggregate 1 but neither local label is normalized. If only the
evaluated original B3 occurrence operation is retained, test its evaluated
map instead: recursively count its fibres by

    N_v(y)= Σ_(t_v(u)=y, compatible u) ∏_children c N_c(u_c),
    N_leaf(x)=1.                                         (2.3)

The sum/product enumerates precisely the fine tuples choosing each local
witness; hence `N_root(y)=1` is necessary and sufficient for that **evaluated
occurrence** map. It is not equivalent to (2.2). I4 §3B proves this distinction;
E5 does not impose fully staged retention on an original semantic arrow that
did not retain those stages.

## 3. Arbitrary finite tree substitution and comparison squares

### Theorem 3.1 — inherited marked local-to-global theorem, explicit form

On a fixed retained graph/partition and actual span data:

A cut tree over an arbitrary outer a has an explicit root vertex carrying a.
The zero-leaf corolla is a genuine nullary root and is included. A vertex-free
one-edge tree represents only an identity, not an arbitrary a; it is allowed
in §2 with vacuous local tests but is not an extra factorization of every a.

1. Globular `Ex_c^1` cells are closed under all finite typed substitutions,
   including identity and genuine nullary-unit insertion. The same holds for
   `Ex_c^×`; actual opcartesian cells are closed when every local cell satisfies
   (1.1).
2. For an arbitrary fixed outer cell a, possibly nonexact, the groupoid of
   proper normalized coefficient-exact factorizations over any specified finite
   cut tree, retaining every actual bijection β and scalar **1** at proper
   vertices and fixing leaves and root, is nonempty and contractible. There are actual coherent
   contractions, splits, rotations, units and exact graft maps.
3. Given an exact proper old diagram and a supplied exact proper new diagram,
   with fixed-interface leaf comparison maps k_i, the unique coefficient
   comparison at every proper vertex is

       k_v β′_v = β_v P(k_children),
       k_v=β_v P(k_children)(β′_v)^(-1).                 (3.1)

   Define the new root by `γ_new=γ_old P(k_children)`. If a new root is already
   supplied independently, this displayed equality is an additional validity
   test for that comparison, not a consequence of proper-node exactness. For
   genuine scalar-labelled cell comparisons, proper β and β′ have scalar 1,
   the scalar s_v of k_v is the product of its child-comparison scalars, and
   the new root scalar is defined to be the old root scalar times the product
   of its child-comparison scalars. An independently supplied root must pass
   that scalar equation too. The pure coefficient-diagram statement omits
   scalars explicitly. No cancellation of γ or of a root scalar is used.
   The coefficient comparison is invertible on the **whole retained diagram**
   iff the individual tested leaf/stage maps satisfy (2.2). For invertibility
   as genuine unary equipment-cell comparisons additionally require each
   supplied scalar to be a unit; the scalar-one certified doctrine instead
   requires literal 1. In the evaluated semantic-occurrence variant use (2.3).
4. These comparisons commute with every finite graft/contraction/regrouping
   diagram; after the boundary tests in §4 they also commute with successive
   allowed interface changes and with graft/interface squares.

**Construction and proof, crediting CUT §§5–10 and I4 §§3–3B.** For (1), tuple
substitution of bijections at fixed shared interfaces is a bijection, by the
componentwise inverse followed by regrouping. Products of 1, respectively
units, stay so. If each local graph source has at most one nonempty entry,
recursing down its sole possibly nonempty child shows that the flattened
source has at most one nonempty entry; (1.1) applies.

For (2), at each proper edge use the flat tuple span of its retained leaf run
and canonical flattening as β; the root map is a composed with regrouping.
Given any other marked object, recursively invert its β to obtain the unique
comparison to these flat spans. The defining root equation ensures it also
commutes at the arbitrary root; no inverse of that root is used. Thus every
object has a unique isomorphism to the canonical object. Contraction replaces
`β_w` by `β_w T_(…,β_v,…)` and discards the contracted edge; at the root do the
same with γ. Splitting inserts a flat run span and its flattening and adjusts
the parent by the inverse regrouping. Its comparison to an existing split is
the supplied old β. Unary insertion uses the actual unary tuple identity;
nullary insertion uses the named empty run and `I_A`, not an arbitrary empty-
graph component. Exact grafting uses each supplied child's actual bijection
at the old occurrence. These formulas construct the maps **before** invoking
uniqueness for their coherence.

Equation (3.1) proves (3) by induction because P preserves fixed-interface
bijections. Conversely a componentwise inverse includes an inverse at each
retained leaf/stage, so each such table must pass. An arity-changing forest
can still be noninvertible as a forest; only its coefficient comparison is
being inverted. Arbitrary nonexact grafts also give the directed comparison
(3.1), but not an inverse, and their entire original occurrence tuple remains
part of the data. Their literal grafted tree need not be exact-proper; it is
represented faithfully by the old exact skeleton plus the external graft
forest, as in I4 §3B, not misclassified as a new exact-proper object.

For (4), on a fixed finest tuple any two routes apply the same local function
to the same occurrence subtuple. Tuple flattening only changes grouping;
induced graph restrictions satisfy `i_(i_U V)=i_U i_V`; scalar evaluation uses
the same finite list of vertex labels. Nested and disjoint contractions,
grafts and unit insertions therefore give identical maps after the specified
regrouping identifications. Substituting (3.1) twice yields the naturality
formula for the composite k-family. The split comparisons are the unique
families satisfying these already constructed equations, so all finite
rotation diagrams, including pentagons, commute. This proves an induction
for arbitrary finite depth, not an extrapolation from finitely checked trees.

For two cuts with the same actual named planar atomic frontier, their mixed
comparison is `χ^(-1)ρ`, transported through their retained β maps, where ρ
and χ are row/column flattenings. The square

    Xi_old K_rows = K_columns Xi_new                     (3.2)

holds pointwise on each fine named tuple for the same reason. Distinct
nonparallel frontiers do not acquire a slot permutation; I4's ordered/type
criterion is required if an independent crossing cut is requested. ∎

The root may be nonexact throughout (2)–(4). This is a rooted module/cut
statement, not a fabricated simplicial object of arbitrary outer maps with
undefined deleted-interval faces. CUT's separate exact interval object has
its own all-degree simplicial construction; no stronger E5 claim uses it.

## 4. Restriction, internal seams, and sharp all-run boundary tests

Let `f_i:A′_i→A_i` be an incidence-compatible family along a nonempty run
`p=(S_1,…,S_n)`. Every occurrence identified by the retained diagram uses the
same map; merely equal names do not identify other occurrences. Put
`S′_i=S_i[f_(i−1),f_i]`. The canonical comparison is

    c_f:P(S′_1,…,S′_n)→P(S_1,…,S_n)[f_0,f_n].           (4.1)

It forgets chosen internal lifts but retains the old apex witnesses and the
specified lifted exterior endpoints. The transported coefficient of t is

    t′=(f_0,f_n)^*t · c_f.                               (4.2)

These are two separate arrows over the same new exterior objects. Pulling
back t is not the same as c_f. For nonglobular apex maps first use their
canonical lift into the exterior pullback; test that lift, not the raw map.

### Theorem 4.1 — exact fibre criterion, empty and nullary clauses

For a target tuple z of (4.1), with old internal interface values `a_i`, its
actual fibre is

    c_f^(-1)(z) ≅ ∏_(0<i<n) f_i^(-1)(a_i).               (4.3)

Hence c_f is bijective iff the product of these finite fibre cardinalities is
1 for every feasible target tuple. For `n=1`, the internal product is 1 and
c_f is always a bijection. Empty target support passes vacuously. Surjectivity
of the relevant internal maps guarantees surjectivity, not bijectivity.

At a genuine nullary unit the comparison instead is

    A′→A′×_A A′,     x↦(x,x),                            (4.4)

which is bijective iff f is injective, including empty domain. The same test
applies to every marked globular nullary, since its actual bijective coefficient
identifies its output span with the identity span. It cannot be replaced by
an empty internal product. If old t is coefficient-exact, its
transport (4.2) is coefficient-exact iff (4.3), or (4.4), passes.

For a specified finite retained tree require these tests at **every named
local comparison with its actual child-composite spans**. They are necessary
and sufficient for componentwise transport of all its actual certificates.
For every regrouping of one finite path, require the tests at every realizable
contiguous composite run, including singleton runs and the entire frontier
when unary expansion is allowed, and at all permitted unit positions. This
is necessary and sufficient for all its finite exact cut trees, contractions,
rotations and permitted unit insertions. Repeated insertions use the same
unit equation and add no untested arbitrary empty occurrence.

**Proof.** Choosing an element above z is exactly choosing one lift of each
of its named internal values, independently. This gives (4.3), not merely a
cardinality argument. Equation (4.4) has one preimage on each diagonal pair
and none on off-diagonal pairs with equal images. Pullback of old bijective t
is bijective, so (4.2) is bijective iff c_f is. At a tree node use its actual
child-composite tuple: applying the same calculation recursively transports
β precisely when its local test passes. Necessity reads each named component;
it does not infer a hidden failure from a root alone. Every realizable run can
be exposed as a proper node (use a unary root for the whole frontier), proving
the all-cut converse. Successive changes forget the same lift coordinates
in either order. Thus their maps, and when present their inverses, commute
with each tuple graft/contraction. This proves the stated all-tree extension.
This is the existing CUT §10/E1 §9.3 theorem specialized to the explicit E5 marks. ∎

**Outer-only stability.** Reindexing just the two exterior objects of a
positive run leaves internal maps identities, so (4.3) passes; all coefficient
marks and, by (1.1), opcartesian assemblies are preserved. This is not a claim
that a cartesian projection itself has a bijective apex. For a nullary source,
there is one interface and its unit issue is (4.4), not two independent
exterior restrictions of a positive path.

**Why primitive-pair checking fails.** Let `A_0=A_3=1`, `A_1=A_2={0,1}`,
and take three singleton-apex spans following `*→1→1→*`. Let both internal
maps select 0. Each length-two comparison, after restricting its exterior
internal endpoint to 0, is empty-to-empty. The full path has one old target
tuple and no lift. Testing all runs or the next actual child-composite node
detects precisely this defect. This is the inherited CUT/D2/I4 control.

## 5. Structured positive families and relation-level negative controls

### 5.1 Noninvertible positive families, unbounded in tree depth

For any finite chain of interface sets choose actual subsets `U_i⊆A_i` and
maps `f_i:U_i↪A_i`. Use arbitrary finite spans whose left/right leg images
lie in `U_(i−1)` and `U_i`, arbitrary allowed graph data and retained normalized
bijection certificates. Every feasible internal value has a unique lift;
all maps are injective, so genuine unit insertions also pass. Composite spans
retain the same endpoint support property. Thus every finite exact substitution,
all regroupings and every permitted unit position transport coherently. If
some U_i is proper and the participating support is nonempty this is genuinely
noninvertible interface transport, not a family of disguised bijections.

More generally f_i may duplicate values outside every feasible support while
each supported value has exactly one preimage. Positive runs still pass. If such
an f_i is noninjective, nullary insertion there is forbidden by (4.4); omitting
that clause would be false. This supplies noninjective but support-admissible
positive-arity families without asserting a nonexistent all-unit extension.

### 5.2 Relations versus actual witnesses

For relations `R⊆A×B`, `S⊆B×C` and maps `f,g,h`, ordinary restriction always
has the inclusion

    (f,g)^*R ; (g,h)^*S ⊆ (f,h)^*(R;S).                  (5.1)

At `(a′,c′)` put `W={b:R(fa′,b),S(b,hc′)}`. Equality holds precisely when
`W≠∅ ⇒ W∩im(g)≠∅`. Uniformly over all R,S this is equivalent to
`A′=∅ or C′=∅ or g surjective`. D2 §§2–5 proves this and its all-path/tree
extensions, with the additional empty-old-internal-carrier exception for
longer paths. Relation equality needs **some** old witness with a lift at
each exterior pair, whereas (4.3) needs exactly one lift of **every actual
old tuple**. They are intentionally different tests.

For singleton exterior sets, old middle `{0,1}`, primed middle `{0}` included,
and the unique R,S pairs using 1, (5.1) is strict. All ambient cartesian
restrictions nevertheless exist. For `g:{0,1}→1`, constant, with singleton
old spans and exteriors, (5.1) is equality but c_g is two-to-one. Taking all
graphs empty makes the old assembly actually opcartesian by (1.1), yet its
internally transported cell is not: restrictions alone do not give exact
internal-substitution transport. Empty exteriors and empty feasible support
are already included by the fibre/emptiness formulas, not omitted exceptions.

On the complete relation quiver, D2's sharp uniform global result is that
all positive exact operations are preserved iff every primed carrier is empty
or every interface map is surjective; with all nullaries, iff every primed
carrier is empty or every map is bijective. Our supported-subset family is
an explicit useful restricted repair, not a denial of that obstruction.

## 6. Presentation quotients: actual equations, sharp preservation boundary

We fix the **complete concrete all-finite-span signature** used by SPAN and
E2's enlarged local reconstruction, not just original C5 names. Quotients
below keep objects, vertical maps, horizontal spans, full profiles, graph
partitions and occurrence positions fixed. All equations are parallel.
Let `H≤M^×` and let I be an induced-upward set of ordered graphs:

    G|U∈I ⇒ G∈I.                                        (6.1)

This is a finite incidence test on the graph table. Take the following actual
unary generating templates, together with the established local presentation:

* **Scalar templates:** `D((G,S),h)=id_(G,S)` for every concrete span S,
  nonempty G and h∈H. No such template is imposed at empty G.
* **Section templates:** if G∈I, `s_0=s_1:(G,S)⇒(G,S[2])`, where `S[2]`
  has apex `E×{0,1}` with legs ignoring the bit, and `s_i(e)=(e,i)`.
  Both have scalar 1.

These are templates over finite spans, not a claim of finitely many total
span generators, and not a definition by all desired semantic equalities.
Define `m≈_G n` to mean literal equality for empty G and `n=mh` for some h∈H
for nonempty G.

### Theorem 6.1 — generated quotient and complete-VE guardrail

The least substitution congruence generated by these templates is exactly

    (U,φ,m) ~_(I,H) (U′,ψ,n)
    iff U=U′, m≈_G n, and [G∈I or φ=ψ].                (6.2)

It preserves chosen cartesian restrictions and contextual universal units.
Within the stipulated all-or-nothing coefficient-forgetting rule, (6.1) is
necessary and sufficient for substitution compatibility. It can be checked
without solving a marking-preservation conclusion.

**Proof.** Scalar multiplication by H is a monoid congruence. A nonempty
induced child forces its retained whole nonempty; an active induced child
forces the whole active by (6.1). Hence (6.2) is stable under changing either
an outer cell or one child of any typed substitution, including empty/nullary
occurrences. Every generator holds in (6.2).

Conversely any scalar change in (6.2) is produced by postcomposition with
its corresponding D_h. For two coefficient maps at active G, let P be their
common actual tuple apex with its source endpoint span. There is a legitimate
cell from the source path to `(G,P)` with partition U, coefficient identity
and the given scalar; it need not be opcartesian. Apply `s_0=s_1` there and
postcompose the endpoint-compatible map taking `(z,0)` to φ(z), `(z,1)` to
ψ(z), with the original outer boundaries. This derives exactly the desired
coefficient equation. Combining these two derivations gives every pair in
(6.2); soundness excludes every other pair.

If an induced H_0 is active but its whole G is inactive, give the H_0-child
a two-point apex and use its two singleton selectors, identified by the
active rule. A binary graph-cut cell on G reads that bit, with a singleton
complementary apex. The two substituted G-maps differ and are not identified.
Thus the proposed rule is not a congruence. This is ACT Theorem 2.1's necessity,
including empty blocks; adding scalar orbits changes no coefficient fact.

Restriction-factorization appends/deletes forced exterior coordinates, keeps
the graph and scalar and bijects actual coefficient-function sets. Both it
and its inverse preserve (6.2). Contextual-unit factorization keeps the whole
graph and scalar and bijects the actual partitions/functions by forced unit
insertion. Hence both universal bijections descend. Equivalently E2
reconstruction Theorem 6.1 proves that **every** fixed-sort substitution
congruence on a complete virtual equipment automatically preserves restriction
and contextual-unit bijections. No false full-VE lift-uniqueness counterexample
is being used here. A separately selected nonnullary universal composite may
need its inverse source-compression closure; that different issue is below. ∎

The scalar-only case is `I=∅`. ACT is `H={1}`. Their combination is included to
make the mark boundary a classification in a concrete parameterized family,
not only two unrelated examples.

### Theorem 6.2 — exact mark descent and actual universal composition

In the family (6.2):

1. `Ex_c^×` and the **prequotient** `Ex_op` predicate are representative-
   invariant iff `I=∅`. For scalar-only quotients they are preserved and
   reflected, and (1.1) is also the intrinsic quotient opcartesian criterion.
2. `Ex_c^1` is representative-invariant iff `I=∅` and either `H={1}` or
   `N=0` (where the nonempty-graph scalar templates have no instances).
3. For arbitrary I the intrinsic quotient opcartesian cells still require
   `s(p)≤1`. At an inactive output graph their coefficient must be bijective;
   at an active output graph the specified coefficient map need only connect
   spans of equal endpoint support. The scalar must be a unit (equivalently
   have unit class). This quotient notion need not recover an actual β.

**Proof.** Multiplication by a unit preserves and reflects unitness: if mh is
a unit then m=(mh)h^(-1) is a unit. Moreover `[m]` is a unit scalar class iff
m is: `[m][n]=[1]` means mn∈H at positive G, and mn=1 at empty G; either makes
m a unit. Scalar-only quotient retains actual maps and partitions. For
`s(p)≤1` the canonical tuple composite κ remains contextual opcartesian:
its explicit source compression/regrouping and scalar identity factorization
preserve (6.2). Every other assembly factors uniquely through κ by a unary
map. In the scalar-only quotient that unary map is invertible iff its actual
coefficient is bijective and m is a unit, giving (1.1) intrinsically as well
as representative-invariance.

If any G is active, use singleton interfaces and the two-point apex E. The
parallel unary coefficient maps `id_E` and a constant map with scalar 1 are
equal by the actual section derivation in Theorem 6.1. The first is bijective
and opcartesian, the second is neither before quotient; their source has at
most one nonempty graph. Thus neither predicate descends in that case. If
H is nontrivial and a nonempty G exists, `D_1=D_h` with h≠1 similarly destroys
literal scalar-one marking even though both coefficients are bijections and
both scalars units. These witnesses prove sharpness of (1)–(2).

At active G, an endpoint-preserving unary map `c:S→T` has a quotient inverse
iff S,T have equal endpoint support and its scalar is a unit. Necessity uses
the existence of a reverse endpoint-preserving map; sufficiency chooses, for
each finite nonempty endpoint fibre, a witness to define such a reverse map.
The composites have the identity's partition and scalar class, so the active
rule identifies their coefficient maps with identities. At inactive G no
coefficient equations are added and actual bijectivity is necessary. With
`s(p)≤1`, factor through κ as above. If `s(p)≥2`, the cross-edge argument of
§8 remains valid because no whole graph is identified: the two distinct
possible whole graphs admit no common unary factor. This proves (3). ∎

The adjective “mark descends” above means that **all** representatives of a
class give the same verdict. The existential image “has some bijective
representative” is always a definable different condition, but does not
recover which β was chosen, does not reflect the mark on every preimage,
and may provide no determined actual comparison. The scalar-one existential
image likewise does not retain normalized local scalar labels.

### 6.3 Selected universals and the original presentation boundary

For an arbitrary selected nonnullary opcartesian `e:q⇒H`, let Q_e be its actual
contextual inverse source-compression operation. Its universality survives a
parallel congruence precisely when

    a[1,e,1] ~ b[1,e,1] implies a~b                       (6.3)

in every typed surrounding context. To make this a **generator-level proof
obligation**, apply Q_e to each contextual instance of each supplied equation
and exhibit a derivation of the resulting pair from those equations. Every
congruence derivation is a finite zigzag of such contextual instances, proving
sufficiency; necessity is inverse-factor invariance. It is not enough to test
only the bare uncontexted equations. This is E2 reconstruction §6.1, not a
generic decidability claim or a replacement for our explicit family proof.
The scalar-only family above checks Q concretely: canonical κ has scalar 1,
so its compression changes neither scalar nor whole graph and bijects the
coefficient tables. For an arbitrary opcartesian e, factor it through κ by
its invertible unary map; compression additionally multiplies by the inverse
unit scalar and conjugates by a coefficient bijection. Both preserve the
H-orbit relation. Thus the compressed equations remain derivable. A formal composite declaration in E4 is not licensed merely
by calling a coefficient-exact cut universal.

Original C5-only equations `D(W,h)=id_W` at old positive graph components are
a narrower signature. KERNEL and BRIDGE prove their actual original kernel,
fixed-endpoint refinement lifting and conservation through free chosen virtual
and ordinary envelopes. They do **not** prove that every new finite-span
horizontal/equation is generated from original C5. Our all-finite-span templates
above have explicitly declared that larger signature. The older BRIDGE sentence
suggesting substitution closure by itself never preserves complete-VE units/
restrictions is superseded here by E2's corrected complete-VE theorem; its
chosen-constructor and old-kernel results are used only at their valid scope.

### 6.4 A nontrivial quotient preserving the literal normalized mark

For `N≥1`, there is also a nontrivial positive family without replacing
scalar-one exactness by unit exactness. (At N=0 it is the identity quotient.)
For each `d≥2`, let `M_d={1,a,…,a^(d−1),0}` with `a^d=0`, ordinary
truncated-power multiplication, and 0 absorbing. At nonempty output graphs
impose the primitive equation `D((G,S),a)=D((G,S),0)` for every concrete span S;
at empty graphs impose none. The resulting scalar relation has classes `{1}`
and `J={a,…,a^(d−1),0}` at nonempty G, literal equality at empty G, and keeps
all graph and coefficient data. J is a multiplication ideal and induced empty
relations are contained in nonempty ones, so this is a substitution congruence.
The generator yields `a^j=0` by multiplication for every j≥1; conversely that
explicit two-class relation separates 1 and proves no further equalities.
Thus this is an independently generated parameterized quotient, not a desired
invariance hypothesis.

Its only unit is 1, and its quotient still has only the identity class as unit.
Therefore `Ex_c^1`, `Ex_c^×` and `Ex_op` all descend and reflect. The quotient is
injective on actual normalized exact cells, since neither their coefficient,
partition nor scalar changes. The canonical-composite compression proof above
also proves intrinsic opcartesian preservation/reflection. All restrictions and
units remain available, and the lift-fibre transport conditions are unchanged.

This positive family does **not** supply universal fixed-actual-endpoint
refinement lifting: take a positive-graph unary outer scalar a, its identity
child, and target scalar 0 with the same coefficient. The quotient refinement
equation holds, but every representative of the identity child's class has
scalar 1, so its actual composite remains a. KERNEL Theorem 3 gives the sharp
tradeoff within graph-indexed scalar kernels: universal fixed-endpoint lifting
forces the H-orbit family, whose literal scalar-one mark descends only when
H is trivial. Thus that strengthening forces equality for N≥1, whereas the
literal-mark-preserving family here is nontrivial after dropping that extra
lifting demand. This is a specialization of the inherited scalar-kernel test,
not a claim of faithful recovery of all quotient refinements.

## 7. Quotient marking repair and exact unmarked boundary

This section imports ACT §§5–7 and CUT §§6–10 at `H={1}`, so scalar memory is
not silently conflated with coefficient memory. Fix a quotient outer operation
[a], its actual G, its entire ordered leaf path and partition, and any finite
planar cut tree T. Root scalar m is arbitrary. At an inactive proper node keep
the actual coefficient bijection β. At an active proper node a **naive** object
keeps only its class and the condition that a bijective representative exists.
Its morphisms, however, retain actual prequotient endpoint-preserving span
bijections. This is expressly not the intrinsic isomorphism groupoid of Q_I.

### Theorem 7.1 — inherited sharp repair

At a naive object x, its automorphism group is

    A_x = ∏_(active proper vertices v) ∏_(a,b) Sym(E_v(a,b)).   (7.1)

Contracting v deletes its factor, and is an equivalence iff that factor is
trivial. Therefore every naive contraction over every realizable cut tree of
a fixed profile is an equivalence iff **every active realizable run composite
is endpoint-thin** (each endpoint fibre has size at most one). Include singleton
runs, empty/unit runs, repeated occurrences and the whole frontier under unary
expansion. This structural criterion is computed from the retained span-leg
and graph tables, not from an assumed coherent quotient action.

Retaining an actual β at every active proper node, and requiring

    h_v β_v = β′_v P(h_children)                          (7.2)

literally everywhere, gives the certified groupoid D_T. It is nonempty and
contractible, with the actual maps/coherence of §3, and forgetting certificates
recovers Q_I substitution. In the finite equivariant-mark model which retains
the original actual morphisms, a contractible repair over x has exactly

    |A_x|=∏_(active proper v)∏_(a,b)|E_v(a,b)|!           (7.3)

marks; chosen β tables attain this bound. This is not a universal bit-complexity
bound or an impossibility for doctrines deliberately discarding symmetries.

**Reason.** Activity is upward, so inactive subtrees have no active descendants;
(7.2) forces all their automorphisms from the leaves. At each active proper
node the naive quotient equation imposes no coefficient condition, and its
parent is active too. Its actual endpoint permutations are therefore independent,
giving (7.1). Restoring (7.2) forces each h recursively, giving the unique
certified comparison; contractions compose actual β tables as in §3. A finite
mark set retaining these symmetries has action groupoid `L//A_x`; trivial
stabilizers require a free action and contractibility also requires transitivity,
giving (7.3). This is ACT's exact argument, not a new generic quotient theorem.

For the scalar-only quotient, SCALAR separately describes all normalized-cut
lifts as `H^r`, one actual unit label per positive proper node, with the actual
root label adjusted to keep the flattened witness fixed. Its original unary
D_h gauges give a unique arrow between fixed marked lifts, coherently under
contraction/splitting. Empty graph nodes have label 1. If the outermost scalar
is additionally held fixed, the product is constrained by its H-stabilizer,
not necessarily product=1. Literal scalar-one preservation is not recovered
without these labels. Fixed-endpoint lifting is existence, not faithfulness:
for two nonempty children, the distinct actual tuples `(1,1)` and `(h,h^(-1))`
can have the same actual composite and the same quotient tuple. The retained
scalar labels and gauge tuples distinguish them; quotient labels alone do not. This independent inherited scalar repair does not fix
any failed boundary fibre test (4.3) or nullary diagonal (4.4).

At an active root graph, support equality can hide a nonbijective intermediate
comparison. For three singleton graph blocks with only the first-to-third
cross-edge, edge-containing activity makes the whole active and the first-two
induced graph inactive. Duplicate their internal singleton interface by `2→1`.
The proper comparison is two-to-one and fails actual β transport, while the
active root can report support-isomorphism. No root quotient verdict replaces
the runwise test. Existing nonexact/root cells remain available in Q_I and in
the rooted certified action; the repair does not outlaw them.

## 8. Nonreconstruction, ordinary completion and original faithfulness

Two singleton input graphs over singleton spans admit normalized coefficient-
exact cells into both the two-vertex edgeless graph G⁰ and the graph G¹ with
one cross-edge, with identical scalar and coefficient tables. Their pieces,
interfaces, spans and coefficient witnesses do not reconstruct which whole
was supplied. Neither cell is opcartesian in the full single-graph equipment:
a hypothetical representing whole would have to admit unary factors to both
G⁰ and G¹, whereas a unary graph partition forces literal graph equality.
For `N≥2` this is a genuine cross-edge counterexample, not a bound artefact.
For larger N the same construction works inside larger retained graphs.

Consequently coefficient-faithfulness in §2 preserves precisely the witness
information it claims and **retains** G and its partition as additional data;
it does not infer them from local pieces. ACT's quotients also retain G, so
they do not repair nonrepresentability by identifying these distinct wholes.
Nonexact witness cells still exist, for example the constant two-apex map,
scalar-zero cells when M has an absorbing nonunit, and arbitrary root maps in
D_T. This is a marked subtheory inside the full equipment, not its replacement.

For every finite category K, SPAN/E3's faithful tagged finite-set realization
F embeds original C5 components as `(G,ΓF(h))`. On each original full globular
profile the left endpoint forces the coefficient map and the right endpoint
equation is exactly the original grade-composite equation by faithfulness of
F. Hence original graph, full partition, grade path, scalar and every repeated/
empty occurrence are recovered; this comparison is bijective on those original
operation fibres and faithful on actual original refinement tuples. ACT adds
no coefficient equation there because the coefficient map was already forced.
The scalar-only quotient adds precisely its declared old scalar H-orbit
identifications, with the empty-graph scalar case unchanged. This is a precise
original-information comparison, not fullness on all new envelope cells.

E4 supplies the distinct positive ordinary completion of the free chosen
C5 virtual envelope by **new** horizontal composites. Its ordinary separating
model has graph words, a genuine unit empty word `[]`, and actual tuple spans;
`[empty graph]` is a different old horizontal. Universal composition concatenates
words and stores tuples. An old graph-cut cell factors through the new universal
path composite, but its unary factor need not be invertible and does not delete
cross-edge information. E4 proves old-profile equality and refinement-tuple
faithfulness, not that the concrete single-graph S embeds normally into this
word model: S's chosen unit would map to `[empty graph]`, not `[]`. We do not
assert that false completion or identify the new universal composite with a
chosen old whole. Thus E5's marks are compatible with E4's preservation boundary,
not a way around it.

## 9. E5 conclusion and stopping point

For the declared parameterized family, the independent structural data are:
finite graph incidence tables, full typed occurrence paths, span-leg and
coefficient tables, monoid/unit tables, actual interface-map fibres, and the
explicit primitive quotient templates. Theorems 2.1, 3.1 and 4.1 give faithful
assembly and coherent arbitrary-tree local-to-global transport. Sections 5–7
give sharp restriction/quotient failures and noninvertible structured positive
or certified repaired families, with the required empty/nullary cases. Section 8
proves the nonreconstruction boundary without excluding any nonexact cells.

The evidence target is original **E5 P+C**, with independent mathematical and
finite-check review. It is not a new full Lean theorem, a universal classifier
of abstract equipments, all-equation decision procedure, arbitrary-interface
exactness claim, or acceptance of later contract items. Source attributions
are part of this theorem, not optional background.
