# D1 — Equivariant free/presented calculi and witnessed refinement transport

**Result first.** Given an arbitrary specified strict groupoid action on typed
components and primitive witnesses, the action extends uniquely to the free
calculus, descends exactly when it preserves the generated parallel congruence,
and gives strictly coherent functors on the full occurrence-refinement
categories. The extension and descent satisfy the equivariant free and
presented universal properties. Nothing assumes an action on the quotient.
The theorem includes a local-interface version: independently chosen arrows at
individual boundary **occurrences**, not merely a global renaming of endpoints.
Local changes act on incidence-compatible charted refinement categories;
coherent whole-signature changes give ordinary uncharted refinement functors.
A finite relation-interface example checks all seven existing local equations,
with controls for non-invariance, repeated components, and erased symmetry.

**Evidence boundary.** This is a P-level mathematical source, dated 31 October
2026. The separate finite action certificate supplies L evidence only for its
stated slice. This document does not certify all of the completion contract,
D2, or D3. Existing A2/A3/B2 and C5 results are reused, not re-proved or claimed
as novel. In particular no general normalization, raw-completion equivalence,
or decidability theorem for arbitrary equations is asserted.

## 1. Sources, level, and conventions

The source root throughout is
`/workspace/shared/contract_revision_20261028/extracted/witnessed_decompositions`.
The precise source/obligation crosswalk is in `source_obligation_map.md`.
The principal inherited facts are:

* `research/workstream_A/A2_AdjunctionProof.md`, §§1–6: the actual free tree
  calculus, extension among **all** strict maps, both naturality laws, and the
  actual hom-set bijection, retaining whole components and full ordered paths.
* `research/workstream_A/A3_PresentedUniversalProof.md`, §§1–4: the independently
  generated least parallel substitution congruence, its actual quotient,
  representative-independent substitution, and the presented hom-set bijection.
* `WitnessedDecompositions/SemanticRefinement.lean` and
  `RefinementFunctoriality.lean`: arrows are actual original-slot tuples;
  composition, identities, strict interpretation functors and their laws.
* `research/workstream_integration/proof/Semantics_Transport_Factorization.md`,
  §§2,4–5, and `Completion_Comparison.md`: full-tuple parameter maps,
  concrete equation-basis transport, and coherent normal sections for the
  already presented graph-cut family, not arbitrary equations.
* `research/workstream_C2/proof/C2_Model_Theorem.md`, §§1–6: actual relation
  components, all-arity containment/exact calculi, tuple-level bijective
  interface transport, and incidence-compatible local diagrams.

We work with sets, finite trees and finite ordered profiles; the interface
and primitive sets need not be finite. More generally take a fixed universe
closed under these constructions and quotients, with targets in any larger
universe. All equalities below are mathematical equalities of functions/data,
not claims of definitional equality in Lean. Proofs of typing equalities are
not extra witnesses. We use right-to-left composition: `hg` means first `g`,
then `h`. Ordered lists use their canonical concatenation/flattening
identifications. A formula concerning slots always uses the ordered bijection
`(i,j) <-> the j-th slot in the i-th concatenated block`, including empty
blocks. No permutation of occurrence positions is built into an interface
change. This is the nonsymmetric calculus already supplied by A1–A3, not an
unannounced symmetric-operad extension.

**Strict convention.** Input actions satisfy identity and composition as
actual equalities. Output action laws do likewise. We do not assert that an
arbitrary weak action has already been strictified. Section 8 states the
precise natural-isomorphism coherence when noncanonical normal sections are
used. It is a consequence of the existing coherent completion theorem, not
an assumption about arbitrary equations.

## 2. Arbitrary strict signature diagrams: the global theorem

### 2.1 Declared input class, with no quotient action assumed

Let `H` be any small groupoid. At each object `x` give a quiver `J_x` of
interfaces and actual components, a typed primitive collection `S_x(c;p)`
where `p` is a full ordered path with the endpoints of output component `c`,
and a set `E_x` of pairs of parallel free trees. A primitive includes its
whole component and full path, not just its arity or endpoints.

For each `g:x->y` give:

1. a quiver isomorphism `B_g:J_x->J_y`, mapping actual components as well as
   interface objects, hence mapping full paths occurrence by occurrence;
2. a bijection `s_g:S_x(c;p)->S_y(B_g c; B_g p)` at every fibre.

The functions obey `B_1=id`, `B_hg=B_h B_g`, `s_1=id` and
`s_hg=s_h s_g`, with the indicated fibre reindexing. These are the **supplied
transport data**. No action on trees, equations, quotient operations, or
refinement arrows is input. They may act nontrivially on arbitrary parallel
primitive witnesses even when all their component types are fixed. Thus the
class is not limited to renaming endpoint labels.

Write `F_x=F(S_x)`, `~_x` for A3's least parallel substitution congruence
containing `E_x`, and `P_x=F_x/~_x`. Invariance has two distinct levels:

* **literal declaration invariance:** transporting a pair of `E_x` gives a
  pair of `E_y` (possibly with the two sides reversed);
* **derivable invariance:** transporting a pair of `E_x` gives a pair related
  by `~_y`.

The latter is the exact sufficient and necessary condition for descent; the
former is a particularly effective, stronger certificate. We prove this after
constructing transport on trees. In the concrete example all seven families
satisfy the stronger literal condition, checked individually in §9.

### 2.2 Construction on free trees

For the identity leaf `1_c`, put `T_g(1_c)=1_(B_g c)`. At a node with primitive
`a` and ordered child trees `t_i`, put

    T_g(a(t_1,...,t_k)) = s_g(a)(T_g t_1,...,T_g t_k).       (2.1)

This is well typed: the output of each image child is precisely the matching
image input component of `s_g(a)`. Nullary nodes use the empty family. It
preserves every external leaf position, all intermediate interfaces, and
primitive multiplicity. Induction on the tree proves the mapped full frontier
is `B_g p`.

For every independently specified replacement profile `q_i` and family `u_i`,
structural induction gives

    T_g(t[u_i]) = (T_g t)[T_g u_i].                         (2.2)

At a leaf this is its defining identity property. At a node, the forest
splits into the consecutive blocks belonging to its ordered children; the
map preserves these blocks, and induction applies to each child. Empty
blocks require no choice or deletion. This proves strict substitution
preservation, not merely agreement of evaluated endpoint composites.
Induction similarly gives

    T_1=id,       T_hg=T_h T_g,       T_(g^-1)T_g=id.        (2.3)

Therefore each `T_g` is a base-changing strict calculus isomorphism.
Alternatively, after pulling the target back along `B_g`, A2 constructs this
map from `s_g`; its uniqueness gives the same equations. The direct recursion
makes the otherwise fixed-base source theorem's base change explicit.

### 2.3 Exact quotient-descent criterion

**Theorem 2.1.** For any specified arrow `g`, the formula

    P_g([t]) = [T_g t]                                    (2.4)

is a well-defined map on the actual A3 quotient iff

    (l,r) in E_x  ==>  T_g l ~_y T_g r.                    (2.5)

When (2.5) holds for every groupoid arrow, these maps are strictly inverse
base-changing calculus isomorphisms, `P_1=id`, `P_hg=P_h P_g`, and projection
commutes with transport.

**Proof.** If (2.4) is well defined, declared pairs have the same quotient
class, so their images do; quotient exactness gives (2.5). Conversely induct
on a derivation of `t~_x u`. The equation constructor is (2.5). Reflexivity,
symmetry and transitivity use those properties in `~_y`. For simultaneous
substitution use the induction hypotheses for the outer and all inner
operations, then target substitution stability and (2.2). Hence `T_g` respects
the least generated congruence; it was not defined from a semantic kernel.
Quotient lift gives (2.4). Applying representatives proves strict identity
and substitution preservation. Equation (2.3) and surjectivity of projection
give all action laws. Inverse groupoid arrows give inverse quotient maps.
No injectivity or normal-form assumption on `E` was used. QED.

It is enough to check a generating arrow family and their inverses when the
specified groupoid is presented by generators: derivable invariance composes.
The supplied generator actions must themselves satisfy the groupoid's
relations on primitive/type data; this is not inferred from names.

### 2.4 Equivariant free and presented universal properties

A strict `H`-calculus diagram `M` over the same bases has strict maps
`M_g:M_x->M_y` over `B_g`, with the action laws. An equivariant primitive
assignment is a family `a_x:S_x->U(M_x)` of fully typed maps satisfying

    M_g a_x(v) = a_y(s_g v).                              (2.6)

A map of diagrams is a family of strict calculus maps over identity bases
commuting with all `g`. Then restriction to the primitive corollas gives
natural bijections

    Hom_H-Calc(F(S), M)  ~=  Hom_H-Sig(S,U M),              (2.7)

    Hom_H-Calc(P(S,E), M)
       ~= { equivariant primitive assignments satisfying every E_x }. (2.8)

**Proof, including equivariance rather than assuming it.** A2 extends `a_x`
uniquely to `a_x^#:F_x->M_x`. The two strict base-changing maps
`M_g a_x^#` and `a_y^# T_g` agree on primitives by (2.6); A2 uniqueness after
base reindexing, or induction using (2.1), makes them equal. Thus the free
extension is equivariant. Conversely restricting an equivariant map gives
(2.6). A2's extension/restriction inverse laws apply objectwise, proving
(2.7) with no additional choices.

If assignments satisfy `E_x`, A3 factors each free extension uniquely through
`P_x`. To prove equivariance of the factors, precompose the proposed two maps
with the surjective projection `F_x->P_x`; both composites are the preceding
equal free extensions. Surjectivity gives equality. Conversely quotient maps
satisfy `E_x` on primitives. A3's inverse laws prove (2.8). Naturality in an
equivariant target map follows by postcomposition; in a map of signature
presentations it follows by precomposition. Each equality can be checked on
primitive generators and then extended by uniqueness. These are genuine
hom-set universal properties for strict equivariant maps, not an asserted
2-categorical biuniversal property. QED.

## 3. Individual interface changes: the local construction

The preceding theorem is uniform in **all** strict signature-groupoid
diagrams, but is not by itself a statement that arbitrary independently
changed intermediate interfaces extend to a single global quiver map. This
section supplies the more local construction, necessary for that reading of
D1, from primitive data alone.

### 3.1 Boundary groupoid and component/primitive actions

Let `I` be any small groupoid of allowed interface isomorphisms. Give a
bifunctor

    C : I x I -> Set.

An element `c in C(A,B)` is an actual component from `A` to `B`. For
`f:A->A'`, `g:B->B'`, write `c^(f,g)` for its image. This covariant notation
uses invertibility on the source boundary; equivalently a conventional
contravariant/covariant action is evaluated at `(f^-1,g)`. It asserts no
composition of components. The only laws are the supplied identity and
composition laws of the bifunctor; in particular these maps are bijections.

A full profile has a frame `(A_0,...,A_n)`, components
`c_i in C(A_(i-1),A_i)`, and whole `W in C(A_0,A_n)`. For independently chosen
arrows

    f=(f_0,...,f_n),       f_j:A_j->B_j,

put `p^f=(c_i^(f_(i-1),f_i))` and `W^f=W^(f_0,f_n)`.
When `n=0` there is **one** boundary occurrence and one arrow `f_0`, not two
independent maps. An interface label repeated at two distinct positions need
not receive the same arrow; incidence identifications, not equality of labels,
determine when maps must coincide.

These profiles and their `f` form a groupoid `Prof(C)` (length is fixed along
an arrow). The primitive input is a functor `S:Prof(C)->Set`: at each profile
it gives primitive witnesses and a bijection `s_f` between the corresponding
fibres, satisfying strict identity/composition. This is an arbitrary supplied
local primitive action, not an action on the completed quotient. No component
or witness action follows from the existence of interface names.

A **transported calculus** over these data has maps
`tau_f:M(W;p)->M(W^f;p^f)` obeying the groupoid action laws, identity preservation,
and the following substitution law. Let the outer profile have `k` slots and
let child `u_i` have length `n_i`. Set `s_0=0`, `s_i=n_1+...+n_i`. For a
boundary-arrow list `f_0,...,f_(s_k)` on the expanded profile, set

    f_outer=(f_(s_0),...,f_(s_k)),
    f_i=(f_(s_(i-1)),...,f_(s_i)).

Then require

    tau_f(a[u_i]) = tau_(f_outer)(a)[tau_(f_i)(u_i)].        (3.1)

This condition is formulated only for the actual incident boundaries. If
`n_i=0`, the two appearances at offsets `s_(i-1)=s_i` are the **same** arrow.
Conversely, any maps on a substitution diagram agreeing at shared incidences
are exactly of this form after flattening. All maps in a coherent composite
of diagrams must respect the transitive closure of these identifications.

### 3.2 Free local transport is constructed, not assumed

A raw tree with `n` external leaves has a canonical boundary index `0,...,n`.
Each subtree's frontier occupies a consecutive interval `[r,s]` of this
boundary list; its output endpoints are the corresponding interface objects.
A nullary subtree has `r=s`. This is proved by concatenating child frontiers;
parent child-boundary indices are their cumulative leaf counts. The assertion
holds even when components or interface labels repeat.

Define `tau_f` on a leaf to be the identity leaf on the component transported
by its two endpoint arrows. At a node with child lengths `n_i`, transport its
primitive by `s_(f_outer)` and recurse on child `i` with the sublist `f_i`.
The matching output/input components are the images under the SAME endpoint
arrows, so the node remains well typed. This constructs local transport on
all raw trees and its prescribed final profile.

The action laws follow by tree induction: identity labels act trivially and
composite labels compose at every node and boundary position. For (3.1), a
vertex of the substituted tree is either a vertex of the outer tree or of
one inserted tree. Both orders send that vertex's primitive label through
the same sublist of final boundary arrows, because the two ways of summing
consecutive leaf counts give the same interval endpoints. This proves (3.1)
vertex by vertex, including empty intervals. It also proves arbitrary-depth
coherence: both ways of flattening a three-level family use the same ordered
triple of positions and the same boundary arrows. Tree equality follows.

Thus the free local transported calculus exists for **every** `I,C,S` just
specified. A locally equivariant primitive assignment into any transported
calculus extends uniquely by A2; induction with (3.1) proves the extension
locally equivariant. Restriction and extension are inverse. This is the local
version of (2.7), not merely a global-automorphism special case.

### 3.3 Local quotient descent and equivariant universal property

Give parallel equation families `E(W;p)`. The exact descent condition is

    (l,r) in E(W;p)  ==>  tau_f(l) ~ tau_f(r)
    for every arrow f of Prof(C).                          (3.2)

Induct on A3 derivations exactly as in §2.3. At a substitution constructor,
the final chart `f` induces the outer chart and each child chart by the
cumulative offsets in (3.1); apply the induction hypothesis to these, then
substitution stability. This is the additional local step not covered by an
unexplained appeal to global renaming. It proves `tau_f` respects the actual
least congruence. The converse follows from quotient exactness. Consequently
`[t] -> [tau_f t]` defines the presented local transported calculus, with (3.1)
and all action laws checked on representatives. It is equivariantly universal
among local transported calculi satisfying `E`, by the same free extension,
quotient factorization and surjective-projection argument as (2.8).

**Real scope boundary, not a missing proof.** A separately prescribed change
of just the two outer endpoints does not specify changes at newly exposed
internal interface occurrences. It therefore does not by itself define an
uncharted functor on all refinements. Worse, a nullary child identifies its
boundary incidences: two unequal arrows there are not an allowed transport
of that nullary profile. Section 5 constructs exactly the coherent refinement
comparisons for arbitrary local data, while §4 handles supplied whole-diagram
actions. No undefined local choices are silently promoted to a global action.

## 4. Full occurrence refinement and global coherent comparisons

For any lawful calculus `M`, `Ref(M,W)` has objects the operations with whole
`W`, retaining their full profiles. A morphism `a->b` is a tuple `(u_i)` at
**each original occurrence** of `profile(a)`, with each `u_i` having output
that occurrence's actual component, and with

    a[u_i]=b.

Each entry retains its own entire input profile, so the tuple includes the
ordered segmentation of `profile(b)`, including zero-length blocks. Equality
of arrows is entrywise equality of these data, not equality of the substituted
total. Composition with `(v_j):b->c` has entry

    u_i[v_(s_(i-1)+1),...,v_(s_i)],                         (4.1)

where the `s_i` are cumulative lengths of the `u_i`. A nullary `u_i` remains
that same nullary entry under composition. Identity has the actual identity
operation at every slot. B2 proves the category laws, with the full ordered
occurrence transports; we use those results.

For the strict diagram of §2, define

    Ref(P_g): Ref(P_x,W) -> Ref(P_y,B_g W)
    a |-> P_g a,       (u_i) |-> (P_g u_i).                 (4.2)

The endpoint equality follows from strict substitution. The full child
profiles and their lengths are transported, not reconstructed from the final
profile. Identity preservation is entrywise. Applying `P_g` to (4.1) gives
exactly (4.1) for the image tuples; hence composition is preserved. Laws (2.3)
and (2.4) hold entrywise, giving

    Ref(P_1)=Id,    Ref(P_hg)=Ref(P_h) Ref(P_g),
    Ref(P_(g^-1)) Ref(P_g)=Id.                             (4.3)

Thus these are category isomorphisms, not just functors on object isoclasses.
The same construction works for free calculi, any strict semantic diagram,
and base-changing comparison maps. Explicitly, on the original raw category
`Raw(S_x,W)`, send a tree `t` to `T_g t` and its actual leaf-indexed forest
`(u_i)` to `(T_g u_i)`. Its endpoint equation is (2.2), and its composition
law is (2.2) applied to every forest entry. The existing B2 comparison
`Raw(S_x,W) ~= Ref(F_x,W)` uses the canonical component-preserving
leaf/ordered-slot bijection; transport keeps this same bijection, so the
comparison square commutes entrywise. Consequently the raw-to-presented
refinement functor, obtained by this comparison followed by quotient
projection, also commutes with transport. The local charted construction
in §5 applies verbatim to these forests and this same leaf/slot bridge.

In particular, projection induces `Ref(F_x)->Ref(P_x)` and its square with
transport commutes **on arrows as tuples**, because each entry is sent to
`[T_g u_i]` by either route. If an independently supplied semantic primitive
assignment is equivariant and satisfies `E`, its factor `e_x:P_x->M_x` from
(2.8) gives the commuting square

    Ref(e_y) Ref(P_g) = Ref(M_g) Ref(e_x).                  (4.4)

A2/A3 do not say `e_x` is an isomorphism. If a separate soundness/completeness
and generation theorem does prove it is one, (4.4) is a coherent comparison
of refinement category isomorphisms. No fullness is inferred from a mere
surjective generator evaluation or from equality of arrow endpoints.

The disjoint-union categories over all whole components obey the same laws;
without extra specified transport there are no refinement arrows between
different wholes. Strict diagram naturality on every generator, tuple entry,
and composition establishes all finite-chain coherence, not just a binary
comparison drawn on objects.

## 5. Full local refinement functors: charts and incidence coherence

Here `M` is any local transported calculus from §3, free, presented, or an
independently constructed semantic model.

### 5.1 The category carrying the required choices

Fix `W in C(A,B)` and arrows `f:A->A'`, `g:B->B'`. Define
`ChartRef_(f,g)(M,W)` as follows.

* An object is `(a,lambda)`, where `a` has whole `W` and `lambda` is a boundary
  chart on its full profile with first arrow `f` and last arrow `g`. If its
  profile is nullary, there is one boundary and this requires `A=B` and
  `f=g` as actual groupoid arrows. Internal maps are retained choices.
* An arrow `(a,lambda)->(b,mu)` is an entire refinement tuple `(u_i):a->b`
  satisfying the incidence equations

      lambda_i = mu_(s_i),        0<=i<=k,                 (5.1)

  where `s_i` are the cumulative lengths of the input profiles of `u_i`.
  These equalities compare arrows with the same source and target; thus
  their target-interface choices must also agree. No primitive or tuple
  is quotiented by them. They are admissibility conditions.

Identity tuples have `s_i=i`, so (5.1) holds. For consecutive tuples, if
`t_j` is the second cumulative-length vector, then the composite's offsets
are `t_(s_i)`. The two incidence equations imply
`lambda_i=mu_(s_i)=nu_(t_(s_i))`, proving closure under composition. Associativity
and units are inherited from the full B2 tuples. This is not an endpoint-only
or thin replacement category; it retains all occurrence-wise refinement
witnesses for the supplied compatible charts.

The source projection `U_(f,g):ChartRef_(f,g)(M,W)->Ref(M,W)`
forgets only the charts and keeps the entire operation and tuple. It is a
faithful functor, since no tuple entries are quotiented, but need not be full:
a source refinement can violate (5.1) for selected charts. No essential
surjectivity is claimed for arbitrary fixed endpoint arrows. For identity
endpoint arrows, the full subcategory with every boundary chart the identity
is canonically `Ref(M,W)`. These projections make the extra retained choices
and the precise uncharted comparison explicit.

### 5.2 Strict inverse comparison functors

Write `W'=W^(f,g)`. Define

    L_(f,g): ChartRef_(f,g)(M,W)
                 -> ChartRef_(f^-1,g^-1)(M,W')

on objects by

    (a,lambda) |-> (tau_lambda(a), lambda^-1),              (5.2)

and on a tuple by

    (u_i) |-> (tau_(mu restricted to [s_(i-1),s_i]))(u_i).  (5.3)

Formula (3.1) proves its endpoint equality. The image incidence conditions
are the inverses of (5.1). Identities follow from identity preservation.
For composition, the transport of (4.1) equals the composition of the
transported entries by (3.1), with exactly the same subinterval offsets.
Hence `L_(f,g)` is an actual functor on full tuples.

Applying the same construction with inverse endpoint maps returns every
object chart, operation and tuple entry literally: each boundary action is
followed by its inverse. Consequently

    L_(f^-1,g^-1) L_(f,g)=Id,
    L_(f,g) L_(f^-1,g^-1)=Id.                             (5.4)

The target projection is the composite
`V_(f,g)=U_(f^-1,g^-1) L_(f,g)`. Thus local transport has the honest functor
span `Ref(M,W) <-U- ChartRef_(f,g)(M,W) -V-> Ref(M,W')`,
and (5.4) interchanges its two legs. It is not mislabeled as a functor on
all uncharted refinements without supplied charts.

These are strict isomorphisms of the charted occurrence-refinement categories,
for arbitrary allowed local groupoid arrows, arbitrary equation families
satisfying (3.2), all arities and all refinement lengths.

### 5.3 Successive local changes and comparisons with syntax/semantics

Fix further endpoint arrows `h:A'->A''` and `k:B'->B''`, and set
`W''=W^(hf,kg)`. Define the twice-charted domain explicitly: an object is
`(a,lambda,kappa)`, with `lambda` on `profile(a)` having endpoints `f,g`,
and `kappa` on `profile(tau_lambda a)` having endpoints `h,k`. An arrow to
`(b,mu,nu)` is a full source refinement tuple `(u_i):a->b` satisfying
`lambda_i=mu_(s_i)` and `kappa_i=nu_(s_i)` at all cumulative offsets.
Identity and composition follow from the same offset calculation as (5.1).

There are two actual functors from this domain to
`ChartRef_((hf)^-1,(kg)^-1)(M,W'')`. The successive functor sends an object to
`(tau_kappa(tau_lambda a), (kappa lambda)^-1)` and entry `u_i` to its transport
first by the corresponding sublist of `mu`, then by the sublist of `nu`.
The composite functor sends an object to
`(tau_(kappa lambda)(a), (kappa lambda)^-1)` and each entry through the
componentwise composite sublist. The inverse **composite** chart is retained
in both codomains; we do not attempt to compose differently indexed `L`
functors without this domain bookkeeping. Their endpoint equations,
incidence equations and functor laws follow from (3.1) exactly as in §5.2.

The strict groupoid action law gives equality of these actual functors,
on objects, charts and every entry:

    tau_kappa tau_lambda = tau_(kappa lambda).             (5.5)

For three or more charts the analogous domain retains each successive chart
and imposes its incidence equations. Both parenthesizations have the same
codomain with inverse total chart, and use the componentwise composite arrow
at every boundary and the same transported tuple. Groupoid associativity
and the action law prove equality. Identity charts reduce to the preceding
single-chart functor. This proves precisely the coherence at the strict
level, without an unnamed higher-coherence principle.

Any locally equivariant strict calculus map `H:M->N` maps charted objects by
`(a,lambda)->(H a,lambda)` and tuples entrywise, commuting with (5.2)–(5.5).
Apply this to the actual free-to-presented projection and to the equivariant
semantic factor from §3.3. Thus the local syntax/quotient/semantic squares
commute on every original occurrence. If `H` is an independently proved
calculus isomorphism, so are the corresponding charted comparison functors.

### 5.4 Uncharted specializations and why the chart qualification matters

A global coherent system of interface changes supplies charts for **all**
objects and compatible arrows. For example, a groupoid bisection consists
of a permutation `sigma` of interface objects and arrows
`alpha_A:A->sigma(A)`. Use `alpha_A` whenever an occurrence has label `A`.
This yields a quiver/signature isomorphism and (4.2) on the full uncharted
refinement categories. Bisections compose by
`(beta alpha)_A=beta_(sigma(A)) alpha_A`, so (4.3) is the corresponding group
action. More generally every supplied strict diagram of such choices gives
§2, including arrows between differently labelled interface configurations.
Local charts allow distinct repeated occurrences to use different arrows,
which no single such bisection need realize.

For a fixed occurrence diagram, the groupoid of all assignments of interface
objects and allowed isomorphisms to its incidence classes produces precisely
the local comparisons above. This construction includes independently chosen
internal interface bijections, subject only to actual shared-incidence and
nullary identifications. It is not limited to a simultaneous endpoint name
permutation.

It would be false to erase these choices and claim that ANY two endpoint
isomorphisms give an uncharted refinement equivalence. In the exact relation
model, the whole `Delta_X` has a nullary operation. Transport its two boundary
ends by unequal permutations `f,g:X->X`: the image whole is the graph of
`g f^-1`, not the diagonal when `f!=g`, and has no exact nullary operation.
The nullary frame has just one boundary occurrence, so this is not a legal
local chart. The theorem excludes this *ill-typed supposed action*, not a
valid member of its declared class. On legal charts with `f=g`, the diagonal
and the nullary primitive are preserved.

## 6. Equation invariance is necessary: explicit non-descending control

Use a single component `c` at one interface and three parallel unary
primitives `a,b,z`. Let `C2` act trivially on types, swap `a,b`, and fix `z`.
This satisfies all primitive action laws. Declare only `a(1_c)=z(1_c)`.
Its image is `b(1_c)=z(1_c)`, which is **not** derivable.

To prove non-derivability rather than merely absence from the declared list,
interpret the unary free calculus in the additive monoid of natural numbers:
`a,z` have weight 0, `b` weight 1, identity weight 0, and substitution adds
weights. Every declared instance and every generated congruence step preserves
weight, by induction (equivalently by A3 soundness). The image pair has weights
1 and 0. Therefore it is not congruent. The source quotient identifies `a,z`
but the proposed transport sends them to distinct quotient classes; descent
is not a well-defined function. This is an action on primitive **witnesses**
with fixed endpoints, so the test cannot be passed by checking endpoint names.

Failure of literal stability alone would not suffice for this conclusion:
an image equation could still be derivable. The weight separator supplies the
necessary stronger failure of (2.5). Conversely adding all translates of the
relation makes descent possible, but changes the presented theory by adding
`b=z`; we do not silently perform this saturation.

## 7. Retained transport witnesses versus isomorphism classes

There are two distinct erasures: equational quotienting of operations, already
controlled by A3, and forgetting the actual interface-transport arrows.
They are not interchangeable.

For a strict action of a groupoid `H` on refinement categories `R_x`, form
the transport/refinement category with objects `(x,a)` and arrows

    (g,u):(x,a)->(y,b),  g:x->y,  u:R_g(a)->b in R_y.

Composition and identity are

    (h,v)(g,u) = (hg, v o R_h(u)),       (1,id).            (7.1)

The functor laws (4.3) and associativity in `R` prove its category laws
explicitly. Here both `g` and the full tuple `u` remain arrow data. When
`R_g(a)=a`, `(g,id)` is a retained automorphism; different `g` are different
arrows even if they have the same action on the operation. Taking object
isoclasses forgets these stabilizers. For the trivial `C2` action on a single
fixed identity operation, the retained transport groupoid has two
endomorphisms, whereas its set of isoclasses has just one point and cannot
recover them. Effective action on all other objects does not prevent a
particular object from having a nontrivial stabilizer.

Even a set of operation orbits need not inherit substitution. Take the lawful
one-component scalar calculus whose operation in each arity is an element
of the additive group `Z/3`; identity has value 0 and substitution adds the
outer value and all child values. The automorphism `m->-m` acts in every
arity, preserving all calculus laws. In unary arity, the orbit of 1 is
`{1,2}`. Substituting representatives 1 and 1 gives 2 in the nonzero orbit;
substituting 1 and 2 gives 0 in the zero orbit. Thus independent orbit
representatives do not define a substitution on orbits. A diagonal group
action being compatible with substitution does not make its orbit relation
a congruence under independent substitutions. This control is finite and
does not depend on endpoints.

Retained chart/transport categories avoid both losses. Additional quotient
or descent data may repair an orbit construction, but that is a different
statement (and can impose new equations), not a consequence claimed here.

## 8. Coherent normal sections: exactly what is imported and extended

For arbitrary `E` we have the strict functors of §§4–5; no normal section is
needed. For the C5 graph-cut presentation, the existing independent
`Completion_Comparison.md` supplies `Comp`, its generator/local-relation
construction, and the theorem that pure equation paths with the same
endpoints agree and that mixed arrows are determined by their full
original-slot tuples of normalized entries. Write `Q` for the actual quotient,
`D` for the independent flat-witness calculus, `Phi:Q->D` for its proved
isomorphism, and `N(w)` for the chosen normal raw tree.

An action on the raw primitive data induces `Comp` transport only if it
preserves the **path-relation basis**, not just operation equations. For the
concrete actions in §9 it does: each of the seven rule names is preserved,
each of the 18 labelled critical-join diagrams is sent to the same diagram
at image labels, disjoint/variable squares preserve their addresses, and
MOut/MIn keep every original leaf slot. The preserved monoid multiplication,
category composition and restriction identities identify the changed labels
on both sides. Thus generator-by-generator transport respects all category
relations. This is the existing integration §5.1 argument, now applicable to
every specified action having this checked basis-preservation property.
An arbitrary operation-equation action does not automatically satisfy it,
and no such stronger assertion is used in §§2–5.

Let `nu_t:t->N(ev t)` be the coherent normalization path and let `S` be the
canonical section of `Ref(D)` into `Comp`. For a transport `g`, define

    alpha_(g,w) = nu_(T_g N(w)):
           T_g N(w) -> N(D_g w).                          (8.1)

Evaluation equivariance gives the endpoint. For a full tuple `u:w->w'`, both
routes in the naturality square have exactly the same original-slot
normalized entries. MOut moves the outer equation past insertion, MIn
normalizes the inserted entries, and pure-path coherence identifies the
remaining paths. Hence

    alpha_(g,w') o Comp_g(S u)
          = S(D_g u) o alpha_(g,w).                       (8.2)

Both sides of

    alpha_(hg,w)
       = alpha_(h,D_g w) o Comp_h(alpha_(g,w))             (8.3)

are pure equation paths with the same endpoints, so pure-path coherence
proves equality. `alpha_(1,w)=id` because the chosen normal object is already
normal. Equations (8.2)–(8.3), together with category associativity, prove all
finite-composite coherence. They do not assert that arbitrary chosen raw
normal forms are literally preserved. The same proof works over local charts
when every used equation path and insertion has the specified compatible
incidence chart; §3's local substitution law checks all endpoints.

For the finite bijective example below one may in fact choose the standard
right-comb normal form equivariantly: partitions/order are unchanged, grade
composites transport correctly, and a monoid automorphism preserves whether
a decoration is the identity. Nevertheless (8.1)–(8.3) are the invariant
statement under other normalization choices. They also explain the earlier
source's noninvertible-parameter `d_1` phenomenon without extending D1 into D2.

## 9. Concrete finite relation-interface action and full invariance check

### 9.1 Uniform concrete family, including the selected finite action

Let interfaces be finite sets with allowed bijections. A component from `A`
to `B` is an actual relation `R subset A x B`, with its two interfaces
retained. For `f:A->A'` and `g:B->B'` define

    R^(f,g) = { (f(a),g(b)) : (a,b) in R },
    R^(f,g)(a',b') iff R(f^-1(a'),g^-1(b')).               (9.1)

Identity and composite transport laws follow by applying the functions (or
inverses) to each ordered pair. This is the component bifunctor of §3.

Relational composition is left-to-right: `(R;S)(a,c)` means there is `b`
with `R(a,b)` and `S(b,c)`. For bijections `f,g,h`,

    R^(f,g) ; S^(g,h) = (R;S)^(f,h).                     (9.2)

The forward witness map is `b' -> g^-1(b')`; its inverse is `b -> g(b)`.
They are inverse on realizing tuples, not merely an implication between
existence predicates. For a full path, apply the same coordinate map at each
internal boundary occurrence; composite changes compose coordinatewise.
For the empty path,

    Delta_A^(f,f)=Delta_A',                               (9.3)

because `f` is injective and surjective. Empty finite carriers cause no
exception: all these maps and assertions remain valid. These are exactly
the bijective special cases of the independently supplied C2 model.

Consequently C2's containment and exact operation fibres both transport by
mapping their full profile and whole. Inclusions and equalities are preserved
and reflected. Substitution commutes because the whole and each concatenated
profile component are the same on both routes, with validity from (9.2)–(9.3).
Thinness identifies only the validity proof, not primitive labels or
realizing tuples. This is a semantic model; it is not used as the definition
of the free/presented equality.

For the selected finite instance take three distinct interface labels
`A,B,C`, each with carrier `Fin 3`, and the group `(S3)^3` of independent
carrier permutations. Its relation quiver has all 512 relations in each of
its nine ordered hom sets. Its strict action maps relation **entries**, not
just interface names. Keeping the labels fixed is already a nontrivial typed
action. The category of finite relations on these three objects is a finite
category `K`, with associative composition and diagonals. The same formulas
also allow interface label permutations, different equally sized carriers,
and independent occurrence charts when desired.

### 9.2 Reuse of the actual C5 signature and seven equations

Fix any finite graph bound `N` and finite commutative monoid `M`. Use the
existing C5 signature `S(N,K,M)` unchanged: components are `(G,R:A->B)`,
binary primitive cuts have an actual ordered graph partition and individual
grade relations `R,S` with output `R;S`, nullaries `u_A` occur at
`(empty,Delta_A)`, and unary decorations are `d_m^W`. In transport leave the
whole graph, its edges, ordered subsets and their canonical restriction maps
unchanged; use (9.1) on every grade. Decorations keep `m`. More generally a
specified monoid automorphism `chi` may act by `m->chi(m)`; these actions can
be combined with the interface action. This supplies actual maps on component
types and every primitive witness before considering the quotient.

A primitive binary cut at boundaries `(A,B,C)` is well typed after transport
because (9.2) identifies its new output grade with the composite of the two
new input grades. Nullaries use (9.3). Unary decorations keep their whole and
input consistently transported. The resulting label maps obey identity and
composition as functions. They are the arbitrary-local signature action of
§3 and, for a global permutation family, the strict signature action of §2.

The finite declared template families are mapped as follows. This table checks
literal stability of their **actual typed labelled instances**, not just the
untyped shapes.

| Family | Equation and image-label check |
|---|---|
| R | `c(c(x,y),z)=c(x,c(y,z))`. Both sides retain the same ordered three graph blocks and grade string. Every intermediate grade is the corresponding subpath composite. Applying (9.2) to that subpath gives exactly the image intermediate grade; relational associativity makes the outer grades equal. Graph restriction/union labels are unchanged. Thus the image pair is the R instance at the image triple. |
| UL | `c(u,x)=x`. The empty/id graph block stays empty; (9.3) transports its diagonal grade to the new diagonal; (9.2) transports its unit-composition label. The image is the typed UL instance, with no external occurrence erased. |
| UR | `c(x,u)=x`. Same calculation at the right boundary, using one shared arrow for the nullary incidence. |
| D0 | `d_1(x)=x`. A monoid automorphism fixes 1, so the image is the D0 instance on the transported whole. |
| DA | `d_m(d_n(x))=d_(mn)(x)`. The image right label is `chi(mn)=chi(m)chi(n)`, exactly the product label of the image left side. |
| DL | `c(d_m(x),y)=d_m(c(x,y))`. The graph cut/grades map as above, and the same `chi(m)` appears at the corresponding input and whole. Thus it is the image DL instance. |
| DR | `c(x,d_m(y))=d_m(c(x,y))`. The identical check at the other, still distinct, occurrence. |

This verifies (2.5) and (3.2) concretely. It also supplies the path-basis check
in §8: critical joins only use these same local templates, category/monoid
identities and the unchanged graph restriction identity, so their two words
are transported to the corresponding two words with identical addresses.
The 18-row table in `Completion_Comparison.md` supplies the actual words;
this argument does not replace it by all semantic equalities.

The existing C5 evaluation `Phi:Q->FlatCut(N,K,M)` is equivariant: on every
primitive the two routes produce precisely the same graph partition, full
grade string and decoration. A2 uniqueness and A3 factorization extend that
equality to every tree and quotient class. Its already proved inverse
therefore is equivariant as well, and §§4–5 give commuting isomorphisms on
full refinement categories. This is a witness-sensitive use of the existing
presentation, not simply an interpretation in thin Rel.

### 9.3 Nontrivial permutations, composite changes, repeated occurrences

For a concrete nonidentity carrier change, let `p=(0 1 2)` on `A`,
`q=(0 1)` on `B`, and let `R={(0,0),(1,2)} subset A x B`.
Then

    R^(p,q) = {(1,1),(2,2)},                              (9.4)

which is unequal to `R` while its interface labels are unchanged. A further
pair `p',q'` sends it to the relation obtained directly with `p'p,q'q`;
this follows entry by entry from (9.1), not from coincident cardinalities.
In a path `A->B->C`, use an independent permutation at `C`; (9.2) cancels
exactly the common `B` coordinate, so different choices at different
interfaces are genuinely exercised.

Take `M=Z/2`, additive notation, and choose an empty-graph whole of diagonal
grade at `A`. Let `a` be its binary flat operation with two repeated input
components `X=(empty,Delta_A)` and value 0. Both tuples of unary children
with decorations

    (0,0)    and    (1,1)                                 (9.5)

give endomorphisms `a->a`: the total value is 0 in each case, and each child
has the singleton unchanged profile. They are different arrows, because the
first (and second) tuple entries have different retained values. A carrier
permutation preserves the diagonal and transports these tuples without
merging their slots or values. The same example can be placed at repeated
nonempty graph components in an existing six-vertex C5 cut; empty graphs
only make the displayed coordinates short. The general proof places no
restriction on graph size or nonempty blocks.

For independent local occurrence maps in the two-slot path `A->A->A`, choose
three possibly different permutations `f_0,f_1,f_2`. The two repeated source
diagonal grades become the graphs of `f_1 f_0^-1` and `f_2 f_1^-1`, possibly
unequal. Their composite is the graph of `f_2 f_0^-1`, as required. The two
source occurrences remain two positions even when source types coincide or
transported types happen to coincide. With one unary child at each slot,
(9.5) transports entrywise; the full arrow remains distinct. This example
exercises actual individual-interface transport, not a global relabeling
applied identically to repeated interface labels.

### 9.4 What the finite certificate does and does not establish

The checked finite sources are `formal/D1FiniteTypedAction.lean` and
`formal/D1OriginalAPIBridge.lean`; their exact reproduction logs, axiom audits
and source hashes are delivered separately. The core source uses an explicit
three-point type and three interface labels, the full family of independent
permutations, relation transport, typed binary witnesses with Boolean
decorations, nullary diagonal units and actual leaf-indexed forests. Its
named transport/equation declarations include `transportRel_comp`,
`Expr.evaluate_transport`, `Expr.transport_graft`, `Expr.derives_transport`,
`Expr.presentedTransport_composite` and `Expr.transportRefinement`. It also
checks distinct replacements at repeated components, a concrete quotient
no-descent control, and a nontrivial unit stabilizer.

Its formal equation is the decorated binary rotation
`k(l(u,v),w) ~ l(u,k(v,w))`. This is a derived C5 equation under the translation
of a decorated binary vertex to `d_k(c(-,-))`: DL/DR move the inner decoration
to the root, DA aggregates it, R reassociates the binary cuts, and
commutativity in `Z/2` identifies the totals. The source map gives this
translation explicitly. It is NOT asserted that this single formal equation
is the complete seven-equation C5 congruence or that every formal fragment
has the full flat-witness normal form. `Expr.Derives` is the contextual
rotation closure; the finite L source does not separately identify it with
the public A3 substitution-stable congruence or formalize its full-profile
parallelism. These distinctions do not enter the generic P descent proof.

The bridge imports the frozen original `RelationInterface` and
`RefinementFunctoriality` APIs. It constructs a genuine finite `Signature`,
a typed assignment into the actual C2 `exactCalc`, and the actual A2
`Tree.extend` strict map. It proves primitive full-profile/output transport,
`Quiver.Path` identity/composition transport and evaluation transport, and
distinct parallel decorated generators. This supplies actual original-API
anchors rather than only a standalone record with matching names. Thin C2
evaluation deliberately forgets decoration labels; their distinctness is
retained in the signature and in the separate P C5 semantics.

This L fragment does not prove the arbitrary-action equivariant universal
property, generic changed-quiver `Calc.Hom`, or the entire refinement-category
comparison. Those are the uniform P results above. Executable tests check
additional seven-template cases at their reported finite domain; they are
not presented as L proofs. Exact build status and the audited declaration
closures must be read from the delivered verification report, not inferred
from an unexecuted source listing. The uniform P result has no bound on
profile length, tree depth, finite interface size or graph bound.

## 10. D1 result and limits

The source-to-obligation map records:

* constructed free action from arbitrary specified type/primitive data;
* exact generated-congruence descent criterion, with concrete seven-family
  invariance and a genuinely non-derivable image relation as negative control;
* strict identity/composition laws, equivariant free and presented universal
  properties, and source/target naturality;
* full occurrence-tuple refinement functors, strict global coherence, and
  local incidence-chart category isomorphisms with explicitly proved coherence;
* actual syntax/quotient/flat-witness comparison and, only where independently
  available, coherent normal-section comparison;
* nontrivial finite carrier permutations, arbitrary local occurrence changes,
  repeated components, and the precise loss from isoclasses/orbits.

The contribution is the explicit integration and witness-sensitive D1 package
at this declared scope, not a new general free-operad or quotient principle.
No arbitrary weak-action strictification, symmetric occurrence permutation,
noninvertible exactness theorem, orbit-descent theorem, or full completion
contract acceptance is inferred.
