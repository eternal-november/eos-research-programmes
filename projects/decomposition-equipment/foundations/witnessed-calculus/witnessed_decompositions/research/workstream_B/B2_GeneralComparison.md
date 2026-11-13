# B2 — arbitrary semantic tuples and the interpretation comparison

Contract v0.1, SHA256 `47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
P-evidence under the independently cleared B1/B2 target. This report supplies
complete mathematical arguments for the general comparison; the basic category
and functor laws are additionally required in Lean and are not discharged by
this prose alone. B2 is M-positive. B3 quotient/completion coherence, B4 recovery
classification, and C model obligations are not activated or claimed here.

## 1. Arbitrary target, not a special cancellation model

Let M be any accepted path-profile nonsymmetric witness calculus (`Calc`) on
arbitrary I,J. For each whole c, its total operation space M(c) has a profile
p(a), an identity 1_c with singleton profile (c), and occurrence-wise composition

    a[b_i] ∈ M(c),       b_i ∈ M(c_i),  i∈Slots(p(a)).

The profile is the typed ordered concatenation of the profiles p(b_i). The
ordinary two unit laws and associativity are the laws of the input calculus;
no injectivity, cancellativity, faithful evaluation, presentation, normal form,
finite signature, inhabited operation fibre, or nonempty-profile condition is
assumed. A missing/nullary profile contributes an empty occurrence type. Full
component types and intermediate interfaces are retained, not just arities.

Define Ref(M,c) as follows. Objects are all operations a∈M(c), whether or not a
belongs to the image of a particular interpretation. An arrow a→a' consists of
one tuple b=(b_i) at the original occurrences of p(a) satisfying a[b]=a'. The
entries' own profiles, their lengths and component types are part of the tuple.
Two arrows are equal iff the entire typed tuples are equal. The endpoint equality
is a proof field and contributes no extra distinguishable data. In particular,
two tuples are NOT equated merely because a[b]=a[d].

The total category is the disjoint union over c. Thus arrows never change the
whole, but the ordered frontier of an object may change arbitrarily according
to a typed tuple. The fixed-output formulation neither collapses interfaces nor
restricts the allowed input profiles.

## 2. Actual tuple composition and all category laws

Given b:a→a' and d:a'→a'', use p(a')=concat_i p(b_i) to identify every occurrence
of p(a') with a unique pair (i,j), j∈Slots(p(b_i)). This is A1's ordered typed
`Path.slotExpand`, followed by equality transport along the endpoint equation.
Put d_{ij} equal to the entry of d at this occurrence. Define the composite tuple

    (b;d)_i = b_i[d_{ij}]_j.                               (2)

This formula is data, not a category axiom. Every d_{ij} has output equal to the
j-th component of p(b_i), by full component preservation of the occurrence
correspondence. Its typing remains valid when a block has zero occurrences.
The target equation is derived:

    a[(b;d)_i] = a[b_i[d_{ij}]] = (a[b_i])[d] = a'[d] = a''.

The middle equality is the input calculus's substitution associativity with
precisely that occurrence correspondence. Thus composition actually returns
an arrow with the advertised endpoint.

The identity at a is the tuple (1_{c_i}) at its original occurrences. Its
endpoint equality is the right unit law in M. To verify category laws, it is
necessary to compare tuple entries, not merely endpoints:

* Compose b with the identity at a'. At original i, formula (2) is b_i with an
  identity at every occurrence of p(b_i); M's right unit law gives b_i. Thus
  the complete tuple is b, proving b;id=b.
* Compose the identity at a with b. Each identity has one occurrence, whose
  component is c_i. A1's singleton occurrence correspondence sends the unique
  nested pair to i. Formula (2) is 1_{c_i}[b_i], equal to b_i by M's left unit
  law. Hence id;b=b, with no assumption that components c_i are distinct.
* For b:a→a', d:a'→a'', e:a''→a''', the two parenthesizations of occurrences
  identify every deepest position with exactly the same triple (i,j,k). This
  is A1's three-layer typed occurrence theorem, including equality transports.
  At original i the two composite entries are

      (b_i[d_{ij}])[e_{ijk}]   and   b_i[d_{ij}[e_{ijk}]].

  They are equal by M's associativity law. Dependent function extensionality
  proves equality of the complete tuples, and proof irrelevance equates their
  endpoint certificates. Therefore (b;d);e=b;(d;e) as actual arrows.

All canonical transports here are equality elimination, not arbitrarily chosen
bijections. Composing transports uses equality transitivity; proof irrelevance
ensures that the same typed equality reached by two derivations does not add
spurious arrow data. The category laws consequently require no stronger
coherence fields on M than the accepted `Calc` laws.

## 3. Every strict calculus morphism induces a refinement functor

Let H:M→N preserve full profiles, identities, and every occurrence substitution.
Define Ref(H,c) on objects by a↦H(a). On an arrow tuple b at a, apply H to each
entry b_i and transport the tuple from p(a) to p(Ha) along H's profile equality.
Its endpoint equation is

    (Ha)[H(b_i)] = H(a[b_i]) = H(a').

Thus the map is defined on every arrow, not just a preferred forest form.
Profile preservation means that nested occurrences have the same i,j labels on
both sides: applying H does not change any entry's profile or its segmentation.
For identity tuples, H(1_{c_i})=1_{c_i} entrywise. For composites, at original i,

    H(b_i[d_{ij}]) = H(b_i)[H(d_{ij})].                     (3)

Together with naturality of the typed occurrence splitting this is literal
composition preservation. Hence Ref(H,c) is an actual functor.

The identity strict map acts as the identity on objects and every tuple entry.
For composable H,K, Ref(K∘H,c) and Ref(K,c)∘Ref(H,c) both send an entry b_i to
K(H(b_i)); their equality transports agree by transitivity of the full-profile
equalities. Thus refinement is itself functorial in strict calculus maps. These
statements are not claims that refinement commutes with arbitrary quotients.

## 4. Identification of the raw source and the free-calculus case

A1 supplies, for every raw tree T, an equivalence

    Family_free(frontier(T)) ≃ Tree.Substitution(T),

preserving actual component-labelled occurrences. Its graft compatibility says
that free-calculus substitution is exactly structural tree graft. Thus a raw
arrow F:T→U yields the semantic-free arrow whose tuple is the inverse image of
F under this equivalence, with the same endpoint equation. Conversely, apply
the equivalence to a semantic-free tuple to recover the raw forest.

The maps are inverse on tuples by the two equivalence laws, and are the identity
on tree objects. They take identity forests to identity tuples. For composition,
B1's leafwise equation says that the entry at original leaf l is F_l with the
second layer read at precisely its descendant leaves. A1's commuting profile/
leaf occurrence correspondence identifies this with formula (2). Hence they
preserve composition, not only endpoints. The result is an actual category
isomorphism Raw(S,c) ≅ Ref(F(S),c).

An assignment of primitive witnesses into an arbitrary M extends by accepted
A2 to a strict calculus map E:F(S)→M. Compose the above isomorphism with Ref(E,c).
This is the raw evaluation functor. Its action on an original leaf's forest
entry is precisely evaluation of that entry; each original position and each
entry's frontier remains recorded. Both unit and composition laws are those
proved above, using A2's genuine substitution preservation rather than only a
recursive evaluator equation.

## 5. What injectivity and tuple liftability actually prove

The following are sufficient conditions, not necessary conditions or a B3
classification. Each is stated in terms of operations or supplied tuple entries,
never by assuming the sought categorical full/faithful conclusion.

### 5.1 Operation and tuple equality reflection

Assume for every relevant component d the function H:M(d)→N(d) is injective.
Then H(a)=H(a') implies a=a' in a fixed whole fibre by that hypothesis. In
particular, for E:F(S)→M, this hypothesis reflects equality of raw presentation
trees, not merely equality of their frontiers.

For fixed a,a' in M(c), suppose two arrows b,d:a→a' have equal Ref(H,c)-images.
Transport their image tuples back along the same profile equality. At each
original i the tuple equality says H(b_i)=H(d_i). Injectivity at component c_i
gives b_i=d_i. Extensionality and proof irrelevance give equality of the arrows.
Thus componentwise operation injectivity is a sufficient reason for hom-set
injection for a general source calculus. No target cancellation is used.

### 5.2 The important raw-source faithfulness caveat

Every functor out of Raw(S,c) is categorically faithful on each fixed hom-set,
with NO hypothesis on evaluation, because B1 proves that each such hom-set is
subsingleton. Any function from a subsingleton is injective. This includes a
semantics discarding every primitive witness and internal grouping.

Therefore categorical faithfulness of raw evaluation says nothing about object
recovery, witness preservation, or lifting missing refinements. It must never
be used as their certificate. In particular, the associative quotient example
can collapse distinct tree objects and have extra semantic arrows even though
its raw-source functor is faithful in this technical categorical sense.

### 5.3 Lifting a particular semantic arrow

Fix a,a'∈M(c) and a semantic arrow b:Ha→Ha'. Assume:

1. H:M(c)→N(c) is injective at this fixed whole c;
2. after the canonical profile transport, a supplied tuple x_i∈M(c_i) lifts
   b entrywise: H(x_i)=b_i, with each x_i in b_i's prescribed profile fibre.

The second hypothesis is about individual operations, not about the desired
arrow endpoint. From preservation and the endpoint of b,

    H(a[x_i]) = (Ha)[H(x_i)] = (Ha)[b_i] = H(a').

Hypothesis 1 now gives a[x_i]=a'. Thus x is an actual arrow a→a' mapping to b.
For the raw source M=F(S), B1 supplies uniqueness of this arrow. For a general
M, entrywise injectivity of H is an additional sufficient condition for
uniqueness; it is not inferred merely from injectivity at whole c.

If each entry individually has a lift rather than a tuple already supplied,
finite dependent choice along the finite ordered profile supplies the tuple.
In ordinary classical set-theoretic P evidence this is legitimate; a Lean
implementation may either expose the supplied tuple explicitly or disclose its
standard choice dependence. An empty profile has the unique empty tuple.
Profile preservation ensures that an equality H(x_i)=b_i already forces the
required profile, but stating it explicitly prevents a false lift by an
operation having only the same output component.

If hypotheses 1 and 2 hold for every arrow between objects in the image of H,
this proves fullness on those objects, and hence reflection of existence of
refinement arrows. Entrywise surjectivity in all the relevant operation fibres
is one independent sufficient condition for 2. In the raw case, bijectivity on
all operation fibres therefore makes the induced functor fully faithful and
object-bijective. More concretely, a strict calculus isomorphism has a strict
inverse; §3 sends both maps to functors, and preservation of identity/composition
of strict maps gives mutually inverse refinement functors.

These conclusions do not follow from raw-source categorical faithfulness alone.
They also do not claim a categorical quotient construction for noninjective E.

## 6. Associative quotient: what fails and what survives

The separate `B2_QuotientCertificate.md` defines a typed binary signature with
all indexed associativity declarations, using the actual accepted A3 generated
congruence and quotient calculus. Its freely retained unary witnesses give an
independent nonconstant statistic. The concrete repeated-loop example has

    L=μ[μ,1],       R=μ[1,μ],       L≠R,       [L]=[R].

The object map therefore fails operation injectivity. In Ref(quotient,c), both
([μ],[1]) and ([1],[μ]) are arrows from [μ] to [L], because the second composite
is [R]=[L]. Their first tuple entries have different profiles (length two versus
one); they are unequal despite equal total composites. Their exact original
occurrence assignments and block lengths are the distinguishing arrow data.

This explains genuine nonthinness: semantic substitution need not be injective
in its tuple argument. In the raw category, by contrast, fixing source μ and
target L leaves only the left-expansion forest. The right-expansion semantic
arrow cannot be its image. Every quotient operation has a raw representative,
so individual tuple entries do lift; it is the fixed-output equality-reflection
hypothesis in §5.3 that fails. Mere surjectivity on operations therefore does
not imply fullness of raw evaluation.

For the no-lift conclusion it is important to use the UNIQUE raw μ→L forest,
not simply observe that one attempted representative tuple has the wrong
endpoint. That uniqueness excludes every possible raw lift, including different
representatives of each quotient entry. The certificate proves this argument
and embeds the phenomenon in a genuine mixed-interface context with repeated
loop positions and four or more leaves.

## 7. A genuinely profile-typed witness-discarding negative control

For any base I,J, define P(c) to contain exactly one operation for each typed
path from c.source to c.target: equivalently its total operations are those
paths themselves and its profile map is the identity. Use the singleton edge
path for identity and typed ordered path expansion for substitution. A1's
path expansion unit/associativity laws prove that this is a lawful calculus.
It is not an untyped singleton: different ordered component paths and their
intermediate interfaces remain different operations.

There is a strict map F(S)→P sending a tree to its frontier. A1 proves preservation
of grafting and identities. This map forgets every primitive witness and every
internal grouping compatible with that frontier. Distinct parallel unary red
and blue corollas therefore have equal image. Its raw refinement functor is
still categorically faithful by §5.2, demonstrating why that property is no
witness-recovery certificate. The control retains profile/occurrence typing
throughout and is explicitly not the nonthin witness-retaining principal model.

## 8. Evidence and mathematical significance

The Lean files construct the actual forest/tuple categories and their functors;
proof dossiers add the unrestricted comparison arguments, and finite checks
are labelled C rather than unrestricted proofs. Independent reviews, theorem
locations, source hashes, axiom closures, failed attempts, and reproduction
commands are retained with the result checkpoint.

These are established free/presented-algebra and category-of-substitutions
constructions with explicit typed occurrence bookkeeping. No novelty is claimed
for making a substitution category or for the associative binary-tree quotient.
B2 contributes the requested precise comparison and its failure boundaries to
this library. It does not discharge the much stronger quotient/completion and
integrated semantics gates in A4/B3/B4/C5.
