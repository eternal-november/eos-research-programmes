# C2 independent mathematical proof and depth review

Date: 2026-10-24. Reviewer: `/root/review_relational_model_target`.
This is a separate post-proof review, not the completed pre-attempt review.
The reviewer did not write or edit the proof or model implementation.
Assurance is agent-managed non-author mathematical review; common-model
correlation remains a limitation. No external human certification is claimed.

## Verdict and exact inputs

**Mathematical correctness: PASS for the uniform local C2 model.**

**Scientific-scope verdict: PASS for the authorized local infrastructure
milestone; NOT full C2 acceptance or a standalone major research contribution.**

Inputs:

- Contract v0.1: `47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
- Cleared target: `b6711190a46b19205ef25f439105eaf1951137d90f5e55a595ea67daf172e2f4`.
- Reviewed proof `proof/C2_Model_Theorem.md`:
  `15fcef7404272567dd957cb8f2b7a83ba40761034b589745a215adc233d315df`.

The report is hash-bound; a material later proof change needs delta review.
Companion `C2_P_Theorem_Review_Inputs.json` records the inspected public A source
hashes and the named certificate comparator. This review supplies P assurance,
not an optional L axiom audit or the independently checked exhaustive C suite.
Those separate reviews and parent acceptance remain necessary for the local
checkpoint. Full C2 remains **OPEN** because its later D2/E use is not performed.

## Actual argument reconstructed

### 1. Model universe and relational substitution

The model uses every relation between every pair in an arbitrary family of
finite carriers, including empty carriers and an empty label set. Components
retain both labels and their relation. It does not replace distinct labels
with equal cardinalities or treat two relation occurrences as one.

R1's unit and associativity arguments expand the defining existential
conditions and rearrange exactly the same intermediate values. R2's induction
on the second path gives concatenation, including the empty-path unit. In R3,
the interval endpoints of each child path provide the outer realizing tuple;
conversely the finitely many child tuples concatenate. An empty child forces
its two adjoining values to coincide. Repeated zero-length offsets therefore
do not introduce arbitrary extra values. An empty outer path is the same
diagonal on both sides. Finite existential elimination, not a hidden infinite
choice principle or inhabitance assumption, suffices.

This proves validity of substitution BEFORE thinness is used. The proof then
uses equality of the entire expanded typed profile and unchanged output,
followed by the singleton-fibre property, to establish equality of operations.
This is legitimate for this explicitly thin semantic model. It is not a
tautological quotient of syntax and is not an inference from equality of
composite relations alone. `Path.expand_assoc` and its occurrence transports
give precisely the profile equality the public operation law requires.

### 2. Exactness and zero arity

The containment and equality fibres are genuinely different definitions.
Equality validity is closed under the same substitution because every inner
inclusion and the outer inclusion is equality. Forgetting equality therefore
gives the stated strict structure-preserving injective map of fibres. Properness
is exhibited, not asserted for all-empty degeneracies.

The identity of a component has one input occurrence. A nullary operation
instead has the empty loop profile and requires diagonal contained in its
whole, with equality only for the exact nullary. These conditions apply even
when the carrier is empty. Nullaries with unequal labels are excluded by
typing, not by a carrier-cardinality test.

### 3. Restriction maps, direction and exactness boundaries

The membership-level pullback `R(f(a'),g(b'))` is explicit. Its iteration order
is correct: restricting first along `(f,g)` and then `(f',g')` gives restriction
along `(f∘f',g∘g')`. Equality is pointwise, so identity and composite-change
coherence do not assume arbitrary chosen comparison isomorphisms.

For positive arity the realizer map sends each primed internal coordinate
through its actual boundary function. It proves **composite of restrictions
included in restriction of composite**, not the reverse. The map of tuple sets
need not be injective or surjective; equality of the endpoint relations does
not imply either. Surjectivity of every internal map supplies the reverse
inclusion for positive arity. No endpoint injectivity, endpoint surjectivity,
or nonemptiness is used. No necessity converse is smuggled into the statement.

For zero arity the target of the comparison is the kernel relation of the
single endpoint map. Equality with the primed diagonal is exactly injectivity,
including the empty-domain case. This separately proved case prevents the
false vacuous-surjectivity inference. Arbitrary restriction still takes a
containment cell to a containment cell by composing the comparison inclusion
with the pullback of its original validity proof.

### 4. Restriction and tree substitution

Section 5.1 defines the component and path maps of a fixed global map family,
then proves preservation of identities and substitutions in the common target
fibre. This does not require equality in the lax relation-composition
comparison. It correctly distinguishes a base-changing map from the public
fixed-quiver `Calc.Hom`.

Section 5.2 states the needed incidence equivalence relation on the whole
substitution diagram. A nullary child identifies its two boundary vertices,
so the primed object, label and function must agree there. Under that condition
each child's restricted whole is literally its parent's restricted component.
Both routes then give the same ordered restricted frontier and restricted
root whole. Induction extends the argument to every finite tree. The proof
does not quietly claim an all-arity exact action for arbitrary functions.

As an adversarial reconstruction, take a one-point old carrier and its diagonal
`D`, a constant map from a two-point primed carrier, and `K=Res(D)`, the full
two-by-two relation. An exact binary source with components `D,D` admits an
exact nullary first child and identity second child. After restriction the
nullary child becomes nonexact, since the two-point diagonal is properly
contained in `K`. Nevertheless both restriction/substitution routes have
profile `[K]` and whole `K`, since `K;K=K` and `Delta;K=K`. This explicitly tests
the distinction used by the theorem rather than assuming exactness survives.

### 5. Public A correspondence and free interpretation

The reviewer inspected the actual public `Core`, `Collections`, `Calculus`,
`PathOccurrences` and `FreeExtension` source declarations. The proof's named
maps exist: `Component`, `Path.Slot`, `expandFamily`, `expand_assoc`,
`fiberTotalizeEquiv`, `totalizeFiberEquiv`, `Calc.Operation`, `Calc.Hom`,
`onOperation`, `Signature.Assignment`, and the free `extend`/`homEquiv` maps.

The profile sequence to dependent path conversion and its inverse are
constructor inductions, preserving intermediate labels. Fibre totalization
and recovery explicitly transport validity along profile equality. Their
inverse laws reduce to equality elimination and proof irrelevance; neither
selects an arbitrary representative. The `CalcData` fields use relational
validity proved by R3, and the `Calc` laws use the existing ordered profile
identities. Exact-to-containment is same-base; restriction is deliberately not.

The admissible primitive assignment uses the FULL output component `S.result`
and ordered input path. The free extension is the actual A2 unique strict
morphism into this constructed calculus, not merely an untyped recursive fold.
Thinness explains why parallel primitive labels or grouped trees can have the
same semantic image without making their raw syntax equal. The proof does not
erase the output relation or introduce a semantic-kernel quotient.

## Named examples independently reconstructed

Using sets of pairs, without importing author code, the reviewer recomputed
section 7's `R={(0,0),(1,2)}` and `S={(0,0),(2,1)}`. Their composite is the
two-pair diagonal. The larger `W` has the additional pair `(0,1)`. Restriction
through `g=(0,1)` removes the realization through `2` while retaining `(0,0)`.
The onto map `(0,1,2,2)` restores endpoint equality but has two primed realizers
for the pair `(1,1)`. The noninjective nullary example gives four kernel pairs
against two diagonal pairs. Restricting `W` to endpoint subsets `{0}` deletes
its extra pair, demonstrating that nonexactness is not reflected either.
These tables match the inspected named certificate at the companion hash.

The same standalone reconstruction checked the nullary-child calculation
above. This is useful adversarial spot evidence, not a replacement for F1–F6
and not a claim that the reviewer independently reran their entire domain.

## Revisions and reviewer self-correction

Initial submitted proof hash:
`0fa36ed07bb21e89aa05eabb6daf6390d966be7d17ec10dff3e3f563016eeb88`.

The reviewer requested that positive arity one be described as equal by the
unit law, rather than "definitionally" equal under the recursive definition
`C([R])=Delta;R`. The author made that precision correction and supplied the
explicit nonexact-to-exact example. Neither changes the theorem or target.

The reviewer initially overstated an API naming concern. `Signature.output`
DOES exist and is the relation edge; `Signature.result` is that edge together
with its endpoint labels. The original mathematical relation-fibre notation
using `S.output` was valid. The revision now additionally writes the exact
public `Operation (S.result g) (S.input g)` type. This is a useful clarification,
not a repaired missing field or mathematical error. The correction was sent
to both parent and author before this verdict.

No unresolved mathematical defect remains at the reviewed hash.

## Depth, limits and completion boundary

The proof meets T1–T4 uniformly and includes real boundary functions, actual
component relations, arbitrary occurrence-wise substitutions, and a two-sided
public calculus correspondence. It is not a singleton-model certificate or
an extensionality assertion unsupported by relational validity.

Thin operation fibres must not be confused with a thin component or interface
category: different binary relations remain different components and different
functions remain different boundary maps. Conversely, this construction does
not retain primitive witness multiplicity in each semantic fibre. That loss
is explicitly analyzed. It is not an extension of the C1 arbitrary-category
graph model by pretending its nonthin arrows are merely endpoint pairs.

These are familiar relational laws and model infrastructure. The proof
correctly makes no novelty claim, no sharp D2 map-class classification, no
virtual-equipment universal-property claim, and no E exactness/representability
conclusion. The local mathematical depth required for C2 is present; the
broader intended research depth is still contingent on the OPEN D2/E use.
No later obligation is activated or accepted by this report.
