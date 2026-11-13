# Exact full profile realization with vertex free cuts

## Corrected realization target

The original proper encoder C4 squared to C2 squared applied uniformly at every active coordinate is not exact for the authorized full-unital language. At the old unary identity, concrete labels (0,0) and (2,0) have the same encoded state but different zero-tree fibres. This manuscript replaces that control by an exact **rank-dependent same-profile quotient of the original enriched calculus**, not by changing the enriched operations or omitting unit cuts.

The corrected model keeps exact group labels on operations with one active input, keeps quotient-group labels on operations with at least two active inputs, and has no labels on operations with no active inputs. It genuinely compresses every branching rank. The coefficient-map no-go theorem does not apply because this is not a uniform coefficient map P[D]->P[E]. It is a legitimate quotient multicategory whose state representation depends on the active rank of each full profile.

For the minimality theorem below, take both the old grading category and the old scalar monoid to be terminal. This is an explicit substantial subclass of the original graph-linked family, with arbitrary graph bound N, all its full profiles, unbounded empty positions and unary depth, and a finite witness palette that may vary. No nonidentity old grade arrow is silently assumed invertible. The quotient construction and cut exactness themselves work over the same nonerasing geometry with more general old grades; the claimed minimality needs the terminal-grade and terminal-old-scalar identity-retraction argument, or that retraction property separately proved.

## Algebra and predeclared observations

Let G be a finite group and let pi:G->K be a surjective group homomorphism. Put D=G squared and H=K squared, and write pi2:D->H. The concrete calculus is the unchanged P[D] with every old record exactly observed. Its frame transport swaps the two channels. Fix before minimization the initial readout of the first-channel pi-value at every ordered active input, all occurrencewise graft contexts, all actual old-skeleton factorization cuts including vertex-free identities, and channel swap. Boolean mixed experiments are generated from this fixed language.

For a fixed exact old operation alpha of active rank r define

    Q(alpha) = singleton,       r=0;
               D,              r=1;
               H^r,            r>=2.

The encoder e_alpha is the unique map when r=0, the identity on D when r=1, and coordinatewise pi2 when r>=2. Full profiles and alpha are never identified. The initial decoder reads the first component of pi2(d) at rank one, and the first K-coordinate of each H label at higher rank. At rank zero its list is empty. Swap acts literally on either representation.

## Quotient composition and actual units

An outer operation of active rank m has one active child operation of rank r_i>=1 at each of its nonempty input occurrences. Empty inputs remain ordered and carry only their old data. Nonerasure gives

    r = r_1+...+r_m.

Consequently r=1 forces m=1 and r_1=1. In that case both factor labels are exact D-elements and Q composition is their group product. When r>=2, apply pi2 to any exact rank-one factor labels and multiply in H along each path; factor labels already in H need no conversion. Rank-zero operations have no label multiplication. This rule is independent of representatives because pi2 is a homomorphism. It is precisely the operation induced by e on concrete composition.

Changing one actual factor occurrence at a time therefore leaves the encoded composite unchanged. Concrete associativity and unit laws descend. The nonempty-color identity is the exact rank-one element 1_D, not a quotient class containing other elements. Empty-color identities retain their unique old coefficient-free value. Swap commutes with this composition and preserves every full profile. Thus Q is a same-color nonsymmetric multicategory, not merely a transition model.

This also proves the nonerasing rank monotonicity needed here: a branching operation cannot be turned into a one-active-input operation by any allowed graft context. Deleting designated empty occurrences is allowed; deleting a nonempty branch is not.

## Joint source fixed cut exactness

For a fixed old two-level cut, write x_ij for the concrete final source coefficients, a_i for outer coefficients and b_ij for child coefficients. Every equation is

    x_ij = a_i b_ij,

with one shared a_i for all descendants j in group i. Let a prescribed Q-factor tuple compose to e(x). We construct a concrete lift at this very x.

If the source has rank zero, there are no coefficient choices. If it has rank one, outer and active child ranks are one, so their Q labels are exact D-elements; the quotient composition equation is the literal equation x=a b. Use these factors unchanged.

Now suppose r>=2.

* If outer rank m=1, its Q label a is an exact D-element. The child has rank r>=2, with prescribed H-labels B_j. Set b_j=a^{-1}x_j. Its image is B_j by the Q composition equation. The outer factor remains exactly a.

* If outer rank m>=2, its prescribed labels are A_i in H. For a child of rank r_i=1, its Q label b_i is exact in D. Set a_i=x_i b_i^{-1}. The Q composition equation gives pi2(a_i)=A_i, and the exact child b_i is retained.

* For a child of rank r_i>=2, choose any a_i in (pi2)^{-1}(A_i), then set b_ij=a_i^{-1}x_ij for every j. These child labels have their prescribed images B_ij. One parent a_i works for the whole group. Different i are different outer input occurrences, so no separate-child selection is being passed off as a shared-parent lift.

Empty/nullary groups carry no labels and keep the actual old data. This proves exact lifting of the whole joint tuple, not merely factor marginals.

For a vertex-free cut the old source is an actual unary identity and has active rank one (or is the coefficient-free empty identity). Its Q label is exact, so Q identity feasibility holds exactly when the concrete source is the actual identity. The unique empty record lifts and no new unary vertex is inserted.

Induct over an arbitrary finite target tree: first lift its root cut as above, then lift each target child subtree at the actual concrete representative just obtained. The vertex-free case just proved is the induction base whenever a unit child occurs. Every intermediate factor is retained. This gives, for every full cut index c and every concrete x,

    C_Q(c,e(x)) = e_out(out(W_c(x))).                           (E)

Here e_out acts at the actual full profile of each factor; the exact old cut index and ordered positions are unchanged. This variable-rank encoding is essential. Replacing e_out by one uniform coefficient quotient would reintroduce the obstruction.

Define C_Q by the right side. It is independent of x by this proof. Because concrete cuts are exhaustive factorization tuples over the fixed old skeleton, C_Q is also exactly the set of Q-tuples whose Q-composite is the source. For the reverse inclusion, choose concrete representatives of the factor states, compose to y, and use (E) to transfer the entire factor-state tuple from y to any x with e(x)=e(y). The zero-factor tuple uses y=id and the separately proved unit case. This is the algebraic cut-calculus assertion, not preservation of witness multiplicity or unique endpoint lifts.

## Minimality for the predeclared full language

First, encoded-equal concrete sources have the same complete mixed theory. Atoms factor through the decoder, deterministic operations and swap factor through the quotient algebra, and cuts satisfy (E), including the empty tuple. Structural induction on generated formulas proves

    Dec_phi(e(x)) = truth_P[D](phi,x)

for every finite mixed experiment phi, without a depth bound.

Conversely, suppose two sources lie over the same exact old record.

At r>=2, a difference in encoded H^r labels differs in some channel and some actual ordered coordinate. The corresponding initial first-channel pi-readout separates it, or does so after swap for the second channel. Hence every different encoded state is distinguishable.

At r=1, the terminal old grading and terminal old scalar hypotheses matter. The unique nonempty input is the whole output graph; all other inputs are empty. Graft the designated empty nullary into each empty occurrence. This produces the actual old unary identity with the same concrete D-label. Given distinct labels d and d', follow this context by multiplication by d^{-1}, then ask whether the vertex-free identity cut exists. It exists for d and not for d'. This is an allowed graft followed by the literal unit cut, not an extra observation invented after minimization. It proves exact labels are necessary at rank one even when their quotient values agree.

Rank zero has only one label assignment. Exact old data were observed throughout. The encoder kernel is therefore exactly full mixed-theory equivalence on this terminal-grade, terminal-old-scalar subclass. There is no all-profile discreteness claim: compression at every r>=2 is the proved positive result.

Every reachable eligible same-profile realization R preserving the same initial readouts, deterministic operations and source-fixed joint cuts has a unique surjection

    u:R -> Q,              u(e_R(x))=e(x).

It is well-defined because e_R(x)=e_R(y) forces equal truth of all generated formulas, hence e(x)=e(y). It intertwines composition, units, transport, initial decoder and exact cut relations by the same source-fixed equalities. Surjectivity follows from reachability. If R has no extra observational distinctions, u is an isomorphism. This is the original I2 minimality direction, now applied to an actually stable full-unital equivalence.

## Independent decoder target and quantitative consequences

The decoder is not an inverse reconstructing hidden G labels. For rank one it outputs the original first-channel quotient readout from exact D. For higher rank it reads the corresponding K-values directly. Its recursive mixed-query evaluator uses the actual quotient composition and joint cut tables. Independent testing must compare each concrete query value with that decoder, including the empty cut record; internal quotient consistency is insufficient.

Let g=|G| and k=|K|. Over one fixed exact old record of rank r, the concrete label count is g^(2r), whereas the minimum full-unital state count is

    1,          r=0;
    g^2,        r=1;
    k^(2r),     r>=2.

For C4->C2 this is 16 states at rank one (not the former four), and 4^r states at every branching rank r>=2. In particular rank two has 256 concrete label assignments and 16 minimal states. A nontrivial lost label at rank two is witnessed by tuples ((0,0),(0,0)) and ((2,0),(0,0)), which encode identically; the exact lifting proof establishes equality of their complete full-unital theories despite their different literal labels.

For a genuinely growing parameterized family take G=C_(2m), K=C_m with m>=2 and any graph bound N>=2. Then the lower bounds above grow with m, and k^(2r) grows with attainable rank. The palette is finite at each parameter value. Arbitrarily many empty input positions and unbounded unary syntax do not change these per-old-record label counts, but their exact old tags must still be represented and validated. A state-count statement is not a total input-bit or all-profile enumeration bound.

This construction gives an explicit effective schema for every old record: compute its active rank, choose the indicated representation, and apply the formulas above. For a finite closed typed input the original finite generated-formula refinement algorithm remains valid after unit cuts are included as zero-factor relations: an attained empty tuple and no records have different signatures. The original complexity qualifications remain; this manuscript does not improve that algorithm's cost bounds.

## A separate positive seed with nontrivial old interfaces

There is also a full-profile positive control over nonterminal old grading, for example the path category with objects 0,1,2 and arrows 0->1->2. Keep old operation data exact and permit the declared old transports preserving ordered active/empty occurrence status, together with channel swap. The old scalar may likewise remain any exactly retained admissible old scalar. State the initial seed differently and explicitly:

* At active rank zero, retain its unique label assignment.
* At active rank one, initially observe the entire exact D-label, in both channels.
* At active rank at least two, initially observe the first-channel K-value at every active occurrence.

This is a strengthened positive-control observation, not the original first-channel parity seed. Under it the same encoder e and quotient Q are minimal without an old identity-retraction argument. Initial rank-one observation already forces exact D-labels; initial observation and swap force both quotient channels at every higher rank. The quotient stability and source-fixed all-tree proof above supplies the matching upper bound. Thus the transport-saturated seed is exactly Q and is already stable under substitution and all full-unital cuts. A single saturated transport repair produces the simultaneous optimum; this is a statement about saturated repair operators, not a claim about every elementary implementation's sweep count.

For any additional coefficient interface map, well-definedness on Q must be checked on its exact-rank-one and quotient-rank-higher representations, along with the actual old occurrence maps. In particular group maps whose quotient squares commute descend in the expected rank-preserving cases. No noninvertible old geometric map is declared cut-reflecting merely because Q is stable; source-fixed old-geometry lifting remains its own obligation. The example with nontrivial old grading and channel swap supplies a mixed-interface positive class without pretending that opaque old grade arrows can be reversed.

## Interface and refinement limitations

The quotient map preserves every concrete refinement tuple and actual cut record in the sourcewise relational sense above. It does not preserve literal factor identities, multiplicities, unique lifts, or arbitrary proof provenance. It is not the I1 uniformly coefficient-labelled map h, and must not be substituted into that theorem's injectivity claims.

The full refinement category on Q can be formed from its well-defined same-profile composition. The original I1 faithful presentation-to-semantic refinement comparison remains a theorem about the original literal coefficient presentations, and is not re-proved or strengthened by this observational quotient. A new finite presentation for Q would require its own presentation theorem; none is needed for the explicit semantic quotient and effective schema claimed here.

The original I2 mixed-only separation and context-free adequacy tests involving e and b in the M family do not survive unchanged: a vertex-free identity test already separates that pair. The replacements use b and b squared and the exact 2k-block cut-only quotient R_k. They are proved in the companion 06_replacement_I2_mixed_tests.md and in ../theory/Full_Unital_I5_Observation_Repair.txt, Sections 3 and 5. This manuscript supplies the actual quotient construction, genuine compressed decoder, minimality and growing size control; those companion proofs supply the remaining mixed-test obligations. Final acceptance is still a separate review judgment, not inferred from finite enumeration.
