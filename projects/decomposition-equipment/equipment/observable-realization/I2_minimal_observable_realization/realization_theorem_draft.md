# I2 construction: observable quotient realization and its universal property

Author derivation, 31 October 2026. **Draft for audit, not an I2 discharge claim.** Imports the delivered I5 simultaneous equivalence theorem and its finite-image modal characterization; it does not re-prove that endpoint. References below are to `dependencies/I5/`.

## 1. Fixed doctrine and imported endpoint

Let P be the selected typed graph-linked multicategory, enriched by branch labels as in `model_and_core_comparison.md`. Full profiles remain distinct sorts p. Let X_p be its operations. Fix before minimization: initial readouts o_p, all occurrence-wise graft contexts, the declared frame transport, and the selected old-skeleton-indexed Boolean joint cut relations. Write

    W_c(x) -> Z_c × X_p1 × ... × X_pm

for outputs of actual cut records over x. A record retains ONE simultaneous tuple; Z_c is any declared fixed joint readout. In the principal family the exact old skeleton supplies this structural information and there is no extra hidden evolving record observation. Witness multiplicities and concrete witness identities are not observations.

Import from I5: there exists a coarsest family E* refining initial readout equality and stable for substitution S, selected cut signatures C, and transport T. It equals equality of all finite well-typed Boolean mixed experiments with deterministic pullbacks and existential joint cut modalities. Fixed-skeleton fibres are finite in the selected finite-label family, which is the needed finite-image condition; there may be infinitely many sorts, cut names and generated terms. Existence is NOT being deduced from arbitrary intersections of bisimulations.

## 2. The actual realization

For every full profile p define Q_p=X_p/E*_p and encoder q_p(x)=[x]. Define initial decoder

    d_p([x])=o_p(x).

It is well-defined because E* refines initial observation. Each declared interface transport t induces t_Q([x])=[t(x)], with precisely the same definedness, by T stability.

For an admissible full-profile substitution define

    [a]([b_1],...,[b_n]) := [a(b_1,...,b_n)].

**Lemma 2.1 (composition and units).** This is independent of every representative and makes Q a nonsymmetric multicategory on exactly the original colors and full profiles. Its identity at color A is [id_A], and q is a multicategory morphism.

**Proof.** Changing only the outer argument is an allowed one-hole context with all inner arguments fixed. Changing one inner occurrence is another such context with the other arguments fixed. S stability preserves E* under each change. A finite sequence of changes proves independence for the full tuple, including distinct positions occupied by the same operation. Types ensure all substitutions are defined; for any additional partial admissibility guard, equal definedness must be included in S. Associativity and the two unit laws follow by applying q to the concrete multicategory laws, now that operations are well-defined. Empty and nullary cases use the concrete typed laws, not deletion of positions. Transport's concrete compatibility with substitution descends by q. ∎

For each primitive cut define a relation, not a choice of factor witnesses:

    C^Q_c([x]) = {(z,[u_1],...,[u_m]): (z,u_1,...,u_m)
                                         is output of some w in W_c(x)}.

**Lemma 2.2 (exactness at every representative).** This set is independent of x. More strongly, for EVERY source representative x of a state s,

    C^Q_c(s) = (id_Z × q × ... × q)(out(W_c(x))).                 (E)

**Proof.** Equality of these sets for E*-equivalent sources is precisely C stability. ∎

Thus an abstract cut tuple can be lifted at any chosen concrete SOURCE to a tuple in the designated factor CLASSES, jointly with its declared z. It need not lift to a prescribed concrete endpoint tuple. It neither selects a witness nor preserves witness number, provenance beyond declared Z, isotropy, or unique lifting. In particular, it is not a claim of CULF or endpointwise full lifting.

**Lemma 2.3 (all generated finite cut trees).** Relational composition of these primitive Q cuts equals the class-image of the concrete generated tree-cut relation over every representative of its source.

**Proof.** A concrete tree maps to a Q tree. Conversely, choose any concrete representative x of the Q root. Use (E) at the root to obtain ONE concrete joint tuple realizing its specified Q children. For each nonleaf child, use (E) at the actual representative just obtained, not at a freshly chosen unrelated representative. Induct down the finite tree. The concrete grammar glues these records because child subtrees have no unrecorded cross-sibling constraint. Nullary nodes need no recursive call. This proves simultaneous realization of the entire specified finite tuple. A grammar with crossing cuts, extra shared variables between siblings, or additional record-level tests needs a separate gluing theorem and is not covered. ∎

## 3. When the result is an algebraic cut calculus

Suppose for each declared old skeleton c, W_c(x) consists of ALL concrete factor tuples over that fixed skeleton whose composition is x (or records with exactly those tuple outputs). Assume old factor operations/skeleton information remains exact under q, as it does for the selected observation. For (F), restrict Z_c to the fixed structural readout of c, as in the selected family, or require each z explicitly to be the prescribed readout of the tuple. Extra independently constrained joint seeds cannot be discarded. With that convention,

    C^Q_c(s) = {typed tuples over c, with their prescribed z,
                                      whose Q-composite is s}.  (F)

For primitive cuts, the forward inclusion follows from q preserving composition. For the reverse, select concrete representatives u_i of a tuple on the right. Their concrete composite y satisfies q(y)=s. They are an actual concrete cut of y over c by exhaustive-factorization semantics. Equation (E) transfers their entire class tuple to any x with q(x)=s. Tree cuts follow either by the same argument or Lemma 2.3. The chosen representatives need not themselves compose to x; that is exactly why C completeness is needed in addition to S congruence.

Consequently Q is an actual same-profile compositional witness calculus with its algebraic factorization cut system in the selected exhaustive-cut family. If only selected factorizations are allowed, retain C^Q as a specified relational cut structure on the quotient algebra and do NOT assert (F). If only unary context actions, rather than full substitution compatibility, have been supplied, one has merely an observational transition model until Lemma 2.1's hypotheses are established. Merging profiles would also prevent the stated multicategory conclusion.

## 4. Decoder correctness for the complete language

Interpret initial atoms through d, Boolean connectives literally, deterministic modalities through induced context/transport maps, and a cut modality existentially over the SINGLE relation C^Q_c. Define Dec_phi(s) to be this recursive evaluation.

**Theorem 4.1.** For every finite generated mixed experiment phi and every concrete x,

    Dec_phi(q(x)) = truth_X(phi,x).

Proof is structural induction. Atoms use d; deterministic steps use the intertwining identities; a cut step uses (E) and the induction hypotheses on every component of the same joint tuple. This proof works for arbitrary nesting of grafts and cuts and does not bound syntax depth. It does not assume the decoder is correct merely because an encoder table has the expected size.

Two distinct Q states in one profile are separated by some experiment, by the imported exact theory characterization. Thus Q is fully observable for precisely the declared language. No unrestricted Yoneda probe family is introduced.

## 5. Eligible realizations, minimality, and exact map directions

An eligible reachable encoded realization consists of a same-full-profile multicategory R, declared transports and cut relations, initial readouts d_R, and a profilewise SURJECTIVE encoder e:X->R such that:

1. e preserves substitution and typed identities and intertwines transports and their domains;
2. d_R(e(x))=o(x);
3. for every c and EVERY concrete x, the R cut relation at e(x) equals the image under e of the actual concrete records over x, with declared Z unchanged.

Clause 3 is an exact joint forward/back condition. Merely preserving all forward records or matching separate factor marginals is not sufficient. Reachability means every R state is encoded by some concrete operation; otherwise restrict to an actually closed encoded substructure, and do not count inaccessible junk as part of the minimum.

**Theorem 5.1 (canonical minimal quotient).** For every eligible reachable (R,e) there is a unique surjective profilewise map

    h:R -> Q,             h(e(x))=q(x),             q=h∘e.

It preserves substitution, identities, initial readouts and transport. It is exact for cut relations in the analogous sourcewise class sense:

    C^Q_c(h(r)) = (id_Z × h × ... × h)(C^R_c(r)).

**Proof.** ker(e) refines initial observation equality by clause 2. It is S/T-stable by clause 1. If e(x)=e(y), clause 3 shows equality of their entire cut signatures into ker(e)-classes, because R states are exactly those classes under the surjection. Thus ker(e) is C-stable. Coarseness of E* gives ker(e)⊆E*, so the displayed definition of h is well-defined. Surjectivity and uniqueness follow from surjectivity of q and e. All deterministic preservation follows by substituting representatives. For cuts choose x with e(x)=r and apply clause 3 followed by (E). ∎

In particular Q has no more states in any profile than an eligible reachable realization. This is a behavioral quotient minimum, not a claim of a minimum bit encoding, implementation runtime, or minimum number of generators.

**Corollary 5.2 (uniqueness).** If R is also fully observable for the specified mixed language, h is injective and hence an isomorphism of same-profile algebras, transports, cut relations and readouts. Indeed decoder induction for R gives equality of all R tests whenever h(r)=h(r'); full observability forces r=r'. Conversely Q is fully observable. Equivalently, a reachable realization with no nontrivial eligible behavioral quotient is isomorphic to Q, since Theorem 5.1 supplies such a quotient. In finite profiles, equality of minimal profilewise cardinalities also forces these surjections to be bijections. For infinite carriers, equality of cardinalities alone does NOT establish uniqueness or full observability.

## 6. Finiteness and effectivity: separate criteria

Under existence of E*, a reachable eligible realization with finite states at EACH full profile exists iff each index |X_p/E*_p| is finite. A uniform bound B on states per profile exists iff the supremum of these indices is at most B. A finite TOTAL sorted carrier exists iff the disjoint union of Q_p is finite; infinitely many inhabited external profiles rule this out even if every profile has one state. Profile tags cannot be erased to avoid that conclusion.

A finite reused label carrier over externally supplied exact old records is a different representation notion. It is valid and useful but is not a finite total carrier, nor automatically a bound on full-profile state counts if a profile has many old records. For a profile p in the principal family the exact count is

    |Q_p| = sum over old operations alpha of profile p of |L|^|Act(alpha)|,

with cardinal arithmetic if the old-operation set is infinite. Over ONE fixed old record alpha the label-state count is |L|^r. The old graph bound gives r<=N but does not itself enumerate all profiles or old records.

Finite index is semantic, not an algorithm. Effective realization additionally needs computable encoding/readouts, operations and admissibility guards, and exact computable finite cut tables or certified finite relation schemata. An arbitrary finite-index theory does not provide an algorithm to decide equivalence or discover a bound. The generic I5 finite splitter applies to genuinely closed finite typed systems; its finite-schema version applies only with the full concrete realization and uniformity certificate in `repair_calculus.md` §1. Do not infer that certificate from the mere bound on active coordinates.

## 7. Actual effective selected-family realizations

### 7.1 Principal M_k family

I5 proves E* is equality of the entire label tuple over each already-exact old record, among ALL profilewise partitions. Hence Q is explicitly represented by

    (full profile p; exact old operation alpha; ordered active tuple in (M_k²)^r).

q extracts this data. The decoder reads first-local-channel H membership in each occurrence. Composition multiplies along each active path; identity labels are e; transport swaps the two channels. Over each exact old cut skeleton the abstract cut relation is the finite set of solutions x_j=a_g(j)b_j with ONE parent a_i per group, assembled into whole factor-operation tuples. Thus this is an actual algebra/cut/transport realization, not merely a normal-form decision procedure. It has exactly (3k-2)^(2r) label states over alpha, with r<=N, and a profile-independent finite label representation for each fixed N,k. Old structural data remain explicit external parameters and are not identified.

All operations and cut records are computed from the finite monoid table and actual old skeleton. Arbitrary depth is handled by the proven local syntax and tree-cut inductions. The same q and decoder work at every profile without needing to discover a generic old-profile normalizer. The I5 coordinate necessity theorem proves their minimum even against independently varying profile partitions.

### 7.2 Proper quotient positive family

For a finite group G and proper nontrivial normal J, replace the label monoid by G² and initial observation by first-channel J coset. Then Q is P[(G/J)²], on the same framed full profiles, and

    q(alpha,(g_i,h_i)_i)=(alpha,(g_i J,h_i J)_i).

The initial decoder reads the first coset. Substitution is coordinatewise quotient multiplication, typed units are J, and transport swaps cosets. Every quotient fixed-skeleton factorization lifts at EVERY concrete source: choose a representative a_i of each prescribed parent coset and set b_j=a_i^{-1}x_j. The quotient product equation ensures b_j has the required coset simultaneously for all j in group i. Apply independently in the two channels and recursively at actual child sources. This proves exact cuts directly rather than relying only on cardinal counts. Initial first-channel cosets plus transported observation separate every pair of distinct quotient tuples, proving minimality directly as well. The count over alpha is [G:J]^(2r), strictly below |G|^(2r) when r>0.

## 8. Named broader infinite-index boundary

Let branch labels instead be the additive monoid N, retaining the same single-vertex old identity profile and exhaustive unary factorization cuts n=a+b. Observe H0={0}. This seed is already a multiplication/substitution congruence, since a+b=0 iff a=0 and b=0; cuts, rather than ordinary additive composition alone, force the infinite refinement. Define P(n) to mean n≠0. Set F_1=P and

    F_(m+1)(n) := <binary cut>(P,F_m)(n).

Induction gives F_m(n) iff n>=m: a cut with a>=1 and b>=m exists exactly when n>=m+1. Thus n<n' are separated by F_(n+1). All natural labels in ONE fixed unary profile are context-and-cut inequivalent; no finite-state eligible realization at that profile exists. One may use N² with the same first-channel observation and restrict to (n,0), with the identical conclusion. Each binary cut fibre is finite, so the obstruction is infinite observational index, not failure of image-finiteness or a proliferation of external profiles.

This boundary lies outside the finite witness-palette principal contract input and is explicitly a broader-class counterexample. The substantial positive restricted theorem is the all-N,k finite-palette selected graph-linked class above, including its nontrivial proper group quotients. No strongest possible class is claimed.

## 9. Audit questions and remaining companion obligations

This draft supplies construction, semantic finite-index criterion, factorization/minimality direction, uniqueness hypotheses, decoder proof, principal/group representation and one rigorous broader boundary. It imports I5 state-count and elementary stabilization bounds. A complete selected I2 package still needs an independently implemented decoder test and explicit mixed-context/cut controls, repeated-occurrence checks, quantitative ledger and baseline comparison. The contract's separate test “observations adequate without contexts but not compositional” must define the context-free adequacy judgment before claiming a witness: mere initial-readout equality is tautological adequacy, while cut-only adequacy can be witnessed by the I5 unary C-only index quotient Q, which fails the graft e~b but ae not~ab. This should be stated as a selected cut-only judgment, not silently broadened to all whole observations.

## 10. Finite semantic certificate, not just a minimized table

For a genuinely finite closed typed instance, the elementary combined splitter can output a finite formula certificate alongside each class. Initially choose characteristic formulas for the declared finite observation blocks. Suppose every current block B has a formula chi_B. For each new block, conjoin its old chi_B with the complete finite signature conditions: each generating partial deterministic map contributes either its undefinedness predicate or g*chi_D for its attained block D; for every cut c and every possible declared seed z and tuple of current factor blocks (D_1,...,D_m), include `<c,z>(chi_D1,...,chi_Dm)` if that tuple is attained, and its negation otherwise. Empty and nullary signatures are included literally. There are finitely many conditions because this theorem assumes finite carriers and a finite declared semantic signature. The conjunction is true exactly at the new block, by induction.

At stabilization these characteristic formulas separate every final class; syntactic growth may be large and no polynomial formula-size bound follows. Their modal constructor depth grows by at most one per splitter round when domain/initial tests have depth zero; Boolean conjunctions do not add modal depth. Thus at most n-b strict rounds give a finite-depth certificate for the closed finite system. Its adequacy for unbounded generated expressions comes from the established stability theorem, not from testing only depths up to n-b.

A verifier may evaluate these formulas recursively on the ORIGINAL concrete multiplication, transport and actual joint factor records, using no quotient decoder table, and then check that their truth vectors match the proposed encoder. This gives an independently specified decoder-correctness test; it remains finite evidence, while Theorem 4.1 proves general correctness. Extending this certificate uniformly across infinitely many profiles requires the full schema realization/uniformity proof, not just relabeling table sorts. The selected M_k family instead has its explicit I5 uniform distinguishing proof and local label schemata; the group quotient has direct coset and transported-coset distinguishing formulas.
