# I2: minimal compositional observable realizations of typed graph witnesses

31 October 2026. **Paper theorem manuscript for independent audit; not a kernel-checked formalization or whole-contract closure.** Scoped execution gate: `framing.md` §7 and `framing_audit.md`. References to I5 below mean the delivered `i5_repair_delivery_20261031/source/` package, not unpinned later author files.

## Human-readable abstract

An observation may answer every currently visible question yet fail after placing its subject inside a larger construction and then cutting that construction apart. The completed I5 theorem identifies the distinctions that survive all such declared experiments. Here we build the corresponding smallest reachable compositional realization: its typed operations, exact joint cut relation, encoder, original-observation decoder and arbitrary generated-query evaluator. Every competing realization satisfying the same exact-may contract maps uniquely onto it. A proper group quotient gives genuine compression and an actual quotient-label witness calculus; the transformation family forces the full label tuple. A unary additive extension identifies a precise infinite-index obstruction inside one fixed profile. Bounds count label states over fixed old records, not all infinitely many profiles, and the result says nothing about the smallest physical mechanism or access to hidden labels.

### What is imported and what this manuscript adds

The coarsest stable equivalence, full-profile discrete and group endpoints, exact modal characterization and transformation-family state/stabilization counts are **I5 imports**, not new partition theorems here. This manuscript adds the explicitly defined realization category and universal maps, its actual quotient composition and factorization cut structures, semantic and effective decoder contract, finite-index boundaries and finite characteristic-formula certificate. Companion executable evidence tests nonidentity decoding and shared-parent cuts independently of these paper arguments. Ordinary minimal-algebra universal properties are baseline infrastructure; the selected mixed-cut realization/lifting and independently checked construction are essential to the I2 scope.

Pinned I5 sources: `i5_joint_repair_theorem.md` b61d4f46140e7b63356e888f404b5a4a115b3e527dc252957dd3ed4ac0357f0c; `profile_schemata_theorem.md` 09988cb0ecb94df63d0aa6a592e67846c9159e3611f8c16372676c350def2ad1; `repair_calculus.md` 1a7af414bc29cfabf0bb6a65649d3f8c798e64ae27b66e47f8b32527bb642ef2; `monoid_repair_theorem.md` 301f35eb2e9294256b896e56881c1fd636732155f12e75e92fab3d1bfe212001. Their old-calculus hypotheses and relative-presentation dependencies remain in force. No unlocated permission-minimization result is used.

## 1. Fixed doctrine and imported endpoint

Let W be the selected typed graph-linked multicategory, enriched by branch labels as in `model_and_core_comparison.md`. Full profiles remain distinct sorts p. Let X_p be its operations. Fix before minimization: initial readouts o_p, all occurrence-wise graft contexts, the declared frame transport, and the selected old-skeleton-indexed Boolean joint cut relations. Write

    W_c(x) -> Z_c × X_p1 × ... × X_pm

for outputs of actual cut records over x. A record retains ONE simultaneous tuple; For the selected family Z_c={*} is a singleton: the complete old cut skeleton, full factor profiles, ordered occurrence positions and old feasibility guard are already the FIXED cut index c. A serialization of c must retain those data exactly. There is no unspecified hidden evolving record observation. The optional general finite-table statement may carry an explicitly given finite Z_c, but cannot introduce new provenance/readout predicates after minimization. Witness multiplicities and concrete witness identities are not observations.

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

Suppose for each declared old skeleton c, W_c(x) consists of ALL concrete factor tuples over that fixed skeleton whose composition is x (or records with exactly those tuple outputs). Assume old factor operations/skeleton information remains exact under q, as it does for the selected observation. For this assertion Z_c is the fixed singleton structural seed of §1, or any explicitly supplied seed must be the prescribed readout of the tuple; an extra independently constrained seed cannot be discarded. Then

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

Under existence of E*, a reachable eligible realization with finite states at EACH full profile exists iff each index |X_p/E*_p| is finite. Proof: the canonical realization gives sufficiency, and the surjection from every eligible realization onto Q gives necessity. The same statement holds fibrewise over retained old records, with the comparison maps preserving those records. A uniform bound B on states per profile exists iff the supremum of these indices is at most B. A finite TOTAL sorted carrier exists iff the disjoint union of Q_p is finite; infinitely many inhabited external profiles rule this out even if every profile has one state. Profile tags cannot be erased to avoid that conclusion.

For finite P and r<=N, finiteness over a fixed old-record fibre P^r is automatic. It is not a difficult new existence theorem; the substantive effective question is how to construct and certify the smallest representation for all generated probes without assuming the answer or identifying profiles.

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

For a finite group G and proper nontrivial normal J, replace the label monoid by G² and initial observation by first-channel J coset. Then Q is the same OLD calculus decorated instead by the label group (G/J)², on the same framed full profiles, and

    q(alpha,(g_i,h_i)_i)=(alpha,(g_i J,h_i J)_i).

The initial decoder reads the first coset. Substitution is coordinatewise quotient multiplication, typed units are J, and transport swaps cosets. Every quotient fixed-skeleton factorization lifts at EVERY concrete source: choose a representative a_i of each prescribed parent coset and set b_j=a_i^{-1}x_j. The quotient product equation ensures b_j has the required coset simultaneously for all j in group i. Apply independently in the two channels and recursively at actual child sources. This proves exact cuts directly rather than relying only on cardinal counts. Initial first-channel cosets plus transported observation separate every pair of distinct quotient tuples, proving minimality directly as well. The count over alpha is [G:J]^(2r), strictly below |G|^(2r) when r>0.

## 8. Named broader infinite-index boundary

Let branch labels instead be the additive monoid N, retaining the same single-vertex old identity profile and exhaustive unary factorization cuts n=a+b. Observe H0={0}. Define P(n) to mean n≠0. Set F_1=P and

    F_(m+1)(n) := <binary cut>(P,F_m)(n).

Induction gives F_m(n) iff n>=m: a cut with a>=1 and b>=m exists exactly when n>=m+1. Thus n<n' are separated by F_(n+1). All natural labels in ONE fixed unary profile are context-and-cut inequivalent; no finite-state eligible realization at that profile exists. One may use N² with the same first-channel observation and restrict to (n,0), with the identical conclusion. Each binary cut fibre is finite, so the obstruction is infinite observational index, not failure of image-finiteness or a proliferation of external profiles.

The seed zero/nonzero partition is already graft-stable: a unary graft adds a fixed nonnegative constant, so positive inputs remain positive. Thus ordinary graft-only contextual equivalence has exactly two states while the exact mixed theory has infinitely many. The distinction does not rely on introducing infinitely many generators: 1 generates all labels and binary graft/cut syntax is fixed.

### 8.1 Finite capped hierarchy and a failed exact quotient

The companion `index_boundary_theorem.md` proves the following independently declared positive unary family. For t>=2 take M_t={0,...,t} with `u +_t v=min(t,u+v)`, the zero seed and the same grammar. Associativity follows because repeated addition is `min(t,sum)` regardless of parenthesization. For n<t the generated positive-factor test F_m holds iff m<=n; for the top state t it holds for every m. For m<=t use m-1 ones and t-m+1; for m>t use m ones. Hence F_(n+1) separates any n<k<=t, giving exactly t+1 states in every eligible minimum. The identity encoder with capped addition, zero-test decoder and cut relation `min(t,sum_i a_i)=n` realizes this bound. This is a separate finite witness calculus, not a truncated claim about N. All ordered arities and generated depths follow by associativity and the same tree induction.

Indeed the natural truncation `q_t(n)=min(t,n)` is a surjective monoid morphism preserving the seed, but is NOT an exact-may cut quotient of N. The concrete representatives t and t+1 have the same image. The abstract binary tuple (t,1) lifts over t+1, but cannot lift over t: a>=t and b=1 imply a+b>t. Thus their sourcewise image signatures differ. No alternative cut relation on the same q_t can meet exactness at both representatives. This is a sharp boundary between mere algebra congruence and mixed-cut realization.

The capped family requires ceil(log2(t+1)) fixed-width bits for one unary state; its direct operation table has (t+1)^2 entries. A parameterized arithmetic schema can be much shorter than that table without reducing its semantic state count. Testing one proposed m-factor record takes O(m) integer additions/comparisons, while enumerating candidate tuples may require (t+1)^m trials. Numeric bit widths and old tags remain separately charged.

This boundary lies outside the finite witness-palette principal contract input and is explicitly a broader-class counterexample. The substantial positive restricted theorem is the all-N,k finite-palette selected graph-linked class above, including its nontrivial proper group quotients. No strongest possible class is claimed.

## 9. Scope of companion evidence

`encoder_decoder_draft.md` specifies the concrete transformation encoder, separately written normal-form decoder/multiplication interpreter, nonidentity parity codec, source-fixed joint-cut interpreter and actual input/output contract. `verify_encoder_decoder.py` checks the coefficient laws, not a complete implementation of the old graph engine. Effective full-profile operation requires the old record/guard implementation to supply and check actual skeletons; a label grouping alone does not establish old admissibility.

`finite_typed_realization.py` implements the finite CLOSED typed constructor, generated characteristic-predicate DAG certificate evaluator and explicit Boolean/deterministic/polyadic-cut formula interpreter on concrete or quotient states. Its executable deterministic maps are TOTAL; the paper criterion additionally treats partial maps through definedness atoms. No implementation of arbitrary partial maps is claimed. Its cut records are factor tuples with singleton auxiliary Z/named-cut structure; the optional paper variant with arbitrary finite extra Z values is not implemented. Its finite unary M4 test is a closed transition/cut instance, not the whole multicategory. The analytic endpoint constructions and proofs supply all-profile coverage. `index_boundary_theorem.md`, `verify_index_boundary.py` and their results supply the additive/capped boundary. The main proofs do not depend on finite test counts; companion notes and JSON reports specify those counts and ranges without extrapolating them to untested old skeletons.

Independent verifier/auditor results must be read separately from author-side checks. File names containing “draft” do not upgrade paper claims to formal proof or indicate blanket I2 acceptance. The primary-source baseline comparison and final scope audit remain separate artifacts.

## 10. Finite generated-probe certificates without assuming the quotient

Fix the grammar BEFORE running an algorithm. At each sort its atoms are the specified initial observation predicates; constructors are finite Boolean operations (including negation), definedness predicates and pullback along declared elementary graft/transport maps, and the polyadic modality `<c>(phi_1,...,phi_m)` quantifying over ONE joint record. The outer factor and every ordered inner factor occupy their actual positions in this tuple. In the selected family the auxiliary Z readout is a singleton, with the exact structural information retained in c as in §1; this is distinct from the initial H-membership observation. Arbitrary finite interleavings are allowed; no family of all imaginable probes is invoked.

**Theorem 10.1 (effective finite basis certificate).** On a finite explicit closed typed input, the following algorithm computes Q, a finite generated-formula basis defining its blocks, and the encoder/decoder tables. On a certified exact finite schema the same conclusion holds in its declared representation class; all-profile optimality additionally requires the I5 uniformity/realizability certificate, or the direct necessity proofs for the selected endpoint families.

For a claimed algebra quotient, the elementary deterministic table must include the one-hole partial evaluation in EVERY argument slot of each primitive multivariable graft, for every choice of the other concrete arguments. This is a finite expansion on a finite closed system. Testing only one generator action while omitting argument slots proves only the smaller transition-signature result, not an algebra congruence.

Start with the partition by initial readout. For each initial block B retain its atom/finite observation-value conjunction chi_B. At stage j, refine by the old block, every elementary deterministic output block or undefined value, and every complete joint cut signature into current blocks. Retain formulas as follows:

* a deterministic output signature uses a domain predicate and a pullback of the corresponding chi_B;
* a joint tuple `(B_1,...,B_m)` uses `<c>(chi_B1,...,chi_Bm)`;
* a new block's characteristic formula is its old characteristic formula conjoined with the appropriate positive or negative literals for its complete finite signature.

Only tuples occurring in at least one current source signature need be listed: a tuple absent at every source is uniformly false. For nullary tuples distinguish the attainable empty tuple from no records; the corresponding modality has no factor subformulas but is still an existence predicate. All factor slots remain ordered, even when their block names repeat. Formula DAGs may share earlier chi nodes; no small expanded formula-tree bound is implied.

Stop when the partition does not change. Termination uses the finite input state count, not a syntactic depth bound. Each new block is defined by the stated formula, by induction. Every distinguishing split is an allowed experiment, so equal full theories cannot be separated by the algorithm. At termination the partition is S/C/T-stable and refines the input observations; structural induction shows that all generated formulas are constant on every block. These two implications prove that the computed blocks are exactly full-theory equivalence. The final chi_B form a finite characteristic basis and the quotient operations/cuts of §§2–3 are computable from representatives. This is an algorithm from the original tables, not a criterion that presupposes the final answer.

A proposed basis can independently be checked by computing its truth vectors on original input states, checking observation factorization, deterministic definedness/output constancy and complete joint-cut signature constancy. Those checks establish sufficiency for all generated tests. To establish **coarsest** realization, also check that each basis formula is built from the predeclared grammar and compute its concrete truth correctly; then any realization preserving that grammar must retain every truth-vector distinction. A randomly proposed stable finer partition without generated distinguishing predicates does not establish minimum.

This is finite partition-refinement/modal infrastructure already implicit in I5; the certificate makes the actual realization and decoder independently checkable. It is not a new general decidability theorem for unbounded presentations. Logical equivalence is stable in the image-finite setting because a missing matching tuple can be excluded by a finite conjunction: for each candidate competing record choose an offending factor and a distinguishing formula, and conjoin these tests coordinatewise. Infinite record branching can invalidate this finitary argument and is outside the stated semantic criterion unless separately justified.

### Selected all-profile certificate without a profile normalizer

For M_k² the finite scalar splitter and its generated distinguishing predicates can be calculated from the explicit finite monoid table. I5's stagewise coordinate lemma translates each predicate to every actual active coordinate using actual labelled unary identities, the all-input unary cut and transport. Finite conjunctions across the r<=N coordinates distinguish full label tuples. This is an effective recipe given the exact old record and coordinate position, not a finite list of all old profiles. Its validity imports the actual identity schemata and I5 coordinate-necessity proof. Complete old data remain exactly observed.

For C4² the characteristic basis is even smaller: the first-channel parity atoms and their pullbacks through swap determine both parity coordinates at every active occurrence. Their conjunctions define the quotient tuples. The direct shared-parent lifting proof of §7.2 proves the basis cut-stable at every old skeleton. Thus construction and minimality require neither enumerating infinitely many profiles nor assuming that all rank-r sorts support the same arbitrary template set.

## 11. Mandatory mixed-operation and occurrence controls

### 11.1 Observation adequate without contexts but not compositional

Use the declared one-vertex unary slice, with M_k labels, t=k-1 and H={e,b,b²}. Define the diagnostic observation h(A_i)=h(B_i)=h(D_i)=i. Its intended context-free adequacy judgment is equality of ALL cut-only formulas generated from H-membership, with Boolean operations and the exhaustive unary factorization cut. I5 proves that precisely this index partition is the cut-only theory equivalence. It is therefore adequate for the predeclared context-free judgment, not merely for a tautological initial equality test.

But e and b both have index zero, whereas left multiplication by a sends them to a=A_1 and ab=A_t with different indices. Thus this diagnostic observable model has no well-defined left-a graft. The diagnostic h observation is explicit and distinct from the principal H seed: H itself is a multiplication congruence and must not be described as graft-inadequate.

### 11.2 Cut after graft, with neither unmixed language sufficient

Take e and b in the same fixed unary full-profile fibre (or `(e,e)` and `(b,e)` for two channels). Their H observations agree. Since H-membership is a monoid congruence, every graft-only H experiment agrees on them. Since their indices both equal zero and I5 identifies the complete cut-only theory with the index partition, every cut-only H experiment also agrees.

Now graft a above the hole. The results are a and A_t. Let P be the predicate of lying outside H, and let `B=<binary cut>(P,P)`. B(a) is false: a has index one and any product giving a has nonnegative factor indices summing to one, so both cannot be positive. B(A_t) is true: A_t a=A_t and both A_t and a lie outside H. Hence the permitted mixed formula `left_a^*(B)` separates the original states. In two channels the multiplier is `(a,e)` and the same first-channel predicate applies. These are actual unary identity grafts and cuts in the original single-vertex skeleton, not abstract functions invented after the fact.

“Only” here means that neither of the two specified unmixed languages separates this pair, while the displayed cut-after-graft experiment does. It does not claim that this is the only possible separating mixed formula or that no other mixed order could separate it.

### 11.3 Repeated and empty occurrences

Every full profile retains input positions, including equal input colors/operations and arbitrary empty gaps. Composition independence in Lemma 2.1 changes each actual occurrence separately; equality of two factor labels does not merge their positions. A context duplicating a variable is interpreted by inserting the same concrete witness at both positions; compatibility follows by replacing those occurrences one at a time, not by treating duplicated use as one occurrence.

At a grouping with at least two active descendants, the cut equation is `x_j=a_i b_j` with ONE parent a_i for the group. The abstract signature consists of the whole outer factor state and the whole ordered tuple of inner factor states. A checker must enumerate this joint relation, not independently select a possible a_i for each child. If a target requires the same selected hidden factor to be shared across otherwise separate subtrees, that additional equality is not in the declared laminar grammar and needs its own retained record sort/gluing theorem. No such extension is inferred from repeated input colors alone.

Empty input occurrences remain in the exact old skeleton and have no new labels. At rank zero there is one label assignment; over a valid old cut its label solution set contains the empty tuple, whereas an invalid old cut has no record. The distinction is observable and is preserved by the decoder.

### 11.4 Nonidentity decoder and growing states

The group control C4² -> C2² identifies distinct concrete label tuples, yet parity readout, swap, quotient multiplication and whole joint cut signatures are exact. Its decoder outputs original first-channel parity, not a purported inverse recovering discarded C4 labels. §7.2 gives a source-fixed lifting proof for all ranks and all generated trees; the companion checker must test actual original-to-quotient values rather than only internal quotient consistency.

For every k>=4 and each attainable rank r<=N the M_k² family requires `(3k-2)^(2r)` states over the chosen old record in EVERY eligible realization, by the universal surjection and the imported exact endpoint. This gives strict growth with k, and with r when realized in growing graph profiles. It is an I2 realization-size consequence of I5 necessity, not a second proof or new claim of the I5 partition result.

## 12. Quantitative ledger and exact scope of effectiveness

Let n be total concrete states of a genuinely finite closed system, b its initial total number of blocks, L its deterministic-table size AFTER all-slot expansion, and V the total encoded lengths of joint record output tuples. Count at least one unit per record, including a nullary record, and count cut source rows/names separately. Put A=n+L+V+R, where R counts those table headers/source rows and other indexed input entries. Assume n>=1; empty systems are trivial. These are reference/table-entry counts with interned tags, not byte lengths. I5's refinement algorithm takes at most T=n-b+1 sweeps including the final fixed-point test.

**Partition-only bound.** For a suitable sparse/indexed implementation, signature construction and partitioning take O(A) expected hash operations per sweep (or corresponding sorting costs). This bounds neither certificate creation nor the actual Python program as a whole. The supplied Python code scans operation/cut dictionaries at every node and tests partition equality pairwise; a conservative bound for its refinement/construction portion is O(T(n²+nA)) expected indexed/hash operations, excluding input construction and certificate evaluation. This bound includes retaining stage signatures/codebooks; no near-linear Python-runtime claim is made.

**All-slot preprocessing.** For a primitive a-ary total operation with domain sizes d_1,...,d_a and D=product d_i input tuples, expansion creates aD deterministic table entries, since each tuple contributes once to each argument slot. The supplied implementation builds a length-a input tuple for each such entry, so O(a²D) indexed operations is a safe charge, plus reading/validating the original table. Sum these costs over primitives. Degenerate/nullary operations have no one-hole slot but retain their typed constant/unit semantics separately. Costs of providing the original primitive tables are not hidden inside L; large arity and large domains can make this preprocessing expensive.

**Certificate construction/storage.** The program stores stage-class definitions as signatures referring to previous class predicates, not fully expanded Boolean formula trees. With at most n classes per stage and total relevant input size A, O(T n A) reference cells is a conservative bound for the stored signature-DAG definitions and codebook history. A literal generated-formula DAG can be obtained by expressing each exact cut signature as positive/negative joint-tuple modalities over the union of globally attained previous-class tuples for that cut; absent-everywhere tuples are uniformly false. This gives the same conservative O(T n A) bound on predicate/reference cells when tuple slots and connective wires are counted. This certificate-construction charge is SEPARATE from the partition-only bound. Expanding a shared DAG into a formula tree can be much larger and receives no polynomial-size claim.

**Independent certificate evaluation.** The supplied memoized evaluator may check up to O(T n²) (concrete node, stage, candidate-class) triples. At one such triple it can scan previous classes for every factor occurrence in relevant original cut records; O(nA) indexed work is a conservative charge. Thus O(T n³ A) expected indexed/hash operations and O(T n²) additional cached Boolean entries safely bound checking all class predicates by this method, in addition to retained model/DAG storage. The evaluator recomputes class membership from original observation and concrete operations/relations; it does not read the queried node's final class as an oracle. These intentionally loose bounds disclose the cost rather than asserting an optimized certificate algorithm.

**Serialization and query evaluation.** A reference-based serialization must pay for every DAG/model/reference cell plus the actual bytes of input tags, observation values and table payloads. With integer references of O(log(T n A+2)) bits, a conservative reference-DAG serialization charge is O(T n A log(T n A+2)) bits, PLUS stored concrete payload bytes and explicit names. No generic serializer with that precise layout is claimed implemented. The ordinary AST query evaluator is recursive and not memoized: its time is bounded by the size of the concrete evaluation search tree, including all cut records and child-formula visits. It can revisit subqueries and may be exponential in formula size/depth. Its runtime is not subsumed by the partition bound. An optimized memoized formula evaluator could instead charge visited (state, subformula) pairs and their relation scans, but is not needed for the stated tests.

All these are abstract indexed/hash-operation and encoding charges, not hardware-time guarantees; hashing/comparing large payloads, integer arithmetic and old-record validation require their own bit costs. Finite-state size, construction, certificate synthesis, independent checking, serialization and query evaluation are distinct resources.

In the selected graph family let m=3k-2 and p=m². Per exact old record of active rank r:

| Model | Concrete label states | Minimum label states | Honest coding interpretation |
|---|---:|---:|---|
| M_k², first-channel H seed plus mixed probes | m^(2r) | m^(2r) | fixed-length injective codes need at least ceil(2r log2 m) bits; per-coordinate normal-form coding uses 2r ceil(log2 m) bits |
| C4², first-channel parity plus swap | 16^r | 4^r | exactly 2r parity bits suffice for the quotient labels |

These omit full profile/old-record tags, whose input size can grow through empty positions and unary grade paths even when N,k are fixed. Reading, validating and writing those exact tags is part of any implementation's cost. A symbolic tuple schema avoids explicitly tabulating all p^r states but does not reduce their semantic number.

I5 gives the selected uniform combined-elementary refinement upper bound `max(2,ceil(log2(k-2)))+4` when every required labelled unary multiplier is an elementary context. The generator-only alternative in both channels adds one round under its stated convention. Its cut-only unary hierarchy has exact strict-round count `max(2,ceil(log2(k-2)))`; it is an algorithm-specific elementary signature hierarchy, not a lower bound on all algorithms or growing alternation of fully saturated S/C/T repairs. These statements are imported with their exact conventions.

Unbounded arities and depth are covered by the actual local grammar, occurrencewise congruence and source-fixed tree induction. Finite control does not bound terms, full profiles, old witnesses, or the whole sorted carrier. No generic all-profile normalizer is asserted. The positive all-profile constructions work because their explicit encoders are already determined and the imported/direct local necessity arguments establish optimality at every actual record.

## 13. Contract map, comparison obligation and assurance boundary

Original I2 lines 638–653 are addressed as follows: finite-index criterion (§6 and the same-profile boundary §8); effective finite generated-basis criterion (§10); actual quotient construction (§§2–3 and 7); minimality/unique intertwining maps (§5); decoder (§4 and companion implementation); full profiles and unbounded syntax (§§1–3, 6, 10–12); sharp state bounds (§12); all five mandated tests (§11). The wider finite-index obstruction is explicitly outside the finite palette principal input and does not weaken the positive theorem.

Ordinary Myhill–Nerode/tree-automata theory provides the standard context-congruence quotient and its minimality. Deterministic graft minimization alone does not capture the declared polyadic factorization modalities: §11.2 separates two states whose pure graft theory agrees. I5 already supplies the relevant mixed modal-equivalence machinery. The I2-specific deliverable is therefore not invoking a familiar theorem's name, but exposing and building the actual same-profile quotient witness algebra, proving equation (F) and source-fixed joint lifting rather than marginal matching, supplying a genuine compressed decoder, and proving that every eligible realization factors through it with exact joint-cut maps. `baseline_comparison.md` supplies the primary-source comparison with Comon et al. (tree Myhill–Nerode/minimal deterministic automata), Hennessy–Milner (image-finite modal/contextual equivalence), Wißmann et al. (coalgebraic quotient algorithms), Turi–Plotkin (mixed algebra/behavior compatibility), and the stated many-sorted graph-algebra reference. Their hypotheses are recorded rather than silently imported into this calculus. No literature-priority assertion is made here.

All proofs here are paper mathematics relative to the pinned old/I5 hypotheses. Finite executable checks are tests of explicit codec and cut laws, not proofs of the infinite family. Independent review must issue separate correctness and original-I2 coverage judgments. This manuscript does not discharge I3 objective incidence, crossing I4, arbitrary physical implementation, unrestricted profile effectiveness, or the full completion contract.
