# Learned stochastic mechanisms in the existing witness calculus

28 October 2026

## Result and boundary

A learned positive mechanism family can be interpreted in the **actual original occurrence sensitive calculus**, including full histories and continuous latent variables. The needed extension is measurable and probabilistic decoration of its existing graph assignment, not a new decomposition syntax. An explicit separator construction gives actual state and event bijections, and conditional kernel preservation makes local refinement commute with assembly and finite execution. This is a semantic reuse theorem for a learned model. It neither discovers additional mechanisms nor converts the model into finite hardware.

The current `Dynamic.Graph` is generic in `State : Type` and `Event : Type`; finiteness is an operational specialization, not a requirement of that formal core. Its existing proofs do not contain probability, measurability or resource accounting. The written extension below supplies those arguments at a standard Borel, finite profile and stated time horizon scope. It is **not Lean formalized**, not an extension of all finite span equipment restrictions, and not a new identifiability theorem.

Three limits are essential. First, exactness here retains canonical **learned model records**, not empirically identified physical event multiplicities. Second, the probability of a shared source is charged once, even when its value occurs on several ports. Third, a boundary used to match hidden histories is not thereby a runtime sensor.

## Exact source connection

The original archive ``, version 6, is locally available under `contract_revision_20261028/extracted/witnessed_decompositions/`. The focused formalization archive `` is the verified 27 October source checkpoint. Its actual modules are under `dynamic_lean_checkpoint_20261027/staging/Dynamic calculus Lean formalization source checkpoint/overlay/WitnessedDecompositions/Dynamic/`. The integration archive `` contains `theory/Original_Calculus_Dynamic_Interpretation.md`; its written Theorems 1–5 give the underlying set level constructions used here.

The exact public definitions used are:

* `Dynamic.Graph`, `Graph.Hom`, `Graph.IsIso`, and `Graph.pullback`. A map has separate state and event functions commuting with source and target. `Graph.isIso_iff_bijective` tests both functions.
* `Dynamic.Assignment`: the **same** quiver interfaces receive boundary graphs `boundary v`; the same component colors receive graph spans `left c`, `component c`, `right c`.
* `Assignment.Op`, `Op.witness`, `Op.Exact`, `Assignment.calculus`, and `operationEquiv` in `Dynamic/Target.lean`. An operation with original ordered profile p is a boundary preserving graph map W_c → P_D(p), where P is the actual compatible tuple graph. It is not just an endpoint relation or a stochastic matrix.
* `Assignment.GeneratorMaps`, `freeExtend`, `EquationMaps`, `descends_iff`, `freeRefinementFunctor`, and `presentedRefinementFunctor` in `Dynamic/Bridge.lean`. Declared equations must agree on the entire state and event maps.
* Original `Path.Slot`, `Path.expand`, and `SemanticRefinement.Arrow`. An arrow retains a replacement at **each source occurrence**, together with the substitution equation. Equal colors do not identify occurrences or their random draws.

The model is therefore first constructed as an `Assignment`; every grouping below is an `operationEquiv` witness; its refinements are actual original semantic refinement arrows. No automatic interpretation of every historical graph cut generator or equation is claimed.

## Measurable extension of the existing graph target

Equip each state and event set in an assignment with a standard Borel structure. Require source, target and boundary maps to be measurable. A finite compatible tuple carrier is a Borel subset of a finite product: it is cut out by equality in standard Borel boundary spaces, whose diagonals are Borel. The empty profile at v is the actual B_v, not a singleton.

Call an existing operation measurable when both functions of `Op.witness` are measurable. This is a property on an original operation, not replacement notation for it. Measurable operations form a subcalculus of `Assignment.calculus`: identity maps are measurable; substitution is finite coordinatewise composition followed by measurable flattening. For an empty replacement, the retained common boundary value is a measurable boundary map. The original unit and associativity equalities still hold as literal state and event function equalities, hence hold in the subcalculus. The original free and presented APIs apply to this subcalculus and its inclusion into `Assignment.calculus`.

Mark an operation **Borel exact** when its state and event maps are bijections and their inverses are measurable. The explicit coordinate witnesses below have explicit measurable inverses. Thus no measurable selection theorem is being smuggled into an arbitrary set theoretic choice. Borel exactness implies the existing `Op.Exact` after forgetting measurability. Equality only almost surely is not equality in `EquationMaps`; an almost sure quotient would be a different additional construction.

Probability is additional retained data. For a controlled whole graph W, it consists of an initial law or initial kernel, a measurable event kernel Q(de | s,a) supported on source(e)=s, a specified target map and observation map, and the declared admissible input domain. Local open components instead have kernels on **owned random outputs conditional on their permitted input fields and local state**. They need not be row stochastic on all outgoing edges of their graph: edges also contain externally determined boundary transitions. Summing over those external successors would count choices the component does not generate.

Neither an arbitrary graph map nor a support isomorphism is probability preserving by definition. The kernel identities below are separate conditions. The declared model event alphabet may include zero weight records; no event is removed merely because a finite sample did not contain it. If exact positive support is instead used as the event set, it must be certified for the candidate model and measurably specified. Finite observable total variation confidence alone cannot certify that support or true physical event multiplicity.

## Compiling the learned family without a finite state assumption

Use the learner output and exact caveats in `Baseline_Translation.md` and `Baseline_Semantic_Realization.md`. At the source horizon T it supplies local kernels

    p_i^t(dz_i | z_Parents(i)^{<t}, a_Parents(i)^{<t})

and one emission kernel E(dx | z), with conditional independence of current latent coordinates given their parents. Auxiliary values are externally fixed unless their law is separately modeled. This constructs a normalized causal kernel for prescribed auxiliaries; its identification as the physical law under new adaptive interventions is an additional experimental assumption.

Let clock states be 0,…,T and clock events be the steps t−1→t. For each latent coordinate j, form the existing graph G_j:

* its clock t states are histories z_j^{1:t};
* its clock t−1→t event is (z_j^{1:t−1}, z_j^t);
* source drops the new coordinate and target appends it.

For each auxiliary coordinate, use the analogous history graph; at step t its new value is the supplied a^{t−1}. Use an observation graph with one state at each clock and event (t,x^t). Every graph maps to the same clock graph. These are finite disjoint unions of standard Borel products, even when latent and observation alphabets are continuous. The countable disjoint union works if a coherent family for all t is additionally supplied; the learning result at T does **not** identify that extension.

The whole graph is the full compatible product of these coordinate histories and records over the clock, including all declared zero probability records. In particular, when emission noise is zero, x=f(z) is enforced by its Dirac kernel, not by silently changing this event universe. Its canonical event is equivalent to

    e = (t, z^{<t}, a^{<t−1}, a^{t−1}, z^t, x^t).

Its conditional event kernel, given the source history and current auxiliary value, draws each z_i^t once using p_i^t and then draws x^t using E. There are no implicit extra physical noise labels. An implementation may introduce uniforms or other innovation tokens, but these are new modeled records unless already supplied; the learner has not identified their physical multiplicities.

At t=1, all latent histories are empty and the kernel is exactly the learner's product initialization conditional on a^0. It is applied once. If instead one starts at a noninitial window, the law of the retained hidden histories must be supplied jointly and transported jointly. It cannot be replaced by products of local marginals. A general correlated initializer is an allowed extension of this semantics, but not asserted to be an output of the source's product initialization assumption.

### Local state and port meaning

The local stochastic operation of latent mechanism i owns its history z_i^{<t} and the new draw z_i^t. Its kernel reads only the selected latent and auxiliary histories. The emission operation owns x^t and reads the current latent vector; the learned global decoder need not decompose into local sensors. An auxiliary driver owns the externally supplied auxiliary history update; it contributes a Dirac kernel at that supplied input, not a fresh random input at every receiving mechanism.

A graph scope that mentions coordinate j includes its source and target histories as well as its event record, because graph maps must preserve both endpoints. Thus a component may structurally carry the next value of a borrowed parent even though its kernel is prohibited from using that future value. This is a **matching field**, not information available before generation. Causal typing is retained by specifying separately which projection a local kernel may read. Using the poststep field to choose an earlier command is forbidden.

## An explicit original planar signature for arbitrary influence graphs

Choose an order of the learned local kernels, auxiliary driver factors, and the emission factor. There are n factor occurrences. Each coordinate graph has one name, and each random variable has exactly one generating occurrence. Record which coordinate graphs each factor mentions. A shared source or history keeps the same name wherever reused.

For coordinate j, let first(j) and last(j) be its first and last mentions. Pass its **same** coordinate record through every intervening position. Write

    B_k = product over the clock of G_j with first(j) ≤ k < last(j),

and let the kth bag contain its mentioned coordinates together with the coordinates in B_{k−1} and B_k. Empty products retain the clock. The local component W_k is the full bag product graph, using the same declared event convention as the whole. For example, when emission noise is zero, the emitter uses the Dirac kernel at f(z); zero probability off graph emission records remain in both the whole and the bag graphs. No independent copies of z are invented. Unmentioned but recorded external coordinates are given an explicit driver occurrence, so every coordinate is covered.

Take quiver vertices v_0,…,v_n, assigning B_k to v_k. For each interval i<j introduce the color c_ij:v_i→v_j. Its W_ij is the coordinate product over the union of bags in that interval, with boundary projections to B_i and B_j. For each i<k<j, introduce one generator

    g_ikj : c_ij → (c_ik,c_kj).

Its witness restricts the same state or event assignment to the two subintervals. The intersection of their coordinate scopes is exactly B_k. Consequently these restrictions give an actual Borel graph isomorphism

    w_ikj : W_ij ≅ W_ik ×_{B_k} W_kj.                 (1)

**Proof of (1).** A global assignment restricts to a matching pair. Conversely, matching assignments agree on every shared coordinate because each coordinate occupies an uninterrupted interval of bags. Their union is therefore uniquely defined and restricts back to the pair. Restriction and union are finite coordinate maps and hence measurable on their Borel carriers. The source and target maps commute with them coordinatewise. This proves state and event bijectivity, not only equality of supports or counts. ∎

Every arbitrary directed influence graph is represented by these through records; no symmetric operad or crossing primitive has silently been added to the original planar syntax. The price can be large separator interfaces. Changing the factor order is not a free source equality: it requires an explicitly named profile comparison and transported coordinate maps.

Declare only the ordinary parallel grouping equations for these interval splits. Their two maps agree on every state and event because both return the same ordered coordinate restrictions. Thus `EquationMaps` holds, and the original `presentedExtend` applies. The operation family is not declared to contain all possible semantic maps as generators. Original `Path.Slot` and `Path.expand` retain all ordered leaf occurrences and all copies of a repeated color. The interval signature deliberately distinguishes its positions; equal learned kernel parameters may be reused without identifying those occurrences. In more general well typed profiles the original API also permits literal repeated colors. Across time, a kernel template is reused with the continuing history state and owned draw address (occurrence,time), not a reset state or a reused random token. Only explicitly declared source aliases share a draw.

Spatial nullaries are treated literally. At interface v_k the unit component is W=B_k with both legs identity, and its empty profile witness is id_Bk, hence Borel exact. A nonunit loop component has a nullary operation only if its two boundary maps agree; exactness then requires that common map to be a graph isomorphism. A stochastic mechanism with hidden random output cannot be deleted as a nullary unit merely because its output is unobserved.

## Assembly and refinement theorem

The following is the useful extension beyond merely invoking `freeExtend`.

**Hypotheses.** Fix the compiled assignment, its causal factor ownership and its initial kernel at the stated horizon. For every selected local refinement at every source occurrence require:

1. An original boundary preserving witness r_c:W_c→P(q_c) that is a Borel graph isomorphism. It preserves the external labels, clock and phase, and the identities of all shared source/history records.
2. A specified local acyclic conditional kernel program for the replacing components, whose order replaces the parent node in the original causal program. It reads only context already available to that parent and preceding child outputs. Thus the combined expanded program remains acyclic. Each newly drawn variable has one owner; borrowed input fields are aliases. Its interface input dependence respects the original timing. No two occurrences silently receive the same random token, and no shared token silently becomes two independent tokens.
3. For **every** admissible local source state s and causally available input context u, the **joint owned output** kernel κ_child(· | s,u) equals (r_owned(s,u,·))_*κ_parent(· | s,u). Here r_owned is a specified measurable bijection of the owned output fibres, and the graph witness r_c extends it to completed records by the identity on borrowed event fields. Neither r_owned nor either local kernel may read a borrowed successor field that is not yet available. Boundary output aliases must be preserved. This is equality before averaging in a fitted environment, and equal individual output marginals do not suffice.
4. The state maps transport the complete initial joint law, including any noninitial hidden history coupling. All occurrence refinements and boundary maps use one coherent naming and state identification through time.

More explicitly, write a completed parent event as (s,u,y,b), where y is its owned output vector and b consists of externally owned completion fields. Item 3 requires the record map to have the form (s,u,y,b) ↦ (r_state(s), u, r_owned(s,u,y), b), with the declared typed rearrangement and boundary aliases. It does **not** define a predictive law by conditioning on b: downstream b can be correlated with y, and is generated later by the whole program. Its later distribution is preserved by substitution of the equal owned output kernel. This factorization of r_c is an extra check, not a property of every Borel exact graph map.

The program in item 2 is part of the mathematical semantics; it is not an assertion that a distributed physical device has the same input access. An extra hidden random variable in the child program usually violates item 1 unless it is uniquely recoverable from the parent record or the parent record universe is explicitly enlarged. An equality obtained only after marginalizing that variable is not exact refinement in the existing calculus.

**Theorem.** Under these hypotheses:

A. Assembling the original local kernels and then applying the substituted witness gives the same state and event graph map and the same conditional probability kernel as refining locally first and assembling the refined kernels. The resulting witness is Borel exact. This holds for every original finite occurrence refinement forest satisfying the hypotheses, including exact nullary units and repeated colors.

B. For every finite execution length that remains within the declared time horizon, the corresponding map on executions is a Borel bijection. It commutes with truncation and concatenation and transports the full execution law, not only a one step output law. The initial law is inserted once, not at every tree node or time step.

C. If boundary and component types are simultaneously reexpressed by compatible Borel isomorphisms, the owned versus borrowed output fibres and their causal availability are preserved or explicitly transported, and all kernels, observations, initialization and causal input labels are transported along them, refinement before retyping and retyping before refinement agree. The corresponding positive execution laws agree under those coordinate maps. No resource gain or loss follows from the reexpression alone. An arbitrary global latent diffeomorphism need not induce componentwise isomorphisms on this particular signature; then part C is inapplicable to that fixed signature, not a proof that the gauge transformed whole model is physically invalid.

**Proof of A.** On state and event sets, the original substitution first applies the outer witness, then the occurrence indexed local witnesses, and flattens the result. Its inverse uses each inverse witness and joins the parent coordinates; the preserved boundary records make this well defined. Both routes return the same coordinate indexed by the same complete occurrence address. This includes empty branches because their inverses reconstruct their component from the retained common boundary value.

For probability, independently define assembly by the acyclic program: generate each owned stochastic variable once from its stated conditional kernel, reuse its value at all aliases, and execute deterministic record assembly. Its normalization follows by eliminating generated variables in reverse causal order; each conditional kernel integrates to one. In the learned one step family this is simply the conditional product of all p_i followed by E. It is **not** the product of the marginal measures on W_k, which may count common histories several times.

Replacing one local program by its child program preserves the conditional joint measure on its owned outputs under the specified bijection, by hypothesis 3. Its graph map fixes borrowed fields and merely transports the owned output aliases. Integrating that kernel identity against the upstream context law and the transported downstream kernels therefore preserves the completed whole event measure, even when the later borrowed fields depend on the earlier owned outputs. A topological induction over the finite refinement forest proves the statement for all occurrences. Finite product kernel integration and deterministic pushforward are measurable; no conditioning on equality of independent continuous draws is used. The equality test on events in the graph construction synchronizes aliases of one draw, rather than trying to condition unrelated draws on a probability zero diagonal. This proves normalized kernel preservation in addition to the graph isomorphism. ∎

**Proof of B.** The underlying comparison is the original time versus occurrence transpose: a path of matching tuples is the same array as matching component paths. Its inverse is the opposite transpose, and both are measurable coordinate maps on finite products. Truncation and concatenation affect only the time index; refinement affects the occurrence index. Initial transport and the one step conditional kernel identity prove the equality of finite path cylinder measures by induction on the number of transitions. These cylinder sets generate the Borel sigma algebra of the finite execution space. If a coherent infinite kernel family is separately supplied, the same identities determine its path law; this is not an inference from equivalence at T. ∎

**Proof of C.** Let φ_c:W_c→W'_c and h_v:B_v→B'_v be the specified compatible isomorphisms. Their coordinatewise action gives a Borel isomorphism Φ_p:P_D(p)→P_D'(p), including Φ_empty=h_v. Define w'=Φ_p w φ_c^{-1}. Tuple flattening commutes pointwise with Φ, giving exactly the claimed substitution square. Pushforward of the complete kernels and initial law gives the same probability square. The observation and causal label transports are indispensable parts of the hypothesis. ∎

This result is a conditional local verification and reuse result. It does not prove that an arbitrary learned factorization possesses any given refinement, that a new decomposition search is complete, or that the refinements are physically realizable.

## Two probability and record failures caught by the theorem

**Shared source ownership.** Let C be a fair bit and, conditionally on C, let X=C xor N_1 and Y=C xor N_2, with independent noises having P(N_i=1)=1/4. The joint law of X,Y is strictly positive and P(X=Y)=5/8. The complete model record is (C,N_1,N_2). C is generated once; its two appearances are aliases. Replacing C by independent C_1,C_2 gives P(X=Y)=1/2. Even retaining equality C_1=C_2 but multiplying two joint local factors P(C,N_1)P(C,N_2) leaves total mass 1/2: the prior of C was paid twice. Correct assembly owns P(C) once and multiplies the two conditional noise factors. Exact support gluing alone detects neither mass error.

**Extra hidden refinement record.** A parent Bernoulli output with two event records is behaviorally reproduced by a child drawing a four valued uniform token and reporting its parity. The forgetting map has two preimages per parent record. No state and event isomorphism of the original event universes exists, although observed laws agree. Expanding rational probabilities into uniform multiplicity tokens is therefore not an automatic exact witness refinement. One must explicitly enlarge and account for the parent event universe, or accept a nonexact map and a different claim.

Both examples remain relevant when support graphs are full. With positive Gaussian noise, the same support graph can represent very different transition densities or different decoders. Forgetting the kernels loses the learned mechanism information.

## Boundary change is not free equipment structure

The existing structural equipment `GraphSpanModel.md` uses finite sets and finite spans, retains a graph partition and one monoid scalar, and has cells whose coefficient maps run from compatible input span witnesses to the output. The dynamic operation above runs from a whole graph to its pieces. On Borel exact witnesses the inverse gives an assembly map on records; this does not give an interpretation of every original structural graph partition, scalar or nonexact equipment cell. A single global scalar is also not a stochastic transition kernel.

The structural equipment's cartesian restriction retains triples (a',e,b') satisfying endpoint equations. It has no normalized law on the new fibre. The existing dynamic integration already proves the precise comparison for independent endpoint restriction:

    π_p:P_B'(p;W') → B'_a ×_{B_a} P_B(p;W) ×_{B_b} B'_b.

An exact old witness has an exact transported witness retaining its data only when this comparison is a graph isomorphism; in the present extension its inverse must also be measurable. For a nonempty profile its fibres are products of internal boundary lift fibres. For an empty profile it is the diagonal B'→B'×_B B', not a vacuous product. These restrictions therefore need not preserve exactness even at the set level.

Kernel transport asks a further question. Missing lifts discard mass; multiple lifts need a conditional distribution; selecting a set theoretic section does not determine the correct law. Coarsening may create new compatible tuples and can destroy the Markov property after hidden state is marginalized. The companion `Typed_Realization_Bridge.md` supplies the explicit normalized lift and persistent intertwining obstructions and their restricted repairs. No all map stochastic equipment theorem is claimed here. Isomorphic retyping in part C is the safe unconditional class proved in this note.

## Physical access and finite realization remain separate

For a physical claim, every intended controller or device operation must be compiled using the permitted preaction observations, memory, communication and actuators. A hidden history field used to prove (1) is not a sensor; a physical coupling in the environment is not automatically a robot communication channel. In particular the global learned emission f does not provide its inverse on noisy observations.

A simple necessary obstruction is implementer indistinguishability. If two reachable modeled situations induce the same permitted local observation and initialized memory, any deterministic local implementation must choose the same command in them; a randomized one must choose the same command distribution. A proposed refinement requiring different commands has no such implementation, despite a valid hidden state witness. With stateful reuse, the same memory update and command tables must work at every visit and every compatible context. The companion causal uniformity analysis states that persistent condition; the graph witness alone does not supply it.

The history construction keeps the continuous learner's exact law but generally uses unbounded history, continuous values and potentially wide separator records. To recover the finite operational class one needs a separately proved finite sufficient memory quotient, finite alphabets or a quantitative abstraction theorem. Naively discretizing continuous latent coordinates changes the statistical model and does not inherit the source identifiability hypotheses. A finite rational special case can use the same construction with rational conditional weights and finite tables, but is not thereby an instance of the smooth continuous identifiability theorem. Rationality is unnecessary for the mathematical weighted graph bridge and only assists exact finite arithmetic.

The separator signature is compact as a symbolic dependency description; enumerating its joint state and event tables may be exponential in separator width and memory. No hidden polynomial discovery claim is made. Given explicit finite local tables and proposed Borel exact maps specialized to finite sets, the checks reduce to bijectivity, boundary equalities and conditional probability identities in those actual tables. Their successful check transports the result through arbitrary authorized finite refinement trees without reenumerating each complete trajectory. The relevant table sizes and separators must be charged.

## A growing interacting family in a matched learning class

The construction is not restricted to the two bit diagnostic. For every m≥3 and T≥2, take independent unit Gaussian initialization and, at t≥2, the cyclic mechanisms

    Z_i^t | z^{t−1} ~ N((z_i^{t−1})² + (z_{i−1}^{t−1})³, 1),

where indices are modulo m and the current coordinates are conditionally independent. Set the t=1 means to zero explicitly; no hidden z^0 or revealing reset is assumed. Let observations be X^t=MZ^t+ε^t, with M an unknown dense invertible matrix and independent Gaussian noise of a known positive variance. Auxiliary variables may be absent, or an independent dummy auxiliary with no children can be included. These are dynamically interacting, genuinely hidden, positive models. No stability or stationary law is asserted.

This is a concrete S22 conditional theorem class, not merely a generic claim of applicability. Its sufficient statistic is s_i(z)=z, so k=1 and the statistic is a diffeomorphism. Writing λ for its vector of means, at history ±e_j,

    λ(±e_j)=e_j ± e_{j+1}.

These vectors span R^m; selecting a basis among them, together with zero history, supplies the required variability points. The two derivative matrices at ±e_j have entries ±2 at (j,j) and 3 at (j+1,j), and no others. Their sums and differences isolate every diagonal and every ring edge matrix unit. Thus their 2m-dimensional span is exactly the permitted graph matrix space. Finally Pa(i)={i,i−1} and Ch(i)={i,i+1}, whose intersection is {i} for m≥3. The graphical complete-disentanglement criterion is satisfied. The auxiliary influence condition is vacuous when every auxiliary child set is empty.

Consequently, **conditional on the source's exact observational-fit and sparsity premises**, S22 Theorem 5 identifies this family up to its stated permutation and coordinate transformations. That is the baseline's discovery achievement, not a theorem established here about optimization from finite data. The nonparametric v2 temporal sufficient-influence condition still fails in this first-order, no-effective-auxiliary setting; this example therefore also illustrates why the two published results must not be merged into a claimed uniformly stronger theorem.

Applying the separator construction to any admissible learned representative yields the original state/event witnesses and probability-preserving grouping refinements. The m transition factors use local parent histories, while the dense observation factor reads all current latents. That emission can force a width-m separator in this linearization. The bridge therefore does not conceal a compact physical sensor decomposition or claim separator width remains bounded. The displayed transition family has a continuous finite-dimensional Markov realization, but that is not a finite alphabet or finite precision realization.

The rank and graph assertions have the explicit proof above; bounded exact rational regression checks also verify the mean and derivative ranks for 3≤m≤12. This is a growing positive **semantic integration** family. No new physical port inference, sample complexity improvement, or architecture-search result is obtained from it.

## Comparison and remaining theorem residue

The normalization and substitution of stochastic kernels are established probability mechanisms, not new mathematics. [Fritz's Markov category treatment](https://arxiv.org/abs/1908.07021) already treats conditional products and stochastic processes abstractly. Typed hierarchical dynamical assembly is likewise an established construction, including [Vagner, Spivak and Lerman](https://arxiv.org/abs/1408.1598), and [Lerman's maps of open system networks](https://arxiv.org/abs/1705.04814). The learned positive conditional product law is already supplied by [Lachapelle et al. 2022](https://proceedings.mlr.press/v177/lachapelle22a/lachapelle22a.pdf) and the separately scoped [2026 version 2](https://arxiv.org/abs/2401.04890v2); it is not supplied for the first time by this bridge.

What this note adds to the project is an explicit **comparison construction**: the learner's actual family is assigned to the original quiver and `Dynamic.Assignment`; separator restrictions are actual `operationEquiv` maps; full conditional record laws, phase, initialization and occurrence identities are retained; and the resulting local to global theorem states exactly which probability and physical claims do not follow. This closes a semantic notation gap and supplies a reusable conditional checking rule. It is not evidence of a new theorem beyond the combined standard Markov, wiring and original dynamic calculus mechanisms, nor a proof of the unknown physical decomposition discovery target.

A substantive remaining result must infer or verify **one physically implementable, resource bounded, persistent witness family** from the learner's observable evidence, without replacing hidden observations by full state access, without a supplied true port alignment, and with a proved finite data or approximation guarantee. Establishing that extra capability on a growing interacting family is still open. No contract status changes.

## Verification status

The existing Lean APIs and the integration proof were inspected; no new Lean theorem or Lean rerun is claimed. The arguments above are written proofs. An independent sibling audit reviewed the statement and its probability ownership conditions, identified two substantive draft ambiguities about zero weight event universes and borrowed successor fields, and checked their repair. This is internal AI review, not external human certification. `check_calculus_bridge.py` is a bounded rational regression for separator bijections, probability ownership and a nontrivial weighted refinement; its output is `Calculus_Bridge_Checks.json`. It passed 220 scope families, 1,926 state and 1,926 event split bijections, 97,294 joined tuples and 1,024 four step paths, including the shared source and duplicated prior negative controls. It also verified the growing ring mean and derivative ranks for 3≤m≤12. It is not a proof of the standard Borel theorem or a physical experiment.
