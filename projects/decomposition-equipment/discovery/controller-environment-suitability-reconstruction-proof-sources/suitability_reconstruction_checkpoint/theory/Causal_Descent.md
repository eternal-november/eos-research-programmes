# Causal descent through persistent witnessed environments

## Status and plain-language abstract

This note supplies the causal part of the proposed controller–environment reconstruction theorem. It does not claim that solving a partial-observation game is a new mechanism. Its role is to say exactly which game must be reconstructed from the decomposition data, and which information cannot be discarded on the way.

Several partial descriptions may allow different ways of matching their hidden states and events. A possible matching describes one possible environment. That matching must remain the same as the robot runs: the environment is not allowed to silently change its identity after each observation. The robot must choose one physically available action using its actual observations, and that action must work against every still-possible matching. Local controllers cannot each select a different favorable interpretation of the world.

The result below gives an exact finite criterion for this robust suitability problem, conditional on the separate structural theorem producing the complete finite family of consistent world witnesses and their actual event records. It also proves when a change of decomposition leaves the answer unchanged. A separate obstruction shows why independently updating partial beliefs can lose correlations created by observations, even if every proper subset of the state coordinates is retained. Probabilistic claims require additional data; support-level robustness is not a substitute for probabilistic semantics.

## 1. Input and semantic commitments

Let Θ be the finite nonempty set of global reconstruction witnesses derived from the typed chart equations by the structural reconstruction theorem. Elements may be representative labelings rather than isomorphism classes. Retaining duplicates is harmless for universal suitability, provided every possible world is represented. An empty Θ is inconsistent evidence, not a vacuously suitable environment.

A controller assembly κ, including installed drivers and permitted wiring, is existentially chosen once before the unknown environment witness θ. The construction below is for fixed κ. If κ cannot interact with any admitted θ, it fails; that θ must not be removed from the version space to make κ pass. A finite supplied library of κ may be searched, but this is not unrestricted controller-architecture synthesis. Crucially, κ must specify the actual selector/driver memory and schedule as well as its local protocol blocks. Belief sets below are an analyst’s exact representation; they are not automatically storage that the robot possesses. A world witness fixes the matching of components and the transition structure, not a whole future execution: nondeterministic adverse records remain available inside each fixed world.

For each θ let Xθ be its physical state set and Eθ its actual event records. Supplied local controllers have finite memories M1,…,Mk. A state is

    z=(θ,x,m1,…,mk) ∈ Z = ⨿θ Xθ×∏i Mi.

Only configurations permitted by the local typings and gluing equations belong to Z. A designated nonempty initial set Z0 records both physical and controller initialization uncertainty. Unknown physical state and unknown world witness are universally quantified; choosing one favorable θ is not allowed.

The physical interaction interface has a finite move alphabet U and reply alphabet Y. A move is one admissible primitive action or one already compiled causal protocol. It is not an arbitrary function of hidden states or future replies. If a protocol has intermediate choices, those phases must remain explicit in the arena or be compiled into an observation-based contingent plan over precisely its permitted observations. It must not be represented merely by its completed input/output relation. A compiled distributed protocol may branch on a local private input only at a component permitted to receive it, and must meet its actual local memory bound. These private inputs do not become observations of the central selector of U. The theorem presumes that this finite physical protocol compilation has been verified; it does not turn arbitrary distributed synthesis into centralized synthesis.

For z and u the predicate Adm(z,u) asserts all of:

1. u is physically enabled in z;
2. its action projections satisfy every supplied local controller's current demand;
3. its actuator/adapter belongs to the permitted physical interface class;
4. the causal phase at which u is chosen is correct.

Let R(z,u,y,z′) retain actual aligned event records, possibly with parallel witnesses. Its target controller memories are obtained from the actual reply decoders and memory-commit maps, not guessed independently by each chart. Every R edge has the same θ at both endpoints. No silently fresh world matching is permitted. Every admitted nonterminal move has at least one outgoing record at every state at which it is admitted. A nonadmitted move is unavailable, even if a table happens to contain some favorable outgoing edge.

The initial observation map o0:Z0→O and replies y are exactly what the physical robot can observe. Hidden local memories may appear in Z when the robot cannot reconstruct them from its interface; merely naming them as components does not make them observable.

A safety predicate S⊆Z and terminal goal predicate G⊆S express the chosen task. The task semantics here is universal robust success against all actual adverse records and all initially possible θ. Probabilities, costs in expectation, fairness, and almost-sure success are not implicit.

## 2. Exact persistent-witness belief construction

For a public history h=o,u0,y1,…,ut−1,yt define B(h) recursively:

    B(o) = {z∈Z0 : o0(z)=o},
    B(huy) = {z′ : ∃z∈B(h), R(z,u,y,z′)}.

Ignore empty successors as impossible replies. The robot knows its selected moves, so they are part of the history. A move u is available at B exactly when

    ∀z∈B, Adm(z,u).

This is a uniform action condition, not ∀z∃u, and not a condition only on aggregate outgoing records.

### Theorem 1 (all-history realization)

For every public history consistent with available moves, B(h) is exactly the set of final configurations of actual runs with that public history and one fixed initial θ. Consequently a deterministic history-based physical policy obeys all supplied local controllers and safely reaches a declared terminal goal iff its policy on this belief arena does so.

**Proof.** At length zero the assertion is the definition of the initial observation fibre. For the induction step, an actual run extends through precisely an actual record R(z,u,y,z′). Its predecessor lies in B(h) by induction; conversely every predecessor in B(h) has an actual realizing run which can be extended by the displayed record. The same-θ condition on edges retains the initial world witness throughout the extended run. Uniform availability proves that the same selected move implements the local controller demands for all actual runs having this public history. Membership B⊆S or B⊆G is equivalent to the respective predicate holding for all such runs. ∎

This theorem is the place where the separate structural reconstruction must establish that R is complete and sound for actual local records. Supplying an arbitrary list of candidate worlds would not discharge that structural obligation.

### Theorem 2 (unrestricted centralized finite-memory synthesis, not bounded-controller suitability)

Let Q be the finite set of all nonempty subsets of Z; an implementation may construct only those actually reachable from initial observation fibres. Define

    Pre(A) = {B : ∃u [∀z∈B Adm(z,u) and
                         ∀y (B′=Post(B,u,y)≠∅ ⇒ B′∈A)]}.

For infinite safe operation require total admitted moves at every state, or explicitly represent successful termination by an absorbing safe stop self-loop. Under that convention the winning beliefs are the greatest fixed point

    Wsafe = νA. ({B:B⊆S} ∩ Pre(A)).

For safe terminating operation with an explicitly available stop action exactly when B⊆G, set W0={B:B⊆G} and

    Wn+1 = Wn ∪ ({B:B⊆S} ∩ Pre(Wn)).

The union Wreach stabilizes after at most 2^|Z|−1 strict additions of beliefs. If arbitrary additional centralized finite memory over the declared public interface is permitted, a causal finite-state driver exists from all permitted initial observations exactly when every nonempty initial belief belongs to the corresponding winning set. This statement does NOT decide suitability of a fixed or memory-bounded controller κ unless its architecture actually permits the constructed belief-memory selector. A memoryless choice on beliefs gives such a driver; for reachability its fixed-point rank strictly decreases until stopping.

**Proof.** Sufficiency chooses a witnessing move at each winning belief; for reachability choose it from the first rank at which the belief enters. Theorem 1 transfers this to one actual causal driver. Safety necessity follows by the standard greatest-fixed-point exclusion argument: a removed belief either already includes a bad state or every available uniform move has a possible reply leading to an earlier removed belief. Reachability necessity can equivalently use the finite perfect-information belief game; outside the least fixed point the adversary keeps the belief outside it forever or forces safety failure/deadlock. A history-based driver cannot defeat that response. An infinite consistent belief/reply sequence has an actual infinite run with a single θ: its finite realizing runs form a finitely branching tree with a node at every depth, so König’s lemma supplies a branch. Thus the adversary argument does not covertly resample the world at successive prefixes. The explicit stop convention avoids conflating actual unobserved visitation of G with a robot knowing that it may safely terminate. ∎

### Theorem 2a (the actual fixed or bounded controller)

For a supplied physical selector D with finite memory R, output table d:R→U∪{stop}, reply update δ:R×Y→R, and allowed initialization from the initial public observation, form the reachable product Z×R using exactly those tables. The selector is robustly suitable iff:

- every reachable product state is safe;
- whenever d(r)=u, Adm(z,u) holds at every reachable (z,r), and all actual adverse records are retained in the successor product;
- whenever d(r)=stop, z∈G at every reachable (z,r);
- for a terminating task, the reachable product contains no nonstopping directed cycle and no nonstopping deadlock.

For indefinite safe operation omit the final termination condition and require nonblocking at all nonterminal positions. The tables must be physically implementable under κ; a product state is analysis storage, not extra robot memory.

**Proof.** The product graph is exactly the set of runs of this same physical selector against all initially admitted fixed-θ worlds. The first three conditions are exactly universal safety, action compatibility, and correct termination. In a finite graph an infinite nonstopping run exists iff a reachable nonstopping cycle exists; any such cycle stays within one θ because every edge does. Failure of a move or forbidden stopping is a finite counterexample. Conversely absence of these failures and cycles bounds every execution to a correct stop. ∎

For a fixed explicit budget b of selector states, finite move/reply alphabets, and a decidable physical implementation predicate on tables, one can enumerate selectors with at most b states and apply Theorem 2a. Existence among those tables is the exact bounded synthesis criterion. This finite enumeration is not claimed efficient or novel. Shared memory between protocol blocks and selector must satisfy the actual joint resource bound; independent budgets cannot be silently added. Theorem 2 is only an upper-capability comparison: it may show that some more powerful controller could work where the supplied κ cannot.

The powerset construction and fixed points are established game-theoretic infrastructure. The proposed research contribution must be the derivation, invariance, and obstruction theory of this arena from crossing typed decomposition and physically constrained interfaces, not this solver in isolation. No favorable polynomial complexity claim is made. Distributed synthesis with multiple independently observing decision-makers is not silently covered: U here is selected by one controller with one declared physical information interface, albeit with possibly many decomposed internal components.

## 3. Uniform action, witness, and causal quantifiers

The intended statement has the form

    ∃one permitted observation-based driver π
      ∀initial compatible world witnesses θ
      ∀initial physical states
      ∀adverse actual execution records: task succeeds.

With explicit assembly selection the prefix is ∃κ∃π∀θ, not ∀θ∃κ∃π. The following weaker statements are not substitutes:

- ∀θ ∃πθ: each known world is controllable;
- ∀current z ∃u: a full-information action exists;
- ∀reply y ∃adapter: an adapter can be chosen after seeing the outcome;
- ∀time ∃θt: every step has some locally compatible world;
- each chart has its own suitable controller, with no common causal implementation.

A design witness that is genuinely under the implementer's control, such as a fixed installed adapter, is existentially selected before execution. It should be enumerated outside the universally unknown Θ, or represented as a publicly chosen initial move. An unobserved physical matching is not such a design witness. If a controller chooses among adapters during execution, that choice must be part of U and depend only on the public history. These quantifier distinctions survive even when every underlying carrier is finite.

## 4. Exact representation change and causal invariance

Consider two derived arenas with the same physical U,Y and a map p:Z′→Z. Suppose:

- p maps the initial set onto the old initial set and preserves the initial observation;
- S′=p⁻¹S and G′=p⁻¹G;
- Adm′(z′,u) iff Adm(pz′,u);
- for every z′,u,y, the image under p of the fine successor fibre is exactly the coarse successor fibre:

    p[{w′:R′(z′,u,y,w′)}] = {w:R(pz′,u,y,w)}.

The observation interface has not gained hidden component state, and the move u has the same causal ownership and timing on both sides. For a translated interface, first provide a physically realizable uniform action lift and observation translation satisfying these equations; set-theoretic existence of a lift at each hidden state does not suffice.

### Theorem 3 (information-aware exact refinement invariance)

For every common public history h, p(B′(h))=B(h). Thus every policy over the common physical history has exactly the same robust safety and terminating-goal verdict in both arenas. In particular suitability existence over the same permitted physical selector class is equivalent; no new memory or communication is added. Composites of maps satisfying these conditions again satisfy them, so the result is coherent under repeated exact refinements and any commuting diagram of such maps.

**Proof.** Initial observation fibres map onto one another. For each step, image commutes with union over predecessors and the exact successor-fibre equation supplies both inclusions. Uniform admission is preserved because p maps each current belief onto the other, and S/G predicates are pulled back. Policies see the same histories; Theorem 1 and the fixed-selector criterion of Theorem 2a then transfer the verdict; Theorem 2 applies separately only to the explicitly enlarged finite-memory synthesis class. The equations are preserved by ordinary function composition. ∎

This is an alternating-information condition, not mere bijectivity of completed episode records. Suppose b∈{0,1}^n is an adverse challenge and success means a=b. A system revealing b before the controller chooses a is suitable; a system choosing a before b is revealed is not suitable when n≥1. Both can have the same completed pairs (a,b). Forgetting the phase/ownership structure loses the distinction. A record-level graph isomorphism therefore needs an additional phase-preservation proof before it transports suitability.

## 5. Why belief update and crossing reconstruction need not commute

Let K⊆Z be the statically allowed joint configurations derived from the chart reconstruction, and let pi:K→Zi be their actual chart projections, including whatever controller/interface memory each chart is allowed to retain. Their lossless-join closure is

    C(B)=K ∩ ⋂i pi⁻¹(pi(B)).

One always has B⊆C(B); C may introduce correlations excluded by the observation history. A statically exact reconstruction K does not imply C(B(h))=B(h).

### Theorem 4 (exact criterion and explicit failure certificates)

Marginalizing every reachable belief and rejoining over the fixed K preserves exactly the possible current joint configurations iff every reachable B(h) is C-closed. This condition is decidable by exploring the finite persistent-witness belief graph under every uniformly admitted move. A failure has a finite public history h and a tuple z*∈C(B(h))\B(h). For each chart i, a representative zi∈B(h) with pi(zi)=pi(z*) certifies that the impossible tuple passes that chart's marginal test. Each zi is accompanied by its actual run with the same public history; no single run realizes z*.

**Proof.** The equivalence follows from the displayed definition of reconstruction from the marginals. Finite belief exploration reaches every public history up to equal belief and exhausts all future possibilities from such a belief. If closure fails, retain the predecessor chain to h and the finite representatives witnessing each projection membership. Conversely such data prove that marginal reconstruction admitted an impossible current configuration. ∎

This tests preservation of full joint possibility, not the weaker preservation of one selected task verdict. A particular task may tolerate some added tuples. Likewise, local transition updates need their own exactness proof: even if a belief is C-closed, independently projected transition relations may recombine incompatible predecessor records. The necessary extra check is that joining the locally updated marginals equals the actual Post(B,u,y), for every reached B,u,y. A failure certificate has local actual predecessor/record witnesses but no joint actual predecessor record. It is a causal-history version of the earlier actual-witness matching obstruction, rather than a reason to forget witness identities.

### Unbounded-order correlation obstruction

For every n≥2 let θ∈{0,1}^n be an unknown world parameter chosen once. A sensor reports y=θ1⊕…⊕θn. After that reply the true belief is

    By={θ: parity(θ)=y},

with y also stored as public controller memory. At this after-sensor phase take the static reconstruction carrier K to contain all pairs (θ,y); the correlation between θ and the stored reply is imposed by the actual sensor/commit history, not by K in advance. Let the charts retain every proper subset of the θ coordinates together with y. Every proper-coordinate projection of By is the full cube on those coordinates at that y: one missing bit can complete either parity. Therefore C(By) contains all 2^n assignments at y, whereas By has 2^(n−1). Even all proper charts fail to recover the observed correlation. Keeping a bound on chart size cannot solve this uniformly in n.

If the subsequent safe response is a=parity(θ), the actual driver responds a=y and succeeds universally. Rejoining only those marginals invents states with the opposite parity and incorrectly declares that no uniform response is safe. Retaining the shared sensor record or an explicit parity constraint repairs the loss. This family is a structural necessity/control-transfer test, not the practical motivating task or a claim that parity itself is new.

A simpler persistence failure occurs when a sensor reveals a fixed hidden θ and an abstraction forgets the correlation between θ and stored reply before the next action. Resetting the candidate world set then models a different environment that can resample θ. Conversely choosing a favorable θ independently for each local controller makes the problem artificially easier. Neither transformation is justified by static nonemptiness of the reconstruction fibre.

## 6. Probability is additional environment semantics

The theorems above are universal over support. They do not identify stochastic uncertainty with demonic nondeterminism. Two transition kernels with the same nonzero edges can have different success probabilities and expected costs. Even almost-sure eventual success can differ from success on every supported infinite path.

For a fixed physical controller, suppose p:Z′→Z also preserves observations/task labels and the controlled kernels satisfy, for every fine state z′, selected move u, coarse successor z and reply y,

    Σ_{w′:p(w′)=z} P′(w′,y | z′,u) = P(z,y | p(z′),u).

Require matching pushforward initial distributions. Then the induced laws of every finite public/state-label cylinder agree under p for that fixed controller. Induction on cylinder length proves the claim by summing over successor fibres. Consequently measurable events generated by those cylinders, including ordinary reachability and safety events, have equal probabilities. Expected costs transfer when the cost function factors through p and the expectation is defined.

This is a standard kernel/lumping transfer condition, stated to expose the extra proof obligation. A plain record bijection or support-preserving abstraction does not establish it. The current finite robust-suitability solver is not a probabilistic synthesis theorem, and no quantitative guarantee should be attached without actual kernel data and this or an appropriate weaker probabilistic comparison.

## 7. Established baselines and limits

The finite partial-observation game mechanism is standard; see Reif, “The complexity of two-player games of incomplete information” (1984), https://www.sciencedirect.com/science/article/pii/0022000084900345, and Arnold, Vincent and Walukiewicz, “Games for synthesis of controllers with partial observation” (2003), https://www.sciencedirect.com/science/article/pii/S0304397502004425. Architectures with several independently observing agents require separate hypotheses; general distributed synthesis is undecidable, with structured decidable classes studied in https://arxiv.org/abs/1506.03883. These sources are baseline attribution, not evidence for novelty of this note.

Lossless joins, exact abstract interpretation and probabilistic lumping are also standard mechanisms. In particular, structured exact overlapping factored belief tracking is already addressed by Bonet and Geffner, JAIR 2014 (https://bonetblai.github.io/reports/JAIR14-belief-tracking.pdf) and IJCAI 2016 (https://www.ijcai.org/Proceedings/16/Papers/432.pdf). The closure test and parity obstruction here are supporting lemmas, not the headline achievement. The present research burden is to derive Θ, R, causal interfaces and the comparison equations from independently specified typed controller/environment decompositions, and to prove that the resulting arena retains the actual possibilities rather than only each chart's separate feasibility. This note supplies precise targets and proofs for the causal layer; it does not by itself discharge that structural derivation, general distributed control, a full virtual equipment, empirical model validity, or the original research contract.
