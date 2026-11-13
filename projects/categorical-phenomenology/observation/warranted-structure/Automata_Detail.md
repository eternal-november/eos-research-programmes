# A controlled example: observational evidence can warrant a noncommutative group

**Status.** This is a rigorous control example and a proposed way of organizing its interpretation, not a claim of a new automata-learning theorem. The strongest potentially useful conceptual point is that coarse observational classes need not yet carry dynamics: operations may become well-defined only after an observational quotient admits descent. That point is close to coalgebraic final-sequence constructions and classical consistency/closure of automata observation tables. It cannot by itself establish novelty for a general categorical phenomenology.

## 1. What is supplied, what is observed, and what is not supplied

Supply a **finite nonempty intervention alphabet** Σ, the ability to reset a system and execute a finite word of interventions, and an exact binary output measured after the word. Assume stationarity, deterministic responses, and repeatable reset. These are substantive operational assumptions. In particular, concatenation of interventions is supplied; no claim is made that an algebraic signature emerges from literally unstructured data. Reset is an external preparation step, not a letter in Σ. Including a nontrivial reset among the generators would itself destroy the group property, so the claimed structure is explicitly relative to the chosen intervention signature.

An ideal behavior is a function f:Σ*→{0,1}. At stage n distinguish:

- **Available data:** d_n=f restricted to a finite queried set T_n.
- **Currently admissible experiments:** E_n⊆Σ*, with T_n⊆E_n. Membership in E_n does not mean the experiment has been performed or its answer is known.
- **Ideal experiments:** E_∞=Σ*. Their responses define f, but are not thereby accessible to the observer.

A particularly clear access regime is E_n=Σ^{≤b_n}. If b_n is bounded, even an infinite history of repeated experiments need not reveal long-word behavior. If b_n→∞, eventual access to every fixed finite experiment still does not itself provide a finite certificate of all experiments.

For the positive theorem, impose a model promise M_N: the minimal deterministic realization of f has at most N observationally distinguishable reachable states. No state set, transitions, reversibility, group, decomposition, or identification of states is supplied. Nonetheless, finite-state realizability and its known numerical upper bound **are** supplied. A bound inferred only from the same finite table would make the argument circular.

For data d on T define V_N(d)={g∈M_N: g|T=d}. A property P is warranted relative to this promise exactly when V_N(d) is nonempty and every g∈V_N(d) has P. Different promises produce different warrants. Empty completion sets signal model failure rather than warrant every conclusion.

## 2. The canonical structure is recovered from behavior, not a chosen decomposition

For full f, define residual equivalence on histories:

u ~_f v iff f(uz)=f(vz) for every z∈Σ*.

The state object Q_f=Σ*/~_f has the initial state [ε], output o([u])=f(u), and right action [u]·a=[ua]. This is its canonical minimal reachable observable deterministic automaton. Physical hidden states and their internal organization are not identified by this construction.

Define the two-sided observational congruence:

u ≡_f v iff f(xuy)=f(xvy) for every x,y∈Σ*.

The quotient M_f=Σ*/≡_f is the syntactic monoid. It acts faithfully on Q_f on the right, so it is the transition monoid, using the convention “apply the left word, then the right word.” Viewed as a one-object category, M_f is a groupoid exactly when M_f is a group.

This construction has a genuine universal property. An alphabet-generated recognizer consists of a surjective monoid map h:Σ*→R and an output map p:R→{0,1} with f=p∘h. Its kernel is contained in ≡_f, so there is a unique surjective monoid homomorphism R→M_f commuting with the generating map and the output. Thus M_f is terminal among such recognizers. This is standard syntactic-monoid theory, including its categorical generalizations, not a new universal construction.

The target property is now nontrivial and not assumed: **M_f is a noncommutative group.** Within finite-state models this is equivalent to the generated state transformations forming a noncommutative permutation group. Monoid composition comes from supplied sequential interventions; invertibility and noncommutativity do not.

## 3. Finite evidence theorem, with the precise query length

**Theorem 1 (bounded exact identification).** Suppose f∈M_N and the actual data include f(w) for every word |w|≤2N−2. Then f is the unique behavior in V_N(d). Consequently its canonical minimal automaton, syntactic monoid, and whether that monoid is a group, commutative, etc., are completely determined relative to M_N.

**Proof.** Let A and B be complete deterministic binary-output machines with respectively r,s≤N states. Consider their disjoint union of r+s states. Let P_k identify states whose output agrees after every suffix of length at most k. The partition P_0 is by immediate output. P_{k+1} refines P_k by the blocks reached by each letter. Once a refinement step makes no change, all later steps make no change, because its relation already preserves output and all transitions. If the two machines have any inequivalent states, P_0 has at least two blocks. Every strict refinement adds at least one block, and there are at most r+s blocks. Therefore P_{r+s−2} is already the full behavior partition. Two inequivalent initial states have a distinguishing word of length at most r+s−2≤2N−2. Agreement on all tested words therefore implies agreement everywhere. Canonical minimization and the syntactic quotient depend only on behavior. □

The often-used 2N−1 bound is safe but unnecessary here: with terminal binary outputs and the empty word observable, 2N−2 suffices. The bound is sharp even for a unary alphabet: for N≥2, compare an N-cycle accepting only its last state with a one-step tail entering an (N−1)-cycle accepting only its last state. Both first accept at length N−1; their next acceptances are respectively 2N−1 and 2N−2, so they first differ at length 2N−2. Both have exactly N minimal states: within each machine the states have distinct distances 0 through N−1 to their next acceptance. The first transition monoid is C_N; the second is not a group because its transition merges the initial tail state with the last cycle state. Thus this also makes the horizon sharp for certifying the group property in the worst case, not merely for complete behavior identification. This is the Moore-machine/DFA convention. Do not transport the index to a different observation convention without checking it.

This theorem uses no equivalence-query oracle. It requires exact answers to a finite exhaustive collection of membership experiments and a valid state bound. If |Σ|=k≥2, the number of tests in this simple scheme is (k^{2N−1}−1)/(k−1), exponential in N even though the maximum word length is linear. For k=1 it is 2N−1 tests. Existence of a finite certificate does not establish practical feasibility, optimal query complexity, or access to those experiments. If the requisite words are outside E_n, the certificate cannot yet be obtained.

The conclusion is about all behaviors allowed by the declared class, not all conceivable worlds. It says nothing about whether the true hidden mechanism literally consists of those minimal states or about a unique microscopic realization.

## 4. Explicit noncommutative positive example

Let Σ={a,b}. For constructing the example only, take G=S_3, let a represent a transposition s=(12), and b represent a 3-cycle r=(123). Let φ:Σ*→S_3 be the resulting surjective homomorphism, and set f(w)=1 iff φ(w)=e. The learner is not told G, φ, or that any intervention is reversible.

The minimal residual states are exactly the six group elements. Indeed, histories with the same φ-value have the same residual; if φ(u)≠φ(v), append a word representing φ(u)^{-1} to distinguish them. The syntactic monoid is S_3 for the same reason: ker φ=≡_f. Thus the warranted structure is a noncommutative group, not a decomposition.

With the prior promise N=6, exhaustive data through length 10 identify it by Theorem 1 (2,047 binary-alphabet tests). A much smaller, explicitly checkable conformance certificate is possible:

H={ε,a,b,bb,ab,ba}.

These six words represent all six group elements and their inverses also have representatives in H. Query the set T=(H∪HΣ)H. This contains 48 distinct words, all of length at most five; an independent standard-library enumeration verified the count and all stated S_3 transitions and row partitions. The six rows (f(hv))_{v∈H}, for h∈H, are distinct: each row has its unique 1 in the column representing φ(h)^{-1}. Under the promise of at most six states, these six distinguishable reached states exhaust the observable state set. The rows for ha and hb identify the successor among these states, and ε∈H supplies immediate outputs. Therefore the measured table determines the entire transition system.

This is the standard state-cover/characterization-set argument behind finite-state conformance testing, specialized to a fully explicit example. It is not being claimed as a new testing method. One may find the distinct rows adaptively without initially knowing H; H here gives a compact certificate once discovered.

A concrete observation distinguishing the two orders is f(abab)=1 and f(baab)=0. It witnesses that ab and ba are different transformations. Global reversibility requires the full certificate plus the model promise; the short observation alone does not prove a group.

## 5. Indistinguishable irreversible negative examples

**Theorem 2 (no finite group warrant without a complexity restriction).** Let f be the S_3 behavior above. For every finite queried set T, there is a regular deterministic behavior g agreeing with f on T whose syntactic monoid is not a group.

**Proof.** Choose L=max({0}∪{|w|:w∈T}). Define g(w)=f(w) for |w|≤L and g(w)=0 for |w|>L. It is recognized by a finite machine that follows the group together with a step counter up to L and then enters a rejecting absorbing state. Its accepted language is finite and nonempty, because ε is accepted. In its minimal automaton, any word of length greater than L maps every state to the rejecting residual ∅. This transformation is constant, whereas the initial residual is not ∅. Hence it is not bijective, so its syntactic monoid is not a group. □

The construction remains valid even if **all** currently admissible experiments E_n=Σ^{≤L} have been performed. It is therefore not merely a complaint that the observer neglected an available experiment. Access expansion to longer words is needed to distinguish this particular pair. For every new finite horizon another delayed-failure completion exists, so no finite horizon proves group behavior in the class of all finite-state machines with no known bound.

This establishes positive-side non-certifiability at the group example, not that every possible partial table has both a group and non-group completion. Some finite observations can rule out group behavior under additional declared constraints.

A simpler unary control shows that only one delayed defect is enough. Let f(a^n)=1 iff p divides n, with p≥2. Its minimal transition monoid is the cyclic group C_p. Choose K beyond the tested horizon, with p dividing K, and change only f(a^K) from 1 to 0. The modified sequence is ultimately periodic, hence regular, but not purely periodic. A reachable unary automaton whose sole transition is a permutation runs on a cycle from the initial state and therefore has a purely periodic output sequence. The modified minimal automaton cannot have that property. To see non-pure-periodicity, if it had period t>0, then the value 0 at K would repeat at K+pt, a different multiple of p that was not changed and has value 1.

## 6. Where the categorical formulation adds a useful discipline

For the full ideal behavior, define

u ~_k v iff f(uz)=f(vz) for every |z|≤k,

and Q_k=Σ*/~_k. These are **ideal finite-context quotients over all preparation histories**, not available finite data sets. Their definition already quantifies over every possible history u, so a finite empirical table must not be silently identified with Q_k.

There are surjective restriction maps r_k:Q_{k+1}→Q_k and well-defined maps t_{a,k}:Q_{k+1}→Q_k given by [u]_{k+1}↦[ua]_k. In general there is no endomorphism Q_k→Q_k corresponding to a. Two histories may look identical through depth k and yet diverge after a followed by a depth-k observation.

The precise condition for an a-action at level k is that t_{a,k} be constant on the fibers of r_k; equivalently it factors uniquely through r_k. In categorical language, t_{a,k} must coequalize the kernel pair of the regular epimorphism r_k. This is ordinary effective quotient descent in Set. If every letter descends, then ~_k=~_{k+1}; by induction it equals ~_f, so the observational quotient has stabilized to the minimal behavior object.

For the S_3 behavior:

- Q_0 has 2 classes, according to whether the current element is e.
- Q_1 has 4 classes: three singled-out elements detectable by ε,a,b, and one residual class of three elements.
- Q_2 has 6 classes and is the full minimal automaton, because suffixes of length ≤2 represent every inverse.

At the first two stages the supplied interventions do not all descend to operations on the apparent state set. At the third they do, and the resulting endomorphisms form S_3. This is a stronger description than saying a pre-existing group has merely been measured more accurately: the coarse apparent objects did not yet support the relevant dynamics. But the construction is also exactly the kind of phenomenon handled by coalgebraic observation depth and automata consistency, so it should not be advertised as an independent new theory without an additional result.

Finite evidence can certify this descent only when it covers all relevant preparations, as ensured here by the six distinguishable rows together with the six-state upper bound. A closed-looking finite table without that bound can be produced by every delayed-failure example above.

## 7. Relation to known results and exact limits

- **Active automata identification:** Angluin's L* uses membership and equivalence queries, with counterexamples, to learn regular behavior. Our exhaustive finite certificate replaces the equivalence oracle by a known state bound and enough membership tests. It offers no new learning algorithm or polynomial complexity claim. [Angluin, 1987](https://homepages.math.uic.edu/~lreyzin/papers/angluin87.pdf).
- **Conformance testing:** The compact H-certificate is a state-cover plus distinguishing-suffix argument. The W-method tradition makes explicit the state bound, reset, determinism, reachability, and complete specification assumptions. [Chow, 1978](https://archiv.infsec.ethz.ch/intranet_secured/r/1/chow-testingFSMs.pdf); [Fujiwara et al., 1991](https://www.site.uottawa.ca/~bochmann/Curriculum/Pub/1991%20-%20Test%20selection%20based%20on%20finite%20state%20models.pdf).
- **Categorical syntactic algebra:** The canonical quotient and its universal property, and the identification with the transition monoid of the minimal automaton, are established theory. [Adámek, Milius, Urbat, 2018](https://arxiv.org/abs/1804.03011).
- **Finite telltales:** A finite data set identifying behavior among M_N is a finite distinguishing sample relative to that class. It should not be conflated with Angluin's positive-data telltale, which blocks certain proper-subset alternatives and is used for identification in the limit, not necessarily finite announced certainty. The examples here use both 0 and 1 outputs. [Angluin, 1980](https://www.sciencedirect.com/science/article/pii/S0019995880902855).
- **Limit identification versus finite warrant:** With fair eventual membership data and a fixed effective enumeration of all finite machines, a least-index consistent learner eventually stabilizes on the target behavior: only finitely many earlier candidates need refuting. It need not know when stabilization has occurred. This does not contradict Theorem 2, which rules out a sound finite announcement of group structure at the target without a restricting promise.
- **Noise:** All claims are exact and deterministic. Repeated approximate matches, probabilistic outputs, approximate invertibility, or changing systems require a separate statistical and stability theory. Finite samples do not establish exact equations merely by being numerous.
- **Ontology:** The example establishes a canonical organization of operationally distinguishable behavior. It neither proves that it is the system's uniquely correct underlying ontology nor licenses unobservable structural claims.

## 8. Responsible ambitious claim

A defensible proposed research direction is to organize categorical phenomenology around **the emergence of operations by observational descent**, together with explicit access regimes and model-relative finite certificates. The ambition would be to generalize beyond a fixed algebraic signature and finite-state Set models, and prove when experimental extensions create, obstruct, or certify universal constructions on observational objects.

The work above supplies a sharp benchmark: a successful general theory must recover both (i) a genuine noncommutative group warranted from finite behavioral data under a non-group-specific capacity promise, and (ii) the inability to warrant that structure from any finite horizon when delayed irreversible completions remain admissible. It must also avoid treating an operation on the syntax of experiments as an operation already defined on empirical appearances.

This is a promising organizing proposal, not a demonstrated novel theorem or a completed general framework. The automata example is a calibration test for such a proposal rather than proof of its originality.

## 9. Independent checks

Independent mathematical review found no blocking defect and verified the unary sharpness construction. Executable checks are in `checks/check_automata.py` with recorded results in `checks/results.json`, relative to this note. They verify the S_3 table and 48-test certificate, failures of both letter descents at depths 0 and 1, successful descent at depth 2, and the sharpness examples for N=2 through N=20. The proofs above cover arbitrary N; finite checks are supplemental evidence, not substitutes for those proofs.
