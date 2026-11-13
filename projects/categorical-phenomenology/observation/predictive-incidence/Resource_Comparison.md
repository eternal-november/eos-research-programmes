# Independent bridge candidate: finite evidence, generated tests, and incidence loss

3 November 2026. Mathematical development and targeted source audit. This note is independent of, but uses the notation and finite-warrant discipline of, the earlier `phenomenology_emergence_20261103/report.tex`.

## Finding first

There is an exact, useful comparative theorem: a small certificate for a predictive automaton can determine an incidence completion that no equally small *literal restriction to measured attributes* preserves. The discrepancy can be exponential in the number of predictive states. The certificate generates the unmeasured columns; it does not turn them into observations or make unavailable experiments executable.

The underlying ingredients have strong direct predecessors. In particular, the exponential family below is the standard symmetric-group witness for permutation-automaton reversal complexity, the restriction criterion is standard meet-irreducible attribute reduction, and the finite predictor certificate is state-cover/characterization-set conformance. The combined theorem is a precise resource-transfer control, not a defensible source-distinct Gate A theorem on current evidence. A second construction separates short logical certification from a long *actually executed* common-positive witness, but its number-theoretic mechanism is classical unary-automaton intersection.

The earlier report already gives the ideal residual-to-intersection embedding and commuting derivatives. None of that is claimed again as new. What follows adds precise restriction maps, independent finite saturation checks, exact retained-attribute requirements, and physical-versus-inferred experimental resource accounting.

## 1. Data types and three experimental levels

Let a deterministic binary-output system have a finite state set Q, alphabet Σ, transition maps δ_a:Q→Q, initial state q₀, and output set F⊆Q. Neither invertibility nor group structure is required in this general setting. Write δ_w for sequential execution of w and

P_w = {q∈Q : δ_w(q)∈F},     R_q = {w∈Σ*: q∈P_w}.

Thus P_w⊆Q is a test's support, while R_q⊆Σ* is a state's predictive row. These are different types. Histories h prepare δ_h(q₀), and a reset experiment observes f(hw).

For a continuation family E⊆Σ*, define:

- q∼_E r iff q∈P_w ⇔ r∈P_w for all w∈E; Q/∼_E is the predictive quotient visible on E.
- C_E = {⋂_{w∈B}P_w : B⊆E}, with empty intersection Q; this is the extent closure system on Q.
- I_E = {⋂_{q∈A}(R_q∩E) : A⊆Q}, with empty intersection E; this is the intent closure system, ordered by inclusion.
- cl_E(A)=⋂{P_w : w∈E and A⊆P_w}; the fixed sets are C_E.

C_E and I_E are order-dual by the formal-concept polarity. Predictive rows are only some of the intents. Formal intersections need not be reachable states. No equivalence of the predictive carrier and the concept lattice is assumed.

At stage t, actual reset words T_t are finite and T_t⊆E_t^run⊆Σ*, where E_t^run is the currently executable set. For a fixed finite preparation family H, a continuation w can be regarded as currently admissible *across H* only if Hw⊆E_t^run, and its entire column is actually measured only if Hw⊆T_t. The ideal continuation family remains Σ*. A computed value at a word outside E_t^run is a model consequence, not a measurement and not permission or ability to execute it.

An exhaustive finite state set Q is one possible model promise. A different promise, used below, is that the unknown minimal reachable behavior has at most n states; n distinct observed rows then certify a state cover. Merely collecting n named preparation histories does not make them exhaustive.

## 2. Exact restriction theorem and missing-experiment witnesses

Let E⊆U⊆Σ*, with Q finite. Restriction defines

ρ_E:I_U→I_E,     J↦J∩E.

This is a surjective arbitrary-intersection homomorphism. Indeed each intent has the form A'_U and restricts to A'_E, so every target intent is reached. The map need not be injective even if E separates every predictive state.

### Proposition 1: what literal attribute retention must preserve

The following are equivalent:

1. ρ_E is injective.
2. cl_E=cl_U on all subsets of Q.
3. C_E=C_U as families of subsets of the same labelled Q.
4. For every proper meet-irreducible M of the finite lattice C_U, some retained word e∈E has P_e=M.

Here proper excludes Q. Repeated words with the same support do not count as different required supports.

**Proof.** (2) and (3) are equivalent because closure operators are determined by their fixed sets. If the closures coincide, equality of restricted intents A'_E=B'_E gives cl_E(A)=cl_E(B), hence cl_U(A)=cl_U(B) and A'_U=B'_U. Conversely, if cl_E(A) properly contains cl_U(A), put B=cl_E(A). Then A'_E=B'_E, but A'_U≠B'_U, disproving injectivity. Every element of a finite meet-closed family is a meet of its proper meet-irreducibles. Hence (4) implies (3). Conversely, if C_E=C_U and M is proper meet-irreducible, express M as an intersection of retained supports. Only finitely many different supports occur because Q is finite. Meet-irreducibility forces one of them to equal M. ∎

This is the classical finite FCA reduction mechanism, explicitly applied to tests.

A failure produces a useful *kind* of next experiment, not automatically an admissible word. If A is closed in C_U but B=cl_E(A) properly contains A, choose q∈B\A. The definition of ideal closure guarantees a word z∈U with A⊆P_z and q∉P_z. Such a column refutes the presently apparent implication A→q. Acquiring it requires preparation-and-test runs hz for the relevant h. If z is not executable, this direct-witness remedy is unavailable. Finding the word may itself require a model or a search; the proposition is not an oracle for it.

A state separator addresses pairs of rows. An incidence separator may need a test that is positive simultaneously on a whole set of rows and negative on another. These are different obligations.

## 3. An independent finite saturation check

A useful certificate avoids assuming that the complete ideal lattice or its meet-irreducibles have already been enumerated.

### Proposition 2: finite dynamic saturation

Assume Q is exhaustive, E is finite, and ε∈E. Then

C_E=C_{Σ*}

if and only if P_{ae}∈C_E for every a∈Σ and e∈E.

**Proof.** Put D_a(S)=δ_a^{-1}(S). Then D_a preserves all intersections, D_a(Q)=Q, and D_a(P_e)=P_{ae}. If the finite checks pass, each D_a sends every generator of C_E into C_E, hence sends all of C_E into C_E. Since F=P_ε∈C_E, iteration gives P_w∈C_E for every w. Thus C_{Σ*}⊆C_E; the reverse inclusion is automatic. Conversely, C_{Σ*} is closed under every D_a, so equality implies all generator checks. ∎

This certificate requires only the columns E∪ΣE, at most |Q|(1+|Σ|)|E| binary observations when states have resettable preparation representatives. It does not require observing the identity of an action's successor. Membership of S in C_E is checkable as cl_E(S)=S from the measured table. A failed check supplies the explicit extension ae whose column enlarges the extent closure. A successful check gives an algebraic recipe for every future test by finite intersections and preimages.

The exhaustive-domain or otherwise justified behavioral-state promise is essential. Equalities verified on a nonexhaustive preparation sample are not global laws. Likewise, a successful computation from a *hypothesized* transition table is only as sound as that hypothesis's certificate. This is a finite semilattice-generation argument, closely related to algebraic automata and duality-based learning; it is not claimed as a new learning theorem.

The criterion is stronger than merely making row transitions well-defined. In particular, state separation makes row transitions well-defined on a known finite Q, but does not force the observed extent family to be preimage-closed.

## 4. Exact resource transfer from a finite predictor certificate

Let the unknown resettable behavior have at most n reachable behavioral states. Suppose H⊆Σ* contains ε and has n histories, E contains ε, and the actual table on

T=(H∪HΣ)E

has n distinct H-rows. Suppose also every successor row (ha on E) equals one of those n H-rows. Then the table determines the complete minimal behavior: the distinct rows force at least n states, the promise permits at most n, and the successor rows identify the transitions among this exhaustive cover. The ε-column identifies the output and ε-row the initial state.

Consequently the full families P_w, C_{Σ*}, I_{Σ*}, and the restriction map's failures can be computed without further physical experiments. This consequence is logically stronger than requiring that ρ_E be injective. The former allows generated attributes; the latter literally discards them.

For any specified word w, all n values in P_w can be evaluated from the certified transition table in O(n|w|) elementary transition operations. Enumerating every distinct support or every closed set can nevertheless take exponential space and time. This does not give a cheap explicit listing of an exponential output. The number of physical table queries is at most n(1+|Σ|)|E|, after duplicate reset words are removed; discovery of useful H and E is not included. This is an existence/conformance certificate, not a general unknown-machine learning algorithm with that discovery budget.

## 5. Exponential retained-attribute gap with all costs exposed

Let n=2^m≥2, k=n/2, Q={0,…,n−1}, and Σ={c,t}. Let c be the n-cycle and t the transposition (0,1). They generate S_n. Choose F to be one binary-coordinate half of Q, so |F|=k, and let the initial state be 0.

The ideal supports are exactly all k-subsets of Q: permutations preserve cardinality, and S_n acts transitively on the k-subsets. For each coordinate j choose a word w_j with P_{w_j}=B_j, the jth bit half. One of these words is ε because F itself is a coordinate half. Set E={w_1,…,w_m}.

### Theorem 3: extensional versus generative reconstruction

For this family:

1. The minimal predictor has exactly n states. E distinguishes all of them, and m=log₂n tests is optimal for binary row separation.
2. C_E has n elements, whereas

   C_{Σ*} = {A⊆Q : |A|≤k} ∪ {Q}

   has 1+Σ_{j=0}^k binomial(n,j) elements.
3. Every literal retained-attribute family U⊆Σ* with C_U=C_{Σ*} must contain at least binomial(n,k) different test supports. This is attained by choosing one word for each k-subset.
4. Under the valid at-most-n state promise, a measured conformance table with at most 3nm reset runs determines the complete predictor and therefore determines C_{Σ*}, even though its m-characterization-column restriction is not lattice-faithful.
5. The histories and suffixes can be chosen with polynomial word length. With

   D_n=(n+1)n(n−1)/2,

   all characterization words have length at most D_n, all state-cover histories length at most n−1, and all certificate runs length at most D_n+n. Thus total executed intervention letters are at most 3nm(D_n+n)=O(n⁴log n). These are coarse upper bounds, not optimality claims.

**Proof.** The coordinate tests give every distinct m-bit pattern, so all n reachable states are behaviorally distinct. Fewer than m binary tests cannot separate n states. Intersections of coordinate halves correspond to sets of coordinates required to equal 1, giving exactly 2^m=n distinct extents. Every intersection of k-subsets is either Q (empty intersection) or has size≤k. Conversely, each A of size≤k is the intersection of all k-subsets containing it, so the displayed formula holds.

The proper meet-irreducibles of C_{Σ*} are exactly the k-subsets: each has only Q strictly above it; every smaller A is the intersection of two strictly larger allowed sets. Proposition 1 proves the exact retained-support count. If a particular k-subset M is omitted, no retained support contains M, so cl_U(M)=Q. Any q∉M therefore witnesses a spurious implication M→q. The specific missing support M, and no different k-support, can refute it.

Take H={ε,c,…,c^{n−1}}. These prepare every state and have distinct E-rows. Query (H∪HΣ)E. Section 4 gives the certificate and count. Every adjacent transposition of Q is a conjugate of t by a power of c, expressible with at most n+1 letters using positive powers to express the inverse. Every permutation is a product of at most n(n−1)/2 adjacent transpositions. Thus any desired support is realizable by a word of length≤D_n, including each coordinate half. The stated run-length and total-length bounds follow. ∎

For n=4 there are 4 predictive states, 2 separating tests, 4 observed extents, 12 ideal extents, and 6 indispensable ideal test supports. For n=8 the corresponding numbers are 8, 3, 8, 164, and 70.

**What the lower bound does not say.** It is a lower bound on the number of original attributes retained in a context whose literal restriction preserves the full concept structure. It is not a lower bound on all possible membership-query learning algorithms, not a lower bound on logical warrant after a predictive certificate, and not a claim that every closure-preserving method must physically perform those exponentially many tests. The polynomial certificate expressly defeats that stronger interpretation. It also does not count the discovery work needed to find H and E.

**Decisive failure without a domain/capacity certificate.** For n≥4, let T be any finite observed reset-word set from this family and keep the fixed histories H. Choose a subset S⊆H with k<|S|<n. Choose a sufficiently long word z so all hz lie outside T. Change f on exactly those finitely many words hz so their response is 1 exactly for h∈S. The resulting g is still regular and agrees with f on T. It gives a new support S on H that is not in the original ideal extent family. Every original k-support still occurs under g: each has infinitely many realizing words, obtained by appending c^n repeatedly, and only finitely many reset words were modified. Hence the ideal closure on the same named H genuinely changes. The apparently complete finite transition table therefore does not warrant the claimed ideal completion in the unbounded regular class.

## 6. Short certification versus a long actually executed incidence witness

The next example concerns an optional requirement to execute a common-positive witness, not an unavoidable additional epistemic need after a model has been certified.

Choose pairwise distinct primes p₁,…,p_r, r≥2, and put p=max p_i, L=∏p_i, n=2+Σp_i. The states are a root s, a dead state d, and cycles C_i={x_{i,0},…,x_{i,p_i−1}}. The alphabet is {a,b₁,…,b_r}.

- a cycles each C_i, sends s to d, and fixes d.
- b_i sends s to x_{i,0} and every other state to d.
- Only x_{i,p_i−1} is accepting in cycle i; s,d reject.

All states are reachable. Let A={x_{i,0}:1≤i≤r}. Any suffix containing a b_i sends all of A to d. A pure suffix a^t is accepted from all A exactly when t≡−1 mod p_i for every i. Therefore

⋂_{q∈A} R_q = {a^{jL−1}:j≥1}.

Its shortest member has length L−1. The dead-state residual is empty, so these are distinct ideal intents, but their restrictions to every continuation horizon B<L−1 coincide as the empty set. A direct common-positive witness requires the reset runs b_i a^{L−1}, each of total length L.

Nevertheless the entire n-state predictor has a polynomial-size certificate consisting only of short runs. Take

H={ε,a} ∪ {b_i a^j:0≤j<p_i},
W={a^t:0≤t≤2p−1} ∪ {b₁a^{p₁−1}}.

H has n histories of length≤p. W has at most 2p+1 words of length≤2p−1. W distinguishes every state:

- Two different states on one cycle have different next-acceptance times.
- For states on distinct prime cycles, choose the first acceptance time t<p_i of the first. If the second also accepts then, it does not accept at t+p_i, since p_j does not divide p_i. This length is≤2p−1.
- Every cycle state is distinguished from d by an accepting time.
- The root is distinguished from any cycle state by a positive accepting time≤p; after a positive number of a's the root is dead.
- The word b₁a^{p₁−1} distinguishes s from d.

Under the at-most-n promise, (H∪HΣ)W is therefore a complete predictor certificate. It needs at most n(r+2)(2p+1) reset runs, each of length≤3p. When L−1>3p, in particular for r≥3 distinct primes, this certificate executes no common-positive suffix for A: every complete reset run is shorter than the shortest such suffix. The nonempty ideal intersection and its first member are then deductively established from this short evidence and the promise. The exact formula and polynomial certificate also hold for r=2, but this no-executed-witness separation need not: for primes (2,3), W contains a⁵ and the certificate executes both common-positive reset runs b_i a⁵.

For the first r primes, standard prime estimates give n=Θ(r²log r) and log L=Θ(r log r), hence L=exp(Θ(√(n log n))). The exact product formula, not this asymptotic, is the essential result. The construction is a familiar Chinese-remainder unary-intersection mechanism with added access letters and explicit conformance accounting.

If the scientific or operational goal is only to know whether the ideal intersection is nonempty, no further experiment is necessary after the certificate. If the goal independently requires producing an observed shared-positive column, the L-length runs really are required and may exceed the current admissible horizon. Those are different tasks.

## 7. Source comparison and novelty decision

1. **Clark, The syntactic concept lattice** (2013/2015), [author-hosted full paper](https://alexc17.github.io/static/pdfs/JLC2013.pdf). Section 1 explicitly relates the minimal DFA, residual automaton, and universal automaton to prefix–suffix incidence, distinguishing a partition from a Galois hierarchy. The broader syntactic concept lattice uses a two-sided context pairing. Thus neither the common incidence construction nor the existence of distinct predictive and lattice carriers is new here. The present support calculations use the one-sided prefix–suffix setting.

2. **Aragón, Medina, Ramírez-Poussa, Identifying Non-Sublattice Equivalence Classes Induced by an Attribute Reduction in FCA** (2021), [full paper](https://rodin.uca.es/bitstream/handle/10498/24777/2021_252.pdf?isAllowed=y&sequence=1). Its preliminary reduction theory explicitly excludes top from meet-irreducibles and connects retained attributes to irreducible concepts. Proposition 1 is a direct finite closure-system form of this established mechanism, not a new reduct theorem.

3. **Hospodár and Mlynárčik, Operations on Permutation Automata** (DLT 2020), [full paper](https://pmc.ncbi.nlm.nih.gov/articles/PMC7247878/), [DOI](https://doi.org/10.1007/978-3-030-48516-0_10). Their tight reversal complexity is binomial(n, floor(n/2)), with cycle/transposition permutation witnesses. The reverse subset states are exactly the supports δ_w⁻¹(F). Thus the central exponential orbit in Theorem 3 is an existing automata complexity witness. Its translation to indispensable extent generators does not establish novelty.

4. **Barlocco, Kupke, Rot, Coalgebra Learning via Duality** (2019), [full text](https://arxiv.org/html/1902.05762). This already supplies a substantial states/tests bridge using a dual adjunction and proves learning correctness and termination. Its teacher and successor-exploration interface is not silently interchangeable with a reset-only word oracle plus a state bound. Conversely, choosing a different oracle does not make a generic states/tests bridge novel.

5. **Björklund, Fernau, Kasprzik, Polynomial inference of universal automata from membership and equivalence queries**, [author-hosted paper](https://www.uni-trier.de/fileadmin/fb4/INF/TechReports/ratom2longelsevier.pdf). This directly learns the canonical universal/factorization structure using observation tables, with complexity measured in the universal automaton's size and a minimally adequate teacher. Hence learning an incidence-based canonical automaton is not an uncovered problem. Theorem 3 instead compares a polynomial *conformance certificate in minimal predictor size* with literal preservation of an exponential attribute family, without an equivalence oracle; this is a precise distinction, but each step is already supplied by classical conformance, reversal, and reduction results.

6. **Unary intersection precedents.** [Hospodár–Mlynárčik](https://pmc.ncbi.nlm.nih.gov/articles/PMC7247878/) already use Chinese-remainder reasoning for unary permutation operations. The much broader unary state-complexity literature studies least common multiples and Landau growth; for example [Chrobak, Finite automata and unary languages](https://doi.org/10.1016/0304-3975(86)90142-8) is a publication record, not a full-text inspection here. The CRT construction is independently proved above and not offered as a new long-witness phenomenon. The exact preparation and certificate accounting is the useful present addition.

7. **Bollig, Habermehl, Kern, Leucker, Angluin-Style Learning of NFA** (IJCAI 2009), [author-hosted full paper](https://lsv.ens-paris-saclay.fr/Publis/PAPERS/PDF/BHKL-ijcai09.pdf). NL* learns prime residual rows under unions using membership and equivalence queries. Its RFSA-consistency failures already select extended suffixes av that expose distinct or incomparable rows. Thus failure-directed extension of a test family, including order-sensitive rather than equality-only refinement, is not new in the present saturation criterion.

### Decision

The best honest deliverable is a resource-aware comparison theorem and a strong calibration example, not a claim of a new general reconstruction mechanism. It establishes an actionable distinction:

- To improve a literal observed concept context, acquire columns missing from its meet-generated closure, with dynamic failures ae supplying concrete candidates when the finite saturation premise is justified.
- To establish ideal structure with fewer physical tests, first certify a predictive generator under an explicit model-class/domain promise, then infer the missing columns.
- To obtain an actually observed witness, check whether the necessary word is currently executable and charge its full preparation and run length.

No unqualified conclusion follows that predictive sufficiency makes the measured concept lattice complete, that a model inference creates physical observations, that state-bound promises are learned from a fitted model, or that an exponential lattice can be enumerated cheaply. No source-distinct theorem-sized residual has been established by this independent route.

## 8. Finite checks (supplementary, not general proofs)

`check_alternative.py` exhaustively generates the test-support orbit and its intersection closure for n=2,4,8, checks the meet-irreducible characterization, reconstructs transitions from the stated certificates, and checks every support subfamily for n≤4. For n=4 it found a 15-run certificate of maximum length 6; for n=8, 51 runs of maximum length 20. These improve the coarse theorem upper bounds only for these checked instances.

The script also verifies the CRT state separators and certificate length/count bounds for prime lists (2,3), (2,3,5), (2,3,5,7), and (3,5,7,11). The last has 28 states, a checked 2,627-run certificate with maximum run length 33, and shortest common-positive suffix length 1,154 (hence reset witness run length 1,155). The JSON output is in `check_alternative_results.json`. These finite checks do not establish source novelty or replace the proofs.
