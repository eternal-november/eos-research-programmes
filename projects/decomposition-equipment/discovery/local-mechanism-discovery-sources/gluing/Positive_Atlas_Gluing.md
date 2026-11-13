# Positive local atlas gluing and unresolved chart families

## Scope and plain-language summary

A learned observation patch is not declared to be a physical component. Its finite hidden alphabet can contain several components, and different patches can overlap. The task here is to compare all possible ways of coordinatizing those small alphabets and to certify when the resulting local stochastic mechanisms describe one whole process.

The central positive result is stronger than independent local fitting. Once the candidate coordinate charts are globally coherent, checking the full next-state distribution of every observation patch is enough to certify the entire transition law. The reason is not generic pairwise consistency: the declared universe gives a positive transition law whose log-probability is a sum of terms supported in those patches. Within that class, matching patch marginals determines the whole law. A quantitative version bounds the error when the patch distributions agree only approximately.

The result retains unresolved coordinate choices. It does not identify a unique physical hardware partition or expose hidden state to a controller. A source's mathematically available internal state is not an installed sensor or a permitted communication channel.

## 1. Finite observation atlas and declared universe

Let I be a finite index set of observation patches. For each i, a preliminary latent-view identification step provides a finite alphabet Z_i. Its labels have no physical meaning. We assume that pairwise joint laws, and the temporal conditional laws specified below, have been identified in mutually consistent local labels. This note does not prove that preliminary noisy-view identification step.

The declared universe consists of a finite product X=prod_{a in A} X_a, with |X_a|>=2, covered by subsets A_i of A, and bijections

    phi_i : prod_{a in A_i} X_a -> Z_i.

Every atom belongs to at least one patch. The atom sets, cardinalities, incidence sets, and phi_i are not supplied to discovery. There is a strictly positive transition kernel

    K(x'|h)=prod_{a in A} k_a(x'_a | h_{Pa(a)}),

where h=(x(t),...,x(t-L+1)) is a bounded lag history and parent scopes include lag indices. For L=1, h=x. All statements below condition on the complete old history h, even where y is used for brevity. The positive kernel is the law of the FRESH next-coordinate vector; the expanded-history transition has deterministic shift constraints and is not strictly positive. Apply the same instantaneous atlas map at every lag.

There are bounded local parent scopes. This is a declared independent-innovation model class, not something inferred from pair statistics alone. Each local entry is at least eta>0. Positive stationarity gives full support on X. More strongly, every k-coordinate stationary marginal has every atom at least eta^k, because this holds conditionally after one update.

The preliminary data include the exact support R_ij of (Z_i,Z_j) for all pairs, including pairs whose support is a full Cartesian product. They also include, for each patch i, a conditional next-patch kernel

    Gamma_i(z'_i | z_{D_i}) = P(Z_i(t+1)=z'_i | whole old state),

where D_i is a bounded collection of old patch-and-lag pairs. The equality means that the right side depends only on their jointly consistent old values. D_i may be learned and need not be unique. A sufficient exact discovery method is to minimize H(Z'_i | Z_D) over a bounded collection of contexts containing at least one cover of all true parents of A_i. The minimum equals conditioning on the whole old state; every exact minimizer is sufficient. Finite data require a margin or a confidence-family treatment, not this equality by assertion.

## 2. Pair supports and the common quotient

A relation R subset U x V that projects onto both finite sets is the fiber product of two surjections onto a common set C if and only if every connected component of its bipartite support graph is complete bipartite. In that case C can be the set of connected components and the quotient maps send vertices to their component.

Proof. A fiber product has one complete bipartite block per shared quotient value. Conversely, complete bipartite components make membership exactly equality of component labels.

Under the universe in section 1, R_ij has this form, and its quotient is the joint coordinate X_{A_i intersect A_j}. This conclusion concerns support, not independence or the stationary probability table.

Mere distinct atom-incidence signatures do not force a unique product atlas. If one atom occurs only where another occurs, complements can be changed depending on the exposed coordinate. For example (x,b) and (b,c) expose b, but the first patch also permits the static chart (x xor b,b). Dynamic tests can reject this twist, or can legitimately leave it unresolved.

Even a Boolean lattice of equivalence relations is insufficient to infer a product. On U={(0,0),(0,1),(1,0)}, the two coordinate kernels generate a four-element Boolean lattice, but the map to the two quotient alphabets misses (1,1). An actual product-map bijectivity check is essential.

## 3. Coherent candidate atlases

A candidate local chart is any bijection

    g_i : Z_i -> prod_{b in B_i} Y_{i,b},  |Y_{i,b}|>=2.

Local alphabets are bounded, so all cardinality tuples and all such bijections can be enumerated with a cost depending only on that local bound. This is local chart search, not enumeration of X.

Candidate factor occurrences are identified across patches, with explicit bijections of their value alphabets. An accepted global atlas must satisfy:

1. A global factor occurs at most once in each patch.
2. Value identifications around every cycle compose to the identity.
3. For every pair i,j, the candidate equality constraints on shared factor values describe exactly R_ij.

Write B for the resulting global factor set and Y=prod_{b in B}Y_b. These checks imply that Y is in bijection with the compatibility space

    Omega={(z_i)_i : (z_i,z_j) belongs to R_ij for every pair}.

Under the declared universe, X is also in bijection with Omega: each shared true coordinate is made consistent by the pair constraints, and there are no further support restrictions because X is a full product. Consequently every accepted candidate atlas gives a bijection F:X->Y, without constructing either product alphabet explicitly.

This conclusion would be false without the full-product promise. Three binary patch variables with even parity have full support on every pair but not on all triples. Pair supports cannot exclude that world. Section 1 excludes it at the latent-state support level; it does not claim the exclusion was empirically verified by pair data.

A simple rejected atlas consists of three binary patches with relations z1=z2, z2=z3, and z3=1-z1. Each pair relation separately is a valid common quotient. Their cycle has flip holonomy and no global realization.

## 4. Local stochastic tests imply global transition equality

Fix any accepted candidate atlas, and transport K along its bijection F to a kernel P(y'|y). For each candidate factor b, choose an owner patch containing it. Define p_b(.|y) as the corresponding one-coordinate marginal of Gamma_i in that patch's chart. Because these are marginals of one actual process and the atlas is coherent, the definition is independent of owner. It is a function of the old patch context D_i, expressed in candidate coordinates.

Suppose that for every patch i and every consistent old context, the entire conditional distribution in that patch factorizes:

    Gamma_i^g(y'_{B_i}|y)=prod_{b in B_i} p_b(y'_b|y).

Then

    P(y'|y)=prod_{b in B}p_b(y'_b|y)

for every old state y and next state y'. Thus all candidate local kernels are positive and jointly reproduce the whole transition law. Cycles in the observation cover are permitted.

### Proof

Fix y. For each true atom a choose a patch i(a) containing it. The true next value x'_a is a function of the candidate next coordinates Y'_{B_i(a)}, because that patch chart is a bijection. Hence

    log P(y'|y)=sum_a f_a(y'_{B_i(a)};y),

where f_a is log k_a after the coordinate change. This is a positive graphical-model distribution with future scopes among the observation patches. Let Q(y'|y)=prod_b p_b(y'_b|y). Its log density also is a sum of patch-supported functions, assigning each univariate term to an owner patch.

By the factorization test, P and Q have the same marginal on every B_i. Therefore the expectation of log(P/Q), a sum of patch functions, is the same under P and Q. But their difference is

    E_P log(P/Q) - E_Q log(P/Q)
      = KL(P||Q)+KL(Q||P).

Both terms are nonnegative, so both vanish and P=Q. This proves the claim.

### What the theorem does and does not certify

The result is a local-to-global certificate because it checks full small patch distributions, not merely single-coordinate or pair moments. Its sufficiency uses the declared true independent-innovation universe and the fact that every true atom is available inside some identified patch. Generic pairwise predictive agreement, positivity of local tables, or finite predictive rank would not suffice.

Once p_b is known as a finite function of old patch states, its minimal old-coordinate parent set is exactly the coordinates on which that function depends. It is found by changing one coordinate at a time in its bounded local domain. This produces an operational dependency graph for the chosen realization. It is not a causal hardware-identification guarantee outside the declared universe.

Every occurrence of a fixed old state in the proof may be replaced by a fixed old lag history. The proof never takes the logarithm of the expanded-history shift kernel.

The factorized conditional law permits simultaneous private random draws at each candidate atom. A change of atlas may change the number, cardinalities, and parent sets of those atoms. It cannot give the controller access to their hidden values. The original observation channel remains part of the realization.

## 5. Quantitative local-to-global error

Retain a correct coherent atlas, but let Q(y'|y)=prod_b q_b(y'_b|y) be a positive candidate kernel. Suppose every true local factor has entries >=eta, every candidate factor has entries >=eta_hat, and for each patch i and old state y,

    TV(P_{B_i}(.|y), Q_{B_i}(.|y)) <= epsilon_i.

Choose owner patches i(a) for true atoms and j(b) for candidate atoms as above. Then

    KL(P||Q)+KL(Q||P)
      <= sum_a epsilon_{i(a)} log(1/eta)
         + sum_b epsilon_{j(b)} log(1/eta_hat) = C.

Indeed the oscillation of each log local probability is at most its stated logarithm; expectation differences of a bounded function are at most its oscillation times total variation. Apply this termwise to log(P/Q), then use Pinsker:

    TV(P(.|y),Q(.|y)) <= min(1,sqrt(C/2)).

If epsilon_i<=epsilon, the bound is at most sqrt((|A|log(1/eta)+|B|log(1/eta_hat))*epsilon/2). A certificate need not know |A|: if m patches have alphabet size at most R, coverage and nontrivial atom cardinality give |A|<=m*floor(log2 R). It is not dimension-free. It is uniform in y only if the patch confidence bounds are uniform in every required local context.

With initial-law error epsilon_0 on the full L-step lag history, an H-step transcript coupling gives at most min(1,epsilon_0+H*sqrt(C/2)). Pushforward through the original observation channel cannot increase this distance. This does not certify unmodeled physical hazards.

### Stationary initialization

Strict positivity alone does not yield a useful polynomial mixing bound. A compact local update rule does not imply a cheap exact stationary initializer.

One optional sufficient condition is a certified fresh-update Dobrushin bound. Let c_{b,a,l} bound the TV change of candidate atom b's next-state row when only atom a at lag l is changed. Require

    max_b sum_{a,l} c_{b,a,l} <= kappa < 1.

This is not a row-sum condition on the expanded-history transition, whose deterministic shift rows have coefficient one. Under a coordinatewise maximal coupling, each new-coordinate mismatch is at most kappa times the maximum mismatch over the preceding L times. Consequently, after every block of L updates, that maximum contracts by kappa. Any two initial histories are within

    |B|*L*kappa^floor(T/L)

in total variation on the entire lag-history state after T updates (a union bound); a bound larger than one is truncated to one. For L=1 this is |B|kappa^T.

If true and candidate FRESH joint transition rows differ uniformly by at most beta, comparison of their shifted-history chains gives T*beta error over T steps. A T-step burn-in of Q from any fixed history is therefore within

    T*beta + |B|*L*kappa^floor(T/L)

of the true stationary lag-history law. Compare stationary P evolution to Q evolution from the same initial law, then apply Q's contraction. The burn-in cost is explicit, and no reset or physical initial-state control is assumed. The initialization is a model simulation operation, not a procedure that initializes the actual environment.

## 6. The finite family of unresolved charts

Sections 3 and 4 produce a sound and complete family of candidate product atlases within this patch-compatible realization universe: enumerate bounded local charts, retain coherent overlap gluings, and apply the local conditional-product tests and any specified parent/interface resource tests. Completeness here means every patch-compatible product realization of the observed full process that satisfies the declared candidate bounds appears up to labels. All such bounds must actually be filtered: local factor count, factor cardinalities, parent count, allowed lags, communication and summary-state budgets, and any candidate positivity floor. The truth floor eta used in the error estimate is not automatically the same as a candidate floor: merging true atoms can reduce the smallest local transition entry to eta raised to the number merged. It does not include arbitrary hidden refinements, extra invisible states, non-product supports, unrestricted correlated innovations, or different observational grammars.

A useful finite constraint representation avoids listing every whole realization:

- Each patch variable selects a local chart and identifications for its factors.
- An identification token records one global factor's occurrence patches, its local coordinate slots, and bijections to one canonical value alphabet.
- Its occurrence patches must form a clique in the nontrivial-overlap graph E, where ij belongs to E iff R_ij is not full Cartesian. Otherwise sharing the factor would contradict an observed full pair support.
- Neighboring patch choices must agree on tokens and reproduce R_ij exactly. A token's canonical alphabet makes holonomy consistency explicit.
- Local product-kernel tests constrain a patch's chart. Bounds on the inferred old-coordinate parent scope depend only on that patch and its learned old context patches. Further specified local interface tests can be added on their actual scopes.

Assume the resulting finite constraint graph has bounded treewidth w_c, and the overlap graph has bounded treewidth w_o. Each token occurs in a clique of size <=w_o+1. With bounded patch alphabet, token and local chart domains are polynomial in the number m of patches (a coarse bound suffices; the exponent depends on w_o and the alphabet bound). Standard tree-decomposition dynamic programming decides feasibility and represents all solutions in a compact solution DAG in O(m*L^(w_c+1)) table work, where L is the largest domain. It can count or enumerate represented solutions without enumerating the physical whole state product. There can still be exponentially many atlas solutions, and emitting all of them is necessarily output-expensive.

The width here is the width of the actual observation-and-temporal constraint graph, not merely the physical wiring graph. No general polynomial-time claim follows for unbounded width. Computing an appropriate tree decomposition has its own cost, or a valid bounded-width decomposition can be supplied as a checkable witness.

The CSP algorithm is standard machinery. The mathematical burden supplied above is why these particular local constraints are sufficient for positive global dynamics despite unresolved local coordinate choices.

## 7. Crossing summaries and the danger of independent draws

The accepted atomic realization has a canonical complete event record: every old atom value, each local innovation outcome, every new atom value, and the original observation noise. Any grouping or overlapping view must use the same named outcomes for shared atoms. Regrouping this record is exact and preserves all coupled trajectories.

It is generally wrong to sample overlapping summary transitions independently merely because their separate kernels are correct. If a summary-only common realization is desired, let h(x) be the tuple of retained summaries and let u be the permitted external input. Its exact controlled Markov condition is

    sum_{x':h(x')=v} K(x'|x,u)

being constant as x varies within each h-fiber, for every u and v. For a bounded union of source regions and parent scopes this is a finite local test. It is necessary and sufficient for a Markov implementation on that summary state that works for every initial law and allowed input sequence. If it fails, refine the summary partition by the joint response rows and close under controlled lumpability. This refinement is coarsest among deterministic state summaries refining the prescribed observable partition; it is not a lower bound against arbitrary stochastic encodings or additional communication.

A budget restriction can reject the resulting refinement. A hypothetical latent-state encoder does not authorize a new physical sensor or wire. The hardware-access rule must be checked separately and retained in the type.


### 7.1 A recursive interface genuinely needs additional state

Let a source have bits (r,m,n), external input u in {0,1}, and independent fresh updates with probabilities

    P(r'=1)=0.1+0.2*r+0.4*m+0.1*u,
    P(m'=1)=0.2+0.5*r,
    P(n'=1)=0.3+0.2*n.

Suppose the required outgoing observation is r. Its initial partition has two classes. For a fixed r and u, changing m changes the next outgoing-bit probability, so a recursively updated summary retaining r must distinguish m. The pair (r,m) is sufficient because its next joint law depends only on (r,m,u); n remains irrelevant. Controlled partition refinement gives exactly 2 -> 4 -> 4 classes. The necessary state is two bits rather than the one instantaneous output bit, but the full three-bit source need not be retained. This lower bound is for a deterministic, autonomously maintained summary under the stated input and output contract; moving memory elsewhere or adding communication changes the contract.

### 7.2 Individually exact crossing summaries need not have an exact joint update

Consider five source bits (R,H,Z,A,B) with independent fresh updates

    P(R'=1)=1/2,
    P(H'=1)=0.2+0.6*Z,
    P(Z'=1)=0.2+0.6*Z,
    P(A'=1)=0.25+0.2*A,
    P(B'=1)=0.35+0.2*B.

All joint fresh-update probabilities are strictly positive. Let one region contain (R,H,Z,A) and the other (R,H,Z,B). Their prescribed observation contracts require q_S=R and q_T=R xor H, respectively. Each summary alone is an iid fair bit and is already strongly lumpable with two states. These are prescribed readouts, not automatically minimal summaries for an empty collection of outside receiver kernels.

Together (q_S,q_T) determines (R,H), but not Z. For the same old (R,H), changing Z changes P(H'=1) from 0.2 to 0.8. Therefore the two next joint summary laws have TV distance 0.6, even though each individual next marginal is fair. A joint four-state summary cannot be Markov for every initial state. Refinement must retain Z; (R,H,Z) suffices, giving exactly 4 -> 8 -> 8 classes. A and B remain irrelevant.

Thus separately drawing two fair summary bits gives the wrong coupled law. A common realization retaining the shared Z mechanism works, but a budget of four deterministic joint summary states retaining the current prescribed readouts fails. This is not a lower bound on every output-generating machine: if outputs may be emitted on transitions rather than retained as current state, a two-state Mealy implementation can retain Z, freshly draw R and H on each transition, emit the pair, and update Z. That changes the storage/timing contract. The eight-state bound applies only to the stated deterministic current-state refinement problem, with all source initial states respected. This example belongs to the non-rich/ambiguous branch because the fair R update does not distinguish every local coordinate through its own conditional distribution. It does not contradict a generic rich-row uniqueness theorem.

Finite checks for sections 2, 3, 4, 5, the lagged burn-in bound, and these two summary examples are in check_positive_atlas_gluing.py. They are regression tests, not substitutes for the all-size proofs.

## 8. Baseline status

Common-quotient support tests, strong lumpability, positive graphical-model uniqueness from clique marginals, and bounded-width constraint dynamic programming are established mechanisms. The exact integration claim here is the passage from an unknown finite patch atlas through unresolved coordinate choices to a locally checkable whole positive transition realization, with the stated noise-view and model-universe assumptions. No priority claim is made.

Primary baseline references checked for this note:

- Wainwright and Jordan, Graphical Models, Exponential Families, and Variational Inference, section 3.5.2 (forward mapping to mean parameters; the available draft labels the injectivity result Proposition 3 and the mean-parameter existence result Theorem 1). The discussion states uniqueness of the exponential-family density at a specified interior mean parameter. This is the standard mechanism behind section 4, not a new graphical-model uniqueness theorem. https://people.eecs.berkeley.edu/~jordan/sail/readings/wainwright-jordan-fnt.pdf
- Dean and Givan, Model Minimization in Markov Decision Processes (AAAI 1997). The homogeneous partition and coarsest homogeneous refinement construction are the controlled-lumpability baseline for section 7. The paper also explicitly warns that aggregate manipulation costs need not be constant. https://cdn.aaai.org/AAAI/1997/AAAI97-017.pdf
