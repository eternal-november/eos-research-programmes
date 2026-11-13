# Protocol-context substitution: prior art and scope

31 October 2026. Primary-source context for the concurrent controlled-prefix and cylinder-factorization comparison results. This is a scope and proof-obligation review, not a novelty claim or exhaustive literature review.

## Framing

The categorical organization is useful, but neither a colored operad, a realization algebra map, nor a compositional property layer is itself new. Existing work proves actual wiring-compatible realizations and feedback closure, not just diagrammatic notation. The useful target here is narrower and more concrete: derive a specific asynchronous context action, preserve its probability law including private controller memory and primitive timing, construct the actual joint cylinder/path maps, and then prove coherence of the two-sided normalization comparisons. The previously established CFS uniqueness machinery should finish coherence only AFTER those honest maps and laws exist.

## Verified primary baselines

### 1. Wiring syntax

David Spivak, *The operad of wiring diagrams* (2013), https://arxiv.org/abs/1305.0297 . Hierarchical nesting of wiring diagrams is explicitly operadic; relation algebras, plug-and-play systems and recursion are examples. Thus naming typed slots and grafting contexts is established organizational machinery. It does not prove a new stochastic operational interpretation or that a chosen abstraction respects it.

### 2. Compositional dynamical semantics and abstraction

David Spivak, *The steady states of coupled dynamical systems compose according to matrix arithmetic*, https://arxiv.org/html/1512.00802v2 . Theorem 4.12 gives discrete-system wiring semantics; Theorems 4.14 and 4.20 treat measurable and continuous systems. Theorem 4.29 proves the steady-state map a monoidal natural transformation of wiring algebras; Theorem 4.40 does so while retaining steady-state sets. This is a substantive example of analysis commuting with connection. It does not reconstruct causal stochastic workers from two-sided controlled cylinders or handle the specific scheduler/resource/tick protocol in our notes.

### 3. Machines, realization, feedback and contracts

Schultz, Spivak and Vasilakopoulou, *Dynamical Systems and Sheaves*, https://arxiv.org/html/1609.08086v4 . Propositions 5.1.1 and 5.1.2 realize discrete/continuous dynamical systems as machines through wiring-algebra maps. Propositions 4.3.1–4.3.2 prove closure for inertial, total and deterministic machines; Proposition 4.4.3 supplies discrete versions. Proposition 4.5.3 gives a safety-contract algebra, and Proposition 5.2.15 translates machines to their maximal validated safety contracts compositionally. Theorem 5.2.12 gives structure-preserving translations under specified regular-category/extension data. These are particularly close structural precedents. Their totality is not our almost-sure mission completion: an indefinitely running reactive machine can be total. Likewise their safety contracts are not quantitative termination certificates. We should reuse the separation of machine semantics and property semantics, while proving the distinct stochastic closure obligations rather than claiming the distinction is new.

### 4. Indexed double categories / lens-like wiring

David Jaz Myers, *Double Categories of Open Dynamical Systems*, https://arxiv.org/html/2005.05956v2 . The construction distinguishes covariant system maps (including trajectories and steady states) from contravariant plugging of variables into parameters, and organizes them in indexed double categories. Its main representability result sends suitable system structures to spans compositionally. This is a useful precedent for keeping wiring and comparison directions separate. It does not authorize treating our arbitrary CFS legs as operational simulation maps, or treating deterministic span pullbacks as probabilistic coupling pullbacks.

### 5. Probabilistic/quantum context closure and time

Portmann, Matt, Maurer, Renner and Tackmann, *Causal Boxes*, https://arxiv.org/html/1512.02240v3 . Theorem 6.7 proves closure of (sub)normalized causal boxes under compatible port connection; Theorem 6.11 proves composition-order independence. The proofs factor connection into parallel composition and loops and establish the needed loop laws. Messages carry positions in a countable partially ordered set; causal restrictions are substantive. Section 7 defines distinguishing tests, with Theorem 7.3 giving their pseudometric (metric for all distinguishers). This strongly undercuts any generic claim that interactive contexts or feedback-compatible probabilistic semantics are new. It is not the present classical countable-history/CFS realization theorem. An instructive boundary is that their identity wire is not itself a causal operation: their distinguishers may insert instantaneous loops separately. We likewise must distinguish zero-cost structural wiring from charged operational steps, rather than silently equating them.

### 6. Termination-preserving concurrent refinement

Liang, Feng and Shao, *Compositional Verification of Termination-Preserving Refinement of Concurrent Programs* (CSL-LICS 2014), author-hosted description and paper links: https://flint.cs.yale.edu/flint/publications/rgsimt.html . RGSim-T establishes termination-preserving simulation congruent under parallel composition and supports thread-local proof rules. Thus preservation of termination under component replacement and concurrent composition is not a novel generic target. Our exact full trace-law replacement is a different, stronger equality in a more restricted stochastic language; it is not an extension of RGSim-T established merely by terminology.

### 7. Cryptography as a diagnostic, not a target change

Broadbent and Karvonen, *Categorical composable cryptography*, https://arxiv.org/html/2105.05949v3 . Definition 1's attack-model conditions include decomposition of attacks on composites; Theorem 3.1 obtains a wide sub-SMC of secure protocols. Section 4's observational quotient requires a monoidal congruence, and notes that efficient processes may need restriction to ensure it. This is the exact warning relevant here: assuming congruence is a valid abstract hypothesis, but does not prove the desired concrete observer/context closure. Our task should supply a concrete factorization/closure argument rather than rename it. Cryptography is used here only as a comparison of proof obligations.

## Where the present proof must do real work

The following are mathematical requirements of this construction, not claims quoted from the sources.

1. **Substitution is more than free syntax.** A tree of contexts has to compile to one actual primitive-step kernel. Define the scheduler token, current program counter, interface requests/replies, private memory, resource ownership and charged ticks. Prove compiling grafted trees agrees with running the nested program. A free operad of trees ensures only syntactic associativity.

2. **Grouping cannot change scheduling.** Flat round-robin on A,B,C yields A,B,C repeatedly; round-robin on [A,B] and C, with one inner poll per outer visit, yields A,C,B,C repeatedly. These are different event traces and service ratios. Preserve the actual nested control structure when flattening; do not replace it by a fresh global round-robin rule. The unit context must forward without adding a tick unless a different explicit timed equivalence is proved.

3. **The boundary must be closed under nesting.** If a parent selects a child module once, does the child execute one leaf step, one internal administrative step, or an entire invocation? These are different protocols. Whole-invocation hiding can reintroduce the existing deadlock counterexample. Administrative steps cannot be hidden at zero cost if an infinite administrative loop becomes one apparently normalized transition.

4. **Private context memory must remain in the induction.** The proved local replacement theorem uses the output law conditional on the current private context state and retained history, not only public observations. A context-owned fair bit correlated with a worker can distinguish a reconstruction based on marginal fair outputs. An independent-private-innovations implementation discipline can derive closure recursively; for correlated preparations, retain the common state or supply a joint law. Neither richer isolated tests nor an operad creates the missing coupling.

5. **Actual path maps, before normalization.** Construct finite-prefix carriers and a deterministic history-extraction map q that retains all context state/events. Prove q pushes each preparation column to the reconstructed column and pulls every designated test back correctly. For nested substitution prove the two history-extraction routes are literally equal after explicit state-tag reassociation. Only then invoke the existing normalizer naturality/rigidity to obtain coherent comparison cells. This avoids assuming an all-purpose assembly functor preserves reconstruction.

6. **Changed contexts can change cylinders.** Do not apply same-cylinder rigidity between different scheduler experiments or different visible tests. Supply the actual source-changing cylinder map, including test variance. The prior signed context base Prep × Test^op and noncollapsed 2-span warning remain relevant.

7. **Progress stays a property, not semantic admission.** Deadlocking/starving contexts remain well-defined semantic operations. Proving a separately specified progress rule sound may restrict scheduler and lock discipline; interpreting that rule as an everywhere-defined certificate operation would overstate its domain. A fiber of available certificates over each semantic system can be empty. A global fair scheduler is not implied by fairness of local hierarchical schedulers without a service calculation.

## Honest claim threshold

A worthwhile completed result would say: for this explicitly specified asynchronous protocol language, concrete substitution preserves the reconstructed law and the actual two-sided comparison data, including primitive costs and nontermination. The general categorical organization is an application of established machinery; the derived context interpretation and compatibility proof are the technical content. It would remain one doctrine-level instance, not the universal theorem for all gluing/feedback languages, and no finite-data identification, small realization, arbitrary correlation, or native operational meaning for canonical Isbell apices follows.
