# Bounded primary-source baseline comparison

Publication note: This bounded literature comparison was completed before the final construction. Its tentative construction-status and stopping-conclusion language describes that earlier comparison, not the status of the accompanying final conditional theorem. The final result and exact API changes are given in `safe_anonymous_completion_theorem.md` and `comparison_delta.md`; the limited scope of the literature search and its non-novelty conclusion are unchanged.

31 October 2026. Five closest baselines checked; not a survey or novelty determination. Read alongside `comparison_delta.md` and `mathematical_review.txt`. **Tentative residuals below depend on the exact frozen observation language and safe intervention family.**

## Bottom line

Do not describe unknown source/report association, asynchronous callbacks, or recovery without full identification as new. A structured inverse problem plus an actively learned finite-state protocol is the strongest first baseline—not an arbitrary global POMDP or a table of every physical world. Whether either reduction applies depends on what physical maps, joint samples, reset/quiescence operations and complexity bounds are supplied.

## 1. Unlabeled sensing: known physical map, unknown measurement binding

Unnikrishnan, Haghighatshoar and Vetterli, *Unlabeled Sensing with Random Linear Measurements*, arXiv version checked, Theorem II.1 and §II–III. A **known** M-by-K matrix A has iid entries from an absolutely continuous real distribution; measurements are y=Bx, where B contains N distinct unknown rows of A in unknown order. For N≥2K, almost every A permits recovery of every x. Importantly, the text explicitly distinguishes unique x from possibly nonunique selection/binding S. Theorem V.1 gives failure of universal recovery when N<2K and K>1. §III uses combinatorial search; §VI discusses local high-SNR stability, not a uniform safety budget. [Primary paper](https://arxiv.org/pdf/1512.00115).

**Application test (our inference):** If anonymous telemetry can actually be represented as one vector SAx for a common persistent x and known achievable A, this is a direct baseline. It already removes observation-to-row tags. A physical acquisition protocol must still justify why the entries share that x; independently captured changing states cannot be silently assembled into one vector. Unknown arbitrary physical A is not covered by simply calling S unknown. A safe bounded alphabet need not generate the theorem's generic matrix, and a generic noiseless guarantee does not give a useful robust separation margin.

## 2. Homomorphic sensing: algebraic transformation families, not world enumeration

Tsakiris and Peng, *Homomorphic Sensing*, ICML 2019, Theorem 1. Given a finite known family T of endomorphisms of C^m, each rank at least 2n, and a general n-dimensional subspace V (n≤floor(m/2)), unique recovery follows when, for every pair τ1,τ2, a projection ρ onto im(τ2) satisfies n≤codim(Uρτ1,τ2), with U defined in equation (9). The recovery property is τ1(v1)=τ2(v2) ⇒ v1=v2. Proposition 3 specializes it to permutations and coordinate projections. Their algorithms exploit low-dimensional geometry and dynamic programming. [Primary paper, §§2–3](https://proceedings.mlr.press/v97/tsakiris19a/tsakiris19a.pdf).

**Application test (our inference):** Use this before enumerating complete worlds if bounded clock shifts, subsampling and report permutations induce known linear transformations of a structured signal space. The finite set is a transformation family, not a supplied list of whole-system hypotheses. One must prove the actual feasible signal space is sufficiently generic or directly establish the needed separation; invoking genericity for a specially structured physical protocol is not valid. Unknown nonlinear capture semantics or continuously varying unspecified delays require another argument, not a nominal relabeling of T. This theorem is about a supplied observation vector, not how to safely acquire it.

## 3. DroidStar: asynchronous callback learning and a finite certification budget

Radhakrishna et al., *DroidStar: Callback Typestates for Android Classes*, ICSE 2018, §3 and Theorems 4.3–4.5. The method assumes deterministic callback traces, observable quiescence, and finite typestate with a supplied state or distinguisher bound. Theorem 4.4 gives equivalence testing in at most |Q|·|Σ̃_i|^(B_Dist+1) membership queries. Theorem 4.5 states learning using O(|Σ_i|n³+n|Σ_i|^B_Dist) queries. The test configuration supplies abstract/concrete callin/callback mappings. §5.2 implements quiescence through a user-chosen maximum timeout and assumes a minimum callback delay for consecutive callins. The authors explicitly note Android supplies no worst-case execution time. Their method favors inexpensive resets. [Primary paper](https://dzufferey.github.io/files/2018_DroidStar_Callback_Typestate_for_Android_Classes.pdf).

**Application test (our inference):** A direct strong baseline if the raw protocol has a known finite alphabet, resettable membership-query access and certified waiting semantics. It can learn whole observable traces without assigning every callback a unique causal parent; therefore “no explicit invocation tag” alone does not defeat it. However, physical safety may prohibit queried words or resets. A bound on queries is not a bound on elapsed time, hazardous exposure, drainage, storage or lost mission opportunities. The new work would need to derive and charge a safe physical realization of this access, or explain why a mission-restricted observer suffices where exact trace learning does not.

## 4. Random asynchronous LTI identification: useful caution about the word asynchronous

Lale, Teke, Hassibi and Anandkumar, *Stability and Identification of Random Asynchronous Linear Time-Invariant Systems*, §§5–6. The identification construction treats the **randomized no-delay special case** q=1 (h=0), with mean-square stability and moment assumptions (4). Its trajectory is explicitly {x0,u0,x1,…,uT−1,xT}; equation (12) computes same-time and consecutive-time correlations. Least squares estimates average dynamics, and an extended Lyapunov relation estimates update probability and physical parameters. The discussion invokes asymptotic Markov-chain CLT behavior; it is not a finite-budget anonymous-delivery certification theorem. [Primary paper](https://arxiv.org/pdf/2012.04160).

**Application test (our inference):** Do not cite this as solving missing report-to-capture correspondence: its data already contain the aligned state/input trajectory. Its asynchronous stability examples also do not establish general delayed-system identification. It shows why unknown persistent parameters and stochastic update timing must be separated from unknown acquisition association.

## 5. Angluin: unknown target size does not mean finite physical certification is free

Angluin, *Learning Regular Sets from Queries and Counterexamples*, 1987. L* learns a regular language with membership queries plus exact equivalence queries returning counterexamples, in time polynomial in minimal DFA size and maximum counterexample length. The learner need not receive the target automaton in advance. The paper also treats a stochastic substitute for equivalence queries. [Primary paper scan](https://homepages.math.uic.edu/~lreyzin/papers/angluin87.pdf).

**Application test (our inference):** It is wrong to say that unknown memory size alone makes active learning impossible: a true equivalence oracle can support termination without a supplied ceiling. But bounded physical experiments are not that oracle. Without a certified state/distinguisher/memory bound or another structural restriction, a finite transcript cannot exclude a larger mechanism that agrees so far and diverges later. A finite mission horizon may make unrestricted future equivalence unnecessary; exploit that rather than assuming a global unknown-memory theorem.

## Hypothesis checklist for the candidate

| Axis | Must freeze before selecting a baseline |
|---|---|
| Physical readout | Known numerical A, known structured class, or arbitrary unknown map? Do not conflate these. |
| Report association | Which request identifiers, delivery channels, times, order relations and capture boundaries are public? |
| Persistence | What stays fixed across probes: binding, source parameters, queue rules? Which jitter is sampled anew, and with what law/bound? |
| Joint observations | Is a common-state vector actually observed, or does the learner have to establish it from raw history? |
| Excitation | Passive record only, or actively chosen inputs? Which input words are safely feasible? |
| Memory and time | Supplied delay/queue/state ceiling, known distinguishing bound, or unbounded uncertainty? |
| Query access | Reset/drain/serialization allowed? Their time and physical costs must be included. |
| Objective | Exact mechanism, operational signal, finite-horizon mission decisions, or full future trace equivalence? |

## Tentative residual, and tests that may collapse it

The defensible candidate is **a structured, safely executable, costed acquisition construction that replaces a trusted raw-report-to-joint-record premise and then enables an interacting mission**. This is not yet a new theorem. The local prior finite-signature theorem may already cover its abstract existence.

1. First try legal single-outstanding-request serialization plus draining. If it gives binding within budget, the problem reduces to the tagged result; acknowledge this rather than prohibiting the experiment for the lower bound.
2. Next try known-map unlabeled/homomorphic sensing. If a common-state vector and robust separating design are already available, anonymous binding may be a standard inverse problem.
3. Next try callback trace learning under certified quiescence and a small distinguisher bound. Charge the physical realization of every query, not merely the number of queries.
4. Only then isolate a residual: e.g. safe scheduling plus anonymous persistent queues where useful local joint records can be certified within a deadline, without full binding recovery or a full-state search. This is a possible construction target, not a claimed literature gap.
5. A matched obstruction must quantify over **all** legal probes, timing, serialization and correlations under the same raw observation map. Different hidden descriptions are insufficient: two indistinguishable persistent worlds must require conflicting mission decisions. Conversely, unresolved labels are harmless if a common safe useful controller exists.

**Stopping conclusion:** strongest currently justified result is a baseline map and a candidate acquisition premise to investigate. No source-pairing novelty, unknown-delay novelty, generic new framework, or universal absence-of-prior-work claim is supported by this bounded pass.
