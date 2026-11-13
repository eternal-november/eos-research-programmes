# 19 — Exceptions and replanning: distinguish the event, the judgment, and the obstruction

**Origin:** the user's toy environment chart L1435–1441 and the later feasibility/modal discussion L2635–2737. **Status:** corrected generalization; also incorporates the separately corrected environment table from the earlier exchange.

An “exception” is not one generic mathematical object. A reliable system model distinguishes at least these cases:

| Phenomenon | Object/judgment | Why it matters |
|---|---|---|
| Realized safety violation | \(s\notin K\) or trajectory violates \(\Phi\) | A completed bad behavior differs from failed execution |
| Failed precondition | \(x\notin D_f\) for a chosen partial command | Definedness is command-indexed |
| Explicit error result | \(f(x)=\mathrm{Err}(e)\) | Error label can support diagnosis/recovery |
| Unexpected observation | observation outside prediction or rejected by statistical test | Epistemic anomaly does not itself imply danger |
| Model-regime violation | assumptions for validity of approximate law no longer hold | A mathematical update may still exist |
| Infeasible continuation | no allowed policy/trajectory completes remaining task | Can occur *before* a deadline or safety failure |
| Policy failure under uncertainty | no common permissible action or winning strategy across information states | Must preserve observer/agent quantifiers |
| Feedback ill-posedness | no, many, or unstable solutions under a selected loop semantics | Existence, uniqueness, stability are separate |

## A precise finite-state safety example

Let \(S\) be finite, \(K\subseteq S\) safe, and \(A(s)\) enabled actions. For each \((s,a)\), let \(\mathrm{Post}(s,a)\subseteq S\) be a **nonempty** possible-successor set. Define

\[
\mathrm{CPre}(X)=\{s:\exists a\in A(s)\ [\mathrm{Post}(s,a)\subseteq X]\}.
\]

The maximal region from which a state-aware controller can keep the system in \(K\) forever is the greatest fixed point

\[
W=\nu X.\bigl(K\cap\mathrm{CPre}(X)\bigr).
\]

Here the **powerset lattice** supplies a computation on *predicates*, while the transition relation supplies the dynamics. No “lattice of states ordered by exceptionality” is needed. Under partial observability this state-aware fixed point need not implement an observation-based controller; the information-state game has to be constructed.

## Composition is not plan synthesis

Path concatenation, kernel composition, relational composition, tensor product, and sheaf gluing tell how **compatible pieces** combine. They do not select a feasible continuation or minimize an objective. A replanning interface must specify:

- what the current information/history is;
- what actions/policies are permissible;
- which effects of past execution are irreversible;
- which constraints apply to the full run or remaining horizon;
- which criterion selects among admissible continuations.

For a global ten-second deadline, two individually feasible six-second subplans are not jointly feasible; remaining time is part of the compositional interface. If a failed second step follows a first step with real side effects, a partial composite that only records “undefined” omits what replanning needs.

**Counterfactual test:** can a plan be declared locally valid in every component yet globally violate a resource, timing, synchronization, or information constraint? If so, the purported assembly theorem is missing premises.

**Related notes:** [07](07-wiring-and-open-systems.md), [08](08-restriction-categories.md), [09](09-observation-and-modal-affordances.md), [20](20-architecture-and-proof-obligations.md).
