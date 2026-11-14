# Native feedback and shared content: first results

**Status:** independently reviewed written mathematics for explicitly restricted constructions. No historical novelty claim, Lean certification, general O1 extension, or completion of the feedback/concurrency contract is claimed.

## Read this first

The main result is not a new list of applications. It is a concrete retained-witness construction, an exact failure of an overly weak feedback comparison, and two ways of making feedback comparisons sound.

1. **Actual native composition:** causal probability kernels, deterministic bodies and witness maps form category-valued homs with retained relative composition. Nonterminal writer-style histories have explicit content maps, and an independently constructed unary context/content crossing accounts for their composition.
2. **Feedback boundary:** a pointwise body square and probability preservation for each fixed input do not suffice under continuous delayed feedback, even for invertible raw witness maps. A null diagonal selected by feedback changes the closed law.
3. **Positive feedback results:** countably many finite control histories suffice for constant tape laws, even correlated tapes. A stronger all-history innovation condition handles a declared continuous-control class. Seeded delayed feedback preserves the actual writer content and satisfies the proved scoped laws; yanking gives delay, not identity.
4. **Shared content without copying the world:** a fiber product over one world-event graph retains event witnesses and has coherent content maps. A common-event-law condition gives an explicit conditionally independent probability gluing and native path maps. All-state/all-command transport also makes that shared construction sound under a shared world-history controller, including uncountable commands.
5. **Boundary and progress certificates:** native content maps transport stable resumption assertions; exact transport requires reachable-state lifting. Conditional progress theorems retain interference, repair charges and fairness. Probability-based response bounds are separate from universal raw-path response.

The gluing chooses conditional independence of private lifts given the world event. It is not inferred from their marginals and cannot replace an actual correlated joint law without justification. Writer logs alone do not act on later state: the changed world/capability interface must be carried by the returned interface or a separately proved action.

## Files

- `Native_Feedback_and_Shared_Content_First_Results.tex`: integrated source with a theorem/scope roadmap and all proof chapters.
- `THEOREM_LEDGER.md`: result-by-result hypotheses and remaining contract gaps.
- `checks/check_native_constructions.py`: exact finite regression diagnostics.
- `checks/results.json`: recorded diagnostic results.
- `checks/check_sources.py`: balanced-environment, label/reference and local-link checks.
- `MANIFEST.sha256`: integrity hashes, not proof evidence.

Run diagnostics with `python3 checks/check_native_constructions.py` from this directory. They test finite instances and discriminators, not the general measurable proofs. No TeX compilation or rendered layout verification is claimed.

The TeX source is self-contained; it does not depend on external chapter files.

## Scope that must not be widened

- Unary writer content is not arbitrary polynomial branching or an arbitrary contextad/contentad pair.
- Seeded delayed feedback is not an ordinary total trace; no unrestricted stateful sliding law is proved.
- A full retained-history square is not supplied by equality of public output streams.
- Shared-world stochastic grades have a common world-event law at every component state. Arbitrary private-state-dependent controllers need not satisfy it.
- Raw zero-probability behavior is retained separately from probability laws. Positive-probability lift availability is not all-edge availability.
- Operational adequacy for an external controller/plant, a complete recursive/concurrent language, and general scheduler-aware contextual refinement are not established.
- The motivating robot/BFT applications are not implemented or discharged by these abstract results.

## Source relationship

The existing project uses native comma objects `(P,Q,f:e_A P -> d_B Q)` and native context/content squares. The new unary family constructs those data directly, rather than applying the finite-witness O1 theorem to infinite carriers. The Set-level writer content satisfies the unary `T = Id` content conditions of `interaction/independent-criterion/General_Independent_Interaction_Criterion.tex`; the kernel context extension and feedback results require the new proofs here.
