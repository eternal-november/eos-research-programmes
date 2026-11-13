# Native trace and resource transport

## Main findings

1. Interface coarsening preserves sequential weighted-language convolution, choice, and finite iteration. It generally does not preserve synchronous parallel composition.
2. With scalar nonnegative integer costs, equality of local-first and joint-first costs holds exactly when local optimal native traces have a common concrete interface trace.
3. Unbounded feasibility can agree for every visible word while resource mismatch grows linearly without bound. The supplied example uses two deterministic one-state loop machines, not a path diamond.
4. Exactness against every native exact-word tester is equivalent to the entire concrete cost profile being constant on each interface fiber. Support saturation is insufficient.
5. Common native canonical edge replacements with identical actual endpoints and no larger costs give constructive exactness at every trace length. Min-plus one-step matrices provide exact finite certificates for endpointwise canonical optimality and universal resource transparency.

## Files

- `trace_resource_transport.tex`: self-contained note with definitions, theorem proofs, examples, constructive class, vector resources, computational extraction, and explicit limitations.
- `check_trace_resource_transport.py`: dependency-free executable checks and actual native path extraction.
- `check_results.json`: saved successful run, including native edge histories and the resource-gap family.
- `WORKING_NOTES.md`: incremental research checkpoint.
- `tmp/pdfs/compile1.txt`: PDF build failure record. The installed `pdflatex` lacks its format file and its format configuration has no pdflatex entry. No PDF was produced or visually verified. The TeX source is the deliverable.

## Verification

Run `python check_trace_resource_transport.py`. The initial successful run checked 85,219 scalar profile combinations, 4,096 universal-partner combinations, and 480 sequential convolution values. It also checked the gap family and positive canonical class through trace length 20 and extracted concrete native runs.

## Scope

The native graph edges must be controllably selectable, certified, terminating executions from the actual current state. This is open-loop finite-run planning with exact tables, not empirical identification or sure winning under adversarial outcomes. Synchronous composition assumes independent component resources and a common concrete event clock. Macro costs, residual endpoints, and controller overhead must be represented or separately certified. The results do not claim historical novelty for weighted-automaton, min-plus, or direct-image algebra.

## Source relation

The note was developed against the recovered `native_operations_across_doctrines.tex`, `contextual_reduction_wiring.tex`, `common_generation_note.tex`, and `adaptive_experiment_formation.tex`. It adds a cost-sensitive synchronization obstruction even when every Boolean trace lifts, and a comparison between two different composition operators under the same interface change.
