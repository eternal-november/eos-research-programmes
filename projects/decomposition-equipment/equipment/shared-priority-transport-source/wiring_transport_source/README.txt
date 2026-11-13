Shared priority transport proof and replay package
31 October 2026

RESULT

A polynomial certificate retains joint priority constraints when binding
anonymous callback bits to physical role parities. It can certify a four-job
case that an exact marginal-rank matching graph cannot. Safe fast/slow timing
comparisons acquire the missing shared-resource priority information; a
mission-aware strategy can stop before identifying within-role order.

The claims are conditional mathematical and executable-model results. Local
work and FIFO contracts remain grant-conditional, not unconditional isolated
wall-clock promises. The model explicitly supplies a richer fast/slow API,
atomic batch admission before dispatch, stable intrinsic work and priority,
one-sided bounded callback lag, and the physical role/load bridge. The negative
family uses its declared coarse admission grid and restricts prior information
to local/drained calibration, not all safe joint experiments. Its sharp risk
formula additionally uses one committed batch per tick. A separate weaker
bound treats repeated same-tick commits; the two-module sharp obstruction
does not survive that relaxation. No general novelty, optimality or end-to-end speedup is
claimed.

READING ORDER

1. shared_priority_transport_report.txt
   Standalone explanation of results, proofs, assumptions, costs and limits.
2. transport_theorem.md
   Full main theorem, exact poset criterion, strict comparison, refinement,
   growing local-only obstruction and mission-aware repair.
3. failure_repair_theorem.md
   Expanded failure family, probability bound, commissioning costs and legal
   serialization comparator.
4. poset_parity_validation.md
   Constructive adjacent-rank proof, checker contract, independent verification
   and exhaustive coverage.
5. relaxed_admission_bound.md
   Growing obstruction with repeated same-tick commits, including the valid
   nonsharp combined-success bound and exact hard-safe completion bound.
6. implementation_note.md
   Public observation boundary, fixed budgets, operational tests and scope.
7. mathematical_review.md and literature_baselines.md
   Mathematical scope review and bounded primary-source baseline comparison.

REPLAY

Requirements: Python 3.9 or later; standard library only. No network connection,
external data, predecessor implementation or package installation is needed.
Do not use Python's -O option: the test assertions are part of validation.

Extract the ZIP, then run from any directory:

    python3 /path/to/wiring_transport_source/reproduce.py

The runner verifies every shipped file against MANIFEST_SHA256SUMS.txt before
execution. It runs all four suites, regenerates both result JSON files in the
extracted directory, compares the JSON and reference console logs byte for byte,
checks the declared counts, reproduces the relaxed-admission JSON on standard
output, and verifies the manifest again. It writes fresh
logs and replay_summary.json in replay_output/. The command exits nonzero on
any failure. It does not modify any external service or upload any file.

Individual commands from the extracted package directory are:

    python3 poset_parity_checker.py
    python3 check_failure_repair_posets.py
    python3 check_relaxed_admission_bound.py
    python3 reference_shared_pipeline.py

The exhaustive checker test harness enumerates small instances; this test-time
enumeration is not the certificate algorithm's runtime. certify() and the
independent verifier are polynomial; their supplied test harness deliberately
uses permutation enumeration as a separate finite cross-check.

FILES AND EVIDENCE

poset_parity_checker.py
    Certificate producer and exhaustive combinatorial suite.
poset_parity_verifier.py
    Separate verifier importing nothing from the producer.
check_failure_repair_posets.py
    Independent small-instance check of uniform and fixed-payload criteria.
check_relaxed_admission_bound.py
    Exhaustive same-tick first-subset multiplicities and success probabilities.
reference_shared_pipeline.py
    Persistent shared-server simulation, safe comparison acquisition,
    mission-aware acquisition and guarded production with truth-only test
    validation kept separate from the controller's observations.
*_results.json and *_test_log.txt
    Exact reference outputs, not substitute evidence for the proofs.
PROVENANCE.json
    Per-file source and packaged hashes plus publication-only cleanup notes.
MANIFEST_SHA256SUMS.txt
    SHA-256 of every top-level package file except the manifest itself.

Finite suite coverage is detailed in the report and validation files. It
supplements the general proofs; it does not validate physical hardware,
certify elapsed execution bounds, or establish literature novelty. Simulator
budget constants represent supplied timing contracts, not Python benchmarks.
