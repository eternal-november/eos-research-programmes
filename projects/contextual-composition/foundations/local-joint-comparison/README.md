# Local comparisons for generated interference

[Local Joint Comparison and Generated Interference](Local_Joint_Comparison_and_Generated_Interference.tex) proves a rule-format fragment for monadic effect-fibre contexts and one-hole writer content. Transport-closed local admission, chooser descent when a fixed kernel is required, and native primitive/body maps construct comparisons for generated shared-state executions. The resulting joint kernel square is derived rather than assumed.

All coupling choices and dependent history witnesses are retained. The construction permits directed cells and nonserializable microstep histories; it does not flatten intermediate shared-state agreement to final-state agreement. Finite guarded preservation follows from the conditional native equations. Infinite-effect completion, arbitrary native-grade lifting, physical admission and progress remain separate obligations.

Run `python -B checks/check_local_joint_comparison.py` for exact finite diagnostics. The manuscript contains written proofs; these diagnostics are not proof-assistant certification. No TeX compilation is required.

The construction consumes [tree admission and conditional assembly](../retained-dependence/README.md), [joint occurrence bodies](../joint-occurrence-unfolding/README.md), and [retained-fibre guarded prefixes](../retained-fibre-effects/README.md). Its generated-kernel corollary supplies one hypothesis of the [information-and-progress comparison](../../feedback-and-concurrency/information-and-progress/README.md); the remaining information, task and goal conditions are retained.
