# COPS as a matched cave-planning reduction check

**I2 development, not independent acceptance.** The pinned upstream
COPS flow formulation, a separate discrete-state planner, and the
shared admission checker agree on the stated fixture. A common staging
move and a timely local cue permit a joint recovery; although each
known world is solvable on its own without staging, those solutions
cannot be selected before the local distinction arrives.

[Scope and derivation](Cave_COPS_Reduction.tex) ·
[Development fixture freeze](FREEZE.txt) · [Lean kernels](Cut.lean).

Use Python 3.10+ with SciPy and NumPy, Git, and a C++17 compiler. Obtain
the five exact source files in SOURCE.tsv from
[COPS at 67d2e5d](https://github.com/FilipKlaesson/cops/tree/67d2e5dd4534b3f3eec95b6cfda9d4c9c1746ef0).
The adapter supports only the flow solver on this fixture and replaces
the numerical backend with SciPy HiGHS; no Gurobi or Mosek account is
needed. Upstream SubT input layout appears in
[the timed source producer](../../subt-relay-debit/pending-scope/timed-source-producer/README.md).

    R=/path/to/eos-research-programmes/projects/swarm-coordination/research
    sh replay.sh /path/to/cops "$R/integration/shared-admission-core" \
      /path/to/subt-source-parent \
      "$R/integration/subt-relay-debit/pending-scope/timed-source-producer" \
      | cmp expected.json -

The geometry and sensor semantics are authored. The executable portion
does not run TRACE, field motion, the whole COPS package, or a complete
ACHORD deployment. No held-out mission was used.
