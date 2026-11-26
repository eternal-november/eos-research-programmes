# Prospective interaction

**Continuation evaluation, selection, and policy composition.** Read the [manuscript (PDF)](Prospective_Interaction.pdf) ([TeX](Prospective_Interaction.tex)). The [project navigation](../../NAVIGATION.md#prospective-evaluation-and-policy-composition) is the canonical question-to-result route; the manuscript's opening table locates its own statements.

This finite research note proves retained-cut policy evaluation, the occupancy-weighted Bellman loss identity, the evaluated-policy category `Eval(A)`, and its wide subcategories `BOpt(A)` and `Opt(A)` of boundary-optimal and all-history-optimal policies. It characterizes positive-coordinate rectangularity and gives value comparisons and exact greedy-extension fibres for independently supplied comparison data. PI-0 through PI-6, including PI-3b, distinguish scalar value equality from retained policy composition and descent.

The scope is finite, well-founded retained arenas with explicitly authorized full-history controller views, finite nonempty complete-control menus including admitted law labels, normalized fresh rows, and scalar rewards and terminal valuations. Zero-weight and off-policy histories remain policy coordinates. Cut assembly takes place within one common arena; native comparison data are supplied hypotheses. Native context/content presentations and crossings, general feedback, and model/reference revision remain open. The note does not settle whether a native proactad should be a generalization or additional structure on an existing interaction presentation.

## Reproduce and inspect

From this directory, run the exact rational diagnostics:

```sh
python3 checks/check_finite_prospective.py
```

Only the Python standard library is required. The checker rejects optimized Python mode and writes [checks/results.json](checks/results.json). It enumerates the main arena's 8,192 complete policies and checks the supplied finite obstruction, loss, cut-assembly, rectangularity, joint-law, horizon, and transport witnesses. These finite diagnostics accompany the written proofs; they are not proof-assistant certificates.

Build the manuscript with a configured LaTeX installation:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error Prospective_Interaction.tex
```

[RECONSTRUCTION.txt](RECONSTRUCTION.txt) gives the source-reading route, reuse hypotheses, and recheck triggers. [SOURCES.json](SOURCES.json) pins the cited source revisions. [VERIFICATION.txt](VERIFICATION.txt) distinguishes executed diagnostics, written-proof and source reviews, manuscript-only publication reviews, and their limits. No fresh proof-assistant verification or empirical controller validation is supplied.
