# Physical replacement counterexample — 23:20 UTC

Root identified the flaw; independent executable reproduction confirmed it on source `7a61958ea028d73707d5a9d1f4d95d01e5392f0769619997b713a953ccea0823`.

Replace row0 by A[0]=[0,.5,0,0,0], B[0]=[0,0,.25,0,0]. Keep the other learned rows, source law, windows and budget. On held backgrounds d=[1,.5,.5,.5,.5] and all-positive source signs, the local controller admits u=[0,1,1,1,1]. Local and coherent checkers both accept (bound .04418327348); second-slot load x0=1+.5+.25=1.75 exceeds1.5. Thus nonnegative total row<=.75 is insufficient for the controller's per-zone admission proof when physical influence is moved off the diagonal. This does not affect frozen generated A=.5I/B-cycle results, but invalidates a general physical replacement acceptance claim.

Sufficient correction under the declared held-background, two-slot-job regime:

* nonnegative coefficients;
* total row sum<=.75;
* off-diagonal sum `sum_{j != i}(A_ij+B_ij)<=.5`.

On the all-good event, if stage i is accepted then d_i<=.75, so every slot and tail are bounded by d_i+total<=1.5. If stage i is refused then its command is zero throughout; d_i<=1 and external contribution<=.5 suffice. Tail subsets cannot increase a nonnegative convolution. This proof allows arbitrary admission patterns and independently varying d_i. Alternatively, requiring the canonical A=.5I/B single-cycle template is sufficient but narrower.

Both checkers need the same physical predicate and an explicit unsafe-redistribution regression. Main acquisition results need not be rerun; final code/regression and independently checked invariant need re-audit. Status at report creation: fix pending.

## Resolved at23:22 UTC

Repaired source SHA256 `a25f7d71574407ce12c5e86020806ea41d79166a782688e38bf10cffd4cf09ec` applies a stronger sufficient guard in both checkers: external-current A plus ALL lag B<=.5, alongside total<=.75. This covers arbitrary prior command histories for inactive/stop states. Independent no-import `independent_guard_audit.py` verified48 admissible n3 coefficient rows times64 present/past patterns (3,072 checks), plus12 actual split FIFO traces; all passed. Rerun author regression rejected the counterexample and rechecked120 saved decisions unchanged. Full acquisition artifact replay still passes; no acquisition rerun was made. Main result hash remains `15580b6a2d1c52abf101a6a253183e2d80321bfd72fffa84fc03d703d27e4021`.
