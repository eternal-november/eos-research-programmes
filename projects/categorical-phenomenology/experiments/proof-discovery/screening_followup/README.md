# Fresh-family screening follow-up

This is a second, explicitly exploratory experiment designed after the initial list-theory result. Its new 100-positive/20-negative workload, sample size, seeds, and algorithm were hashed before this follow-up's first run. It is not externally preregistered and not a new mathematical benchmark.

Question: can cheaper finite counterexample screening improve total proof-search cost when the same optimization is granted to the strongest ordinary-completion baseline?

Answer in this fixed implementation: it lowers the unweighted operation proxy but **increases actual CPU and wall time**. The smaller screen admits 288 extra false candidates, which lead to many failed proof attempts. All these candidates have independently saved counterexamples. The final learned libraries and the held-out proof certificates are exactly the same across screen sizes, isolating an acquisition-cost tradeoff rather than a difference in mathematical capability.

Read `RESULTS.md` for actual values and censoring. The original failure-guidance result is not replaced or retuned.

## Reproduce

Run from this folder, with the original parent experiment source beside it:

```sh
python followup.py
python audit_followup.py
python measure_randomized.py
```

Do not run `--freeze` to reproduce: the included workload and hashes are the frozen inputs. `followup.py` checks its frozen source/workload hashes. The audit and randomized measurement also check imported parent sources against `../FINAL_SOURCE_SHA256.txt`.

## Design

Both variants retain the same full-completion algorithm, training target, candidate grammar, and proof checker. The ordinary and failure-guided ordering each get either all 343 original finite assignments or eight assignments sampled without replacement using seed 20261103. No outcome-dependent choice of sample size or seed was made.

The new target generator uses seed 20261104. Each positive left side contains reverse, at least two list variables, and 9–23 AST nodes. Its right side is built by a human-written concatenation/reversal normal form. Thus labels deliberately encode familiar list algebra; this is not independent discovery of semantics or of an unknown structural representation. Every target exceeds the discovery grammar's five-node bound. The held-out file is opened only after library acquisition has completed.

The twenty negatives replace one variable on the right with a fresh W. Each has a concrete length counterexample. They are deliberately easy soundness tripwires, not broad tests of false-conjecture discrimination. The shuffled order is fixed. Under a cap, only reached negatives count as rejected; zero false acceptances before reaching any test is vacuous.

The initial operation caps are 100k, 250k, and 1m. An observed proxy/CPU disagreement motivated an explicitly recorded measurement extension: all four methods to completion under a finite 10m cap, plus equal CPU caps. A fixed-order timing pilot is retained. The final report uses five randomized complete-run blocks and three randomized blocks at each of 0.5, 0.8, and 1.5 CPU seconds, with order seed 20261105. Trials run serially in the same Python/container environment. Actual hardware/software information, run order, variance, and cap overruns are saved.

The inherited operation proxy is not hardware work. Atomic kernel checking may run just before a rejected cost charge. The ledger shows one initial capped case with 852 performed but uncharged kernel ticks: guided/all343 records 999,158 charged ticks but executed 1,000,010 including that final check; its uncharged proof was not counted successful. Completed comparisons have no overflow. Actual CPU usage is always reported for soft CPU caps. Timings exclude the additional redundant final proof-bundle replay, but include every acceptance check used by search.

## Scope

This is evidence about a specific screening/proof-search implementation in one elementary theory. It supports checking actual end-to-end computation rather than treating an unweighted operation count as speed. It does not show that all reduced screens are bad, that failure guidance never helps, or that any new categorical, phenomenological, or mathematical mechanism has been established. A stronger adaptive counterexample policy could behave differently; no such further tuning was done here.
