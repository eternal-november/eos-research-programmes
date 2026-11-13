# Actual screening-follow-up results

The new workload was frozen before this follow-up ran, but designed after the initial experiment. All results are exploratory. There are 100 positive equations and 20 easy negative controls. No source, candidate sample, or theorem was changed after outcomes. Additional timing plans are disclosed separately.

## Same completed workload, randomized blocks

| Ordering | Screen assignments | Positives /100 | Negative controls /20 | Total proxy | Acquisition proxy | Median CPU s | CPU range s | Median wall s |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| generic | 343 | 100 | 20 | 1,047,568 | 758,014 | 0.583523 | 0.540038–0.609159 | 0.583519 |
| guided | 343 | 100 | 20 | 1,058,014 | 777,399 | 0.605846 | 0.585557–0.636280 | 0.605879 |
| generic | 8 | 100 | 20 | 891,700 | 602,146 | 0.793906 | 0.715401–0.833709 | 0.793938 |
| guided | 8 | 100 | 20 | 995,861 | 715,246 | 0.868653 | 0.739158–0.987396 | 0.868695 |

All five repetitions of every variant completed under the same 10m proxy cap. None accepted a false control. Each accepted statement has a replayed certificate. Comparisons above process exactly the same workload.

- generic: screen reduction lowers the total proxy by 14.88%, but the paired median CPU ratio is 1.361 (slower by 36.1%). Every repetition is slower, with ratios 1.298–1.450.
- guided: screen reduction lowers the total proxy by 5.87%, but the paired median CPU ratio is 1.442 (slower by 44.2%). Every repetition is slower, with ratios 1.262–1.598.

These are descriptive measurements of this code, not a general timing law or a significance claim. Ordering comparisons are more variable: some equal-CPU-cap runs favor guidance. The robust finding here is the screen-size/proxy disagreement, not a universal ranking of guidance versus ordinary completion.

## Equal operation caps

| Cap | Ordering | Assignments | Positive successes | Negative controls reached/rejected | False acceptances | Status |
|---|---|---:|---:|---:|---:|---|
| 100,000 | generic | 343 | 0 | 0 | 0 | budget_exhausted |
| 100,000 | guided | 343 | 0 | 0 | 0 | budget_exhausted |
| 100,000 | generic | 8 | 0 | 0 | 0 | budget_exhausted |
| 100,000 | guided | 8 | 0 | 0 | 0 | budget_exhausted |
| 250,000 | generic | 343 | 0 | 0 | 0 | budget_exhausted |
| 250,000 | guided | 343 | 0 | 0 | 0 | budget_exhausted |
| 250,000 | generic | 8 | 0 | 0 | 0 | budget_exhausted |
| 250,000 | guided | 8 | 0 | 0 | 0 | budget_exhausted |
| 1,000,000 | generic | 343 | 83 | 15 | 0 | budget_exhausted |
| 1,000,000 | guided | 343 | 81 | 15 | 0 | budget_exhausted |
| 1,000,000 | generic | 8 | 100 | 20 | 0 | complete |
| 1,000,000 | guided | 8 | 100 | 20 | 0 | complete |

At 100k and 250k, no variant reaches the held-out workload. Zero false positives there conveys no negative-control evidence. At 1m, the smaller screen wins by the operation proxy but takes more actual CPU time; the incomplete full-screen runs are not treated as equivalent completed workloads. The guided 343 run performs 852 uncharged terminal kernel ticks, for 1,000,010 executed proxy ticks rather than 999,158 charged ticks. Its terminal proof is not counted.

## Equal CPU caps, three randomized blocks

| CPU allowance | Ordering | Assignments | Positive successes per repetition | Negative controls reached per repetition |
|---|---|---:|---|---|
| 0.5s | generic | 343 | 33, 59, 55 | 5, 11, 9 |
| 0.5s | guided | 343 | 75, 100, 65 | 12, 20, 11 |
| 0.5s | generic | 8 | 0, 0, 0 | 0, 0, 0 |
| 0.5s | guided | 8 | 0, 0, 0 | 0, 0, 0 |
| 0.8s | generic | 343 | 100, 100, 100 | 20, 20, 20 |
| 0.8s | guided | 343 | 100, 100, 100 | 20, 20, 20 |
| 0.8s | generic | 8 | 100, 100, 100 | 20, 20, 20 |
| 0.8s | guided | 8 | 100, 100, 100 | 20, 20, 20 |
| 1.5s | generic | 343 | 100, 100, 100 | 20, 20, 20 |
| 1.5s | guided | 343 | 100, 100, 100 | 20, 20, 20 |
| 1.5s | generic | 8 | 100, 100, 100 | 20, 20, 20 |
| 1.5s | guided | 8 | 100, 100, 100 | 20, 20, 20 |

The 0.5s cap shows why the proxy alone is misleading: full screening reaches positive targets, while reduced screening is still acquiring its library. At 0.8s and 1.5s every variant finishes. CPU caps are soft; actual times, overrun, environment, and randomized order are in results/timing_randomized_*.json.

## Why the proxy changes

- Full screening proposes 416 equations; the eight-assignment screen proposes 704. All 288 additions have explicit finite counterexamples, saved in followup_audit.json.
- Finite-evaluation calls fall from 487,060 to 11,360. But acquisition proof-attempt calls rise from 228 to 1,092 for ordinary ordering, and from 182 to 1,046 for guided ordering. This includes unsuccessful and repeated attempts.
- Within each ordering, the final library statements/certificates and all 100 positive target certificates are byte-identical across screen sizes. Test-phase operation costs are also identical. The changed work is acquisition, not stronger transferred knowledge.
- All 16 emitted bundles replay under the unchanged checker. All 20 negative controls have verified concrete counterexamples. These weak controls do not establish broad false-conjecture detection.

## Conclusion

The original experiment demonstrates checked reuse of an unsupplied intermediate law, but not a distinctive advantage of failure-guided discovery. This separate follow-up shows that a plausible cost optimization can improve an unweighted proxy while making the same proof workload slower. Both outcomes favor stronger baselines and explicit all-in accounting over attributing generic library learning to a new principle.
