# Finite integration execution chronology

- The author wrote and submitted DOMAIN before executing any new C test.
- Domain precision revision fixed boundary probes and parameter-map families;
  no test outcome had been observed. Original bytes remain in DOMAIN.pre_review.md.
- Parent execution release was received at 01:01:45 UTC for the reviewed hash.
- AuthorRun01.log records the first full execution. Its terminal status is not
  inferred from intermediate stage messages. Any actual failure and repair
  will be appended here, with source/domain changes distinguished.

Intentional source-mutant failures are expected negative-control evidence,
not failures of the unmutated result. They are retained separately under
mutations/ with exact before/after hashes.

## Pre-final independent scope inspection and repair

At 01:07–01:08 UTC the non-author C reviewer identified two missing frozen-domain
checks: d_0 towers had been checked only at one generic component, not all four
named six-vertex occurrences plus an empty loop; Hcomp had compared flat tuples
without reifying them into raw forests. The reviewer also required mutant
failures to have the intended assertion context and the wrong-residual mutant
to remain well typed. These are implementation coverage defects, not theorem
counterexamples or reasons to narrow the domain.

AuthorRun01 was deliberately stopped at 01:08:05 UTC; the execution tool
returned terminal exit 130. It had passed named controls and T=112,785 but
was still in X. It is PARTIAL, NOT PASS. Exact prior source/log bytes are
preserved under history/pre_scope_repair/. DOMAIN remains unchanged.

Repairs cover towers at all five named occurrences (135 monoid/source/height
cases), actual canonical raw-entry forest grafting for every Hcomp pair and
named six-vertex composable pair, exact classified source-mutant assertions,
and a type-preserving wrong residual at the two identical middle components.
Memoization/precomputation of identical pure transport values was also added;
all enumerated maps/forests/assertions and actual counts remain unchanged.

## Complete arising-label coverage and consolidated preflight

AuthorRun02 was deliberately stopped at 01:14:04 UTC, terminal exit130, after
named controls and T=112785 but before X completed. The author identified and
the reviewer confirmed that the frozen phrase 'all bare labels arising in X'
required extraction from each actual nested X redex, not only the original
seven singleton prototypes. Exact source/log bytes are preserved under
history/pre_x_label_repair/. This was a finite coverage repair, not a false
mathematical theorem or an outcome-driven domain reduction.

The repair abstracts actual redex variables to identity leaves while retaining
all nonvariable labels, proves literal reinstantiation on both sides in the
checker, and uses the deduplicated union consistently for MIn and ordinary
squares. Independent and author catalogs agree at147/102/67 across Z3/E2/One.
The source/local scalar cross-product was also added to both named structural
middle splits. Separate targeted mutated-copy probes cover contextual MIn and
labelled-nullary MIn-unit cases after the ordinary mutant run's first failure.

A consolidated author/non-author DOMAIN-to-enumerator checklist and narrow
stage smoke were completed before another full run. Smoke and smoke mutations
passed; they are explicitly NOT final full-domain or mutation acceptance.
The reviewer found all identified rows resolved and recommended exact-source
replay. Parent released that replay at01:22:08 UTC. The final checker/model,
runner/probe hashes are bound in FullRunRelease.json; they will not be edited
during replay. No full PASS is inferred before all stages terminate.


## Final released execution and actual-source mutations

AuthorRun03 began at 2026-10-25T01:22:18Z on the released source bytes.
All stages terminated PASS in 893.87 seconds; terminal exit 0 was explicitly
confirmed by the execution tool at 01:38:41Z (not inferred from a partial
stage message). The six Python source hashes and frozen DOMAIN were rechecked
unchanged. `AuthorCertificate.json` records the complete executed counts and
trace digest. In particular, complete arising-label MIn=54,028, Hcomp raw
pairs=118,950, and factorization cases=27,300.

The long six-vertex brute-factorization stage was retained without optimization,
refreeze, stopping or a duplicate third full run, as directed by the parent.
A single explicitly diagnostic 100-graph prefix timing, stored separately in
DiagnosticPrefix.py/.json, estimated its throughput; it did not change any
source, domain, mathematical certificate or acceptance count. The concurrent
non-author replay used its own fresh copy and is separate evidence.

On 2026-10-25 at 01:38:41–01:38:45Z, the released verifier and final mutation
runner both exited 0. All five actual edited-source copies failed exactly at
the intended assertion/function, and the separately executed omitted-MIn and
decorated-nullary targeted probes passed. These final results are in
AuthorVerification.json/.log, MutationCertificate.json, MutationRun.log, and
mutations/. Smoke results remain labelled subsets and are not substituted for
these final executions. Only this chronology and reproduction/manifest
metadata were edited after the final source freeze.
