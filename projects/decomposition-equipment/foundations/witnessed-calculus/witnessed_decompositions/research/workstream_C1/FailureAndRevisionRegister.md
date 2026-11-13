# C1 failure and revision register

Contract and frozen target unchanged. Failed attempts and corrections are
retained; none constitutes a permitted negative branch (C1 is M positive-only).

1. **P wording correction, not theorem weakening.** Initial proof hash
   `2c0ea86e57c5ef5aedfcd2ae03dd2fb044e4222bbd196c5101124d1736f3d07f`, retained
   as `history/C1_Model_Theorem_initial.md`, called a signature finite under
   arbitrary small K. Construction remains valid for small K; finiteness was
   corrected to require finite K, exactly the original target parameter.
   The author and nonauthor reviewer independently identified this wording.
2. **Evidence-status correction.** Initial §8 heading said independently
   checked before L/C reviews finished. Reviewer requested prospective wording;
   it now says for independent checking. No independent result was established
   by the heading. Added exact `Path.slotExpand_assoc` citation for slot transport.
3. **Mutation test strength.** Initial C code recorded arrow/empty-block
   property contrasts rather than executing each weakened implementation.
   Concrete mutant validators were added after author integration and reviewer
   criticism. First source/result/log remain under `finite/history` and
   `finite/author_run_01.log`; they are not final mutation evidence.

4. **Equal-entry wording correction.** Reviewer noted that permuting two equal
   empty entries does not change a tuple. §1 now explicitly distinguishes
   retained empty-block positions from occurrence indices: equal entries do not
   create artificial witness multiplicity. The defined carrier/proofs did not
   change; this prevents accidental over-refinement in the prose.

5. **Lean elaboration and adapter audit history.** `evidence/lean/attempt01.log`
   through `attempt08.log` retain author elaboration repairs. Exact adapter
   pre-review bytes and the sorted-list induction precision repair are recorded
   in `lean/Revision_Record.md`. No claim or target was weakened.
6. **Independent negative-test diagnostic matcher.** The first reviewer
   harness incorrectly classified two intended `decide`-false rejections as
   unexpected because it looked only for type-mismatch wording. Initial
   records are preserved in `review/lean_independent`; corrected exact
   diagnostic checks pass all six probes. This was a test matcher issue, not
   an accepted invalid graph or arrow.
7. **Clean-stage command setup.** Initial attempt named its not-yet-created
   working directory, so process creation failed before executing any command.
   Retried from the existing parent directory after creating the clean stage;
   no restricted action or mathematical test had run in that failed setup.

Any later elaboration failures, negative controls or substantive defects are
appended or linked here before final delivery. Baseline A/B failure records
remain unchanged in their original locations.
