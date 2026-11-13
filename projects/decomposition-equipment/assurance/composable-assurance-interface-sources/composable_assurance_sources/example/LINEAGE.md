# Final data/code lineage

Final source/results frozen29 October2026 at23:12:45UTC; exact SHA256 identifiers in `FINAL_MANIFEST.json`. Frozen case specification `PROTOCOL.md` predates first outcome run. No seed, sample-count, confidence-allocation or acceptance-threshold selection was performed after observing outcomes.

Development reruns were made while implementing this prototype. They are not independent replication evidence and their simulated acquisition costs are not included in the final per-protocol acquisition totals. Earlier transient overwritten files were not all archived; do not imply a complete immutable development audit trail. Corrections were:

1. Replace algebraic two-request queue outputs with explicit causal FIFO service recurrence and record/verify changed polling trace.
2. Represent averaged reference error by two independent bounded sample errors rather than a single bounded averaged-error fixture; the interval argument already used only the common bound.
3. Retain exact decoded observation NPZ and record RNG state/full residual hash; add separate exact regeneration audit.
4. Replace diagnostic fixed legal +e noise realization with sampled width-averaged binomial packet noise. This consumes additional RNG draws before calibration and can change reported rate intervals by tiny amounts. This was a model-faithfulness correction, not selection for favorable results; all frozen seeds were rerun.
5. Correct checker operation reporting from interface-size proxies to executed row/incidence counts. Add explicit native coefficient/width/capture validation to the cached path, and actual reversed polling traces. Native validation currently scans full rows, so the cache result is not a local-cost advantage.

The main result snapshot immediately before the final native-validation/replacement-trace correction is retained as `results/results_v1_before_replacement_validation.json`. Final acquisition numbers use only `results/results.json`. Final supplemental regressions load those saved interfaces without resampling. Expected accepted/refused capability outcomes were unchanged by the corrections, but exact numbers should always be read from the final snapshot.

Calibration observations are exact decoded packet-minus-physical-reference categories, not primitive noise measurements. NPZ is lossless. Full packet and reference residuals are reproducible using recorded NumPy generator state, version, source-generation code and world seed/family; `replay_observations.py` verifies full residual hashes and decoded matrices on all12 cases. The regeneration script is explicitly an auditor/world path, not certificate construction. All reference samples and FIFO/physical acquisition time in the vectorized idle-template schedule are charged even though only decoded observations plus a lossless regeneration recipe are retained.

## Post-freeze semantic guard repair (23:20 UTC)
Root found that the old replacement validator checked only total influence<=.75. That condition does not protect an inactive zone with background1 against external actuation: off-diagonal current .5 plus lag .25 yields1.75. This defect affected admissibility of previously untested replacement structures, not the canonical learned diagonal-current family.

The previous source is preserved byte-for-byte as `versions/experiment_before_inactive_guard.py` (the original FINAL_MANIFEST hash). Both checkers now additionally require external-current influence plus **all** lag influence<=.5. With nonnegative coefficients, background in[0,1], all-good own admission d_i<=.75, and initially idle commands, the active/inactive/tail bounds are sound. This is a sufficient guard, not maximal replacement permissiveness.

No acquisition or primary outcome run was repeated. Supplemental `physical_guard_regression.py` exhibits the old1.75 counterexample, rejects it in both repaired checkers, checks12,500 canonical boundary trajectories, and rechecks all120 frozen decisions unchanged. Updated source/supplement hashes are in `SEMANTIC_GUARD_REPAIR_MANIFEST.json`; `FINAL_MANIFEST.json` intentionally preserves the earlier frozen acquisition/source lineage. The primary results hash remains unchanged. Thus claims of unchanged source after23:12:45 apply only until this disclosed semantic repair.
