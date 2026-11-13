# Small sequential mission diagnostic: a negative comparison

This diagnostic compiles an actual three-leg, all-observation-branch policy tree.
It does not just check three independently successful jobs. One coherent knowledge
state, causal command memory, elapsed time and energy account persist across the
whole policy. The experiment is a controlled finite-grammar test, not the growing
family's primary result and not an unrestricted controller optimality theorem.

## Frozen primary experiment

The 24 original generic truth seeds and their twelve paid aggregate-acquisition
records are reused. Both ascending and reversed orders of edge tasks `(0,1)`,
`(1,2)`, `(2,3)` give 48 roots. No additional aggregate observation is allowed.
At each leg the compiler chooses a held command pattern with at most two active
ports and preparation length one to three ticks. It then pays one more tick for
an individual diagnostic of the first endpoint; command counters advance during
that tick. Every feasible diagnostic outcome must have a certified continuation.
The branch may choose either endpoint only when its response is provably high at
every tick of the next complete passage.

Even-index endpoints correspond to ten metres and 43 quarter-second ticks;
odd-index endpoints to twelve metres and 51 ticks. These durations are consistent
with the separate fast-option premise: acceleration to 1 m/s at 1 m/s^2, braking
at 2 m/s^2, and cruise over the remaining distance. The compiler itself checks
Boolean envelope guards and resources; physical access and motion validation
belong to the separate integration/replay layer.

The absolute deadline is 180 ticks and energy budget 450. Costs include the
three initialization ticks, twelve acquisition ticks, transfer, preparation,
diagnostics and movement. Actuator-command energy is one unit per active port
per tick; a passage also costs its distance in metres as travel-energy units.
These are declared abstract accounting units, not calibrated battery joules.

## Transfer correction and preserved provenance

The initial frozen config used an explicitly abstract one-tick transfer. That
run is preserved in `sequential_mission_results.json`; its exact original source
is `sequential_mission_compiler_v1.py`.

Before the corrected run, `sequential_mission_corrected_config.json` fixed the
transfer at ten quarter-second ticks: one metre at coarse-safe 0.5 m/s with
acceleration/deceleration 1 m/s^2 takes 2.5 seconds. Seeds, tasks, deadline, energy
and option grammar remained unchanged. Corrected outputs use the
`sequential_mission_corrected` prefix. No result was silently substituted.

## Measured result

Both original and corrected runs certify 12 of the 48 roots with exact relational
knowledge and the same 12 with the rectangular baseline. There is **no relational
completion advantage** in this generic sequential experiment. The other 36 roots
produce explicit safe stopped abstention, not a success claim.

All corrected certified trees complete in at most 168 ticks including acquisition
and transfer. Their 48 combined exact/rectangular terminal leaves pass independent
recursive certificate replay, and actual-world replay has zero guard violations.
This remains conditional on the structural and safe-option premises.

The initial structural class includes an all-zero-response world. A separately
frozen negative test performs the paid acquisition and ten-tick safe transfer,
then correctly refuses both mission orders and commands no mission movement.
Safe acquisition therefore does not imply universal goal completion. Refusal is
safe but counts as mission failure. The negative establishes refusal in this
option grammar, not impossibility for every physically conceivable controller.

## Post-result exact cost diagnosis

A separately recorded exploratory analysis uses the same 48 roots and grammar.
For each root it checks the public maximum possible grammar duration (190 ticks)
and binary-searches the integer deadline. Success is checked at the resulting
minimum and failure one tick below it. The public worst-case energy bound for any
grammar policy is 385, below 450, so energy does not hide a time comparison here.

The same twelve roots have exact minimum certified worst-case time **168 ticks
for both methods**. The remaining 36 have no policy even at the grammar's maximum
duration, rather than merely failing the original 180-tick horizon. There is no
exact-only feasibility or time advantage. This exploratory result is not a new
confirmatory benchmark win.

The per-leg individual diagnostic and this option grammar may make retained
relations operationally unnecessary on these particular roots. Equality of these
48 results is not a theorem that correlations never help sequential missions;
the separate constructed family addresses a different, explicit mechanism.

## Reproduction

- `python sequential_mission_compiler_v1.py`: original abstract-transfer run.
- `python sequential_mission_compiler.py --config sequential_mission_corrected_config.json --output-prefix sequential_mission_corrected`: corrected primary run.
- `python sequential_mission_negative_check.py`: all-zero safe refusal.
- `python sequential_mission_cost_diagnostic.py`: exploratory exact cost frontier.

The cost diagnostic verifies its input result hash. Since rerunning the primary
changes wall-clock metadata, use the frozen result for that exact receipt or
explicitly regenerate the diagnostic receipt without changing the root records,
seeds or scientific settings. No claim depends on the measured execution time.
