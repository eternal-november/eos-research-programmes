# Frozen partial-acquisition diagnostic

This is a model-side checking diagnostic, not a physical robot mission or a
physically validated acquisition protocol. It supplements the constructed OR/XOR
family with arbitrary essential binary truth tables and unresolved local scopes.

## Frozen protocol

`partial_acquisition_config.json` was written before outcomes. It fixes 24 seeds
202610292200 through 202610292223, four command ports, four response channels,
maximum run memory three, and a chain of pair-sum diagnostics. True functions use
uniformly sampled distinct port pairs, thresholds two or three, and one of all
ten essential two-input Boolean tables. The learner starts with all canonical
zero-, one- and two-port functions with thresholds one through three; it is not
given the true scopes, thresholds or tables.

Three all-off ticks establish the observer. Twelve public predetermined command
vectors, each with at most two active ports, generate causal counter histories.
After each tick, one rotating chain-edge aggregate is observed. No individual
response is read in this initial acquisition.

For each seed, all eleven public held-command patterns with at most two active
ports are combined with preparation lengths one, two and three and each of the
three diagnostic edges: 99 scenarios per seed. Each scenario is a separate
continuation of the same base evidence, not one sequential robot run. Preparation
produces its actual counter trace; the current edge sum is then acquired. The
checker considers every possible individual diagnostic outcome for the first
endpoint and asks whether some endpoint can be chosen with response one at every
one of the next 43 held-command ticks.

The exact checker preserves persistent functions and every aggregate relation.
The rectangular baseline receives precisely the same arc-consistent local
domains after the aggregate, but discards relations before the individual
observation. It is therefore a sound information-losing comparison, not an
information-equivalent optimum. The engine's separate exhaustive tests compare
against the latter.

## Measured outcome

Out of 2,376 fixed scenarios:

- Exact relational checking succeeds for every diagnostic branch in 874.
- The same-domain rectangular comparison succeeds in 373.
- There are 501 exact-only successes and zero rectangular-only successes.
- Neither succeeds in 1,502.
- Exact-only successes occur in all 24 seeds.
- No selected endpoint violates the 43-step tail in independent actual-truth
  scoring. The stronger claim is the exact universal check over surviving worlds,
  not merely this truth replay.

Every exact-only success retains more than two candidate functions, more than
one essential scope, unresolved threshold assignments, and more than two arity/
truth-table alternatives at at least one endpoint. This is not merely an unknown
single OR/XOR bit in an otherwise identified response.

Important limit: 481 of the 501 exact-only successes have already-stable counter
contexts during the tail. Twenty have a changing context; independent truth
scoring finds an actual response change at an endpoint in only two of those
20 cases. Thus the strongest supported conclusion is about coherent checking
under incomplete, coupled knowledge. These counts do not establish general
online dynamic planning, mission completion or large-scale discovery.

## Reproduction and verification

Run `python partial_acquisition_probe.py` to replay the unchanged frozen
configuration. Results include all generator truth (for audit only), every
acquisition record and scenario, exact and rectangular branch decisions, retained
interface ambiguity and source hashes. The script does not use truth for proof
queries or endpoint selection; it uses it only for delivered observations and
independent scoring.

Run `python partial_acquisition_reference_check.py` for an additional small
exhaustive reference with two ports, memory two, three responses and 125,000
complete persistent worlds. That enumeration belongs only to the test oracle.
