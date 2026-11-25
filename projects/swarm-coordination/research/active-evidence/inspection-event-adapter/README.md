# Source-parameterized inspection event simulator

This implementation uses a directed node/edge layout, positive integer
action durations, finite declared physical worlds and one active crew after
reports are already stored. Entries are abstract time units until the geometry
and communications source supply a calibration. The original #376 fixture is
the authored development instance, not a separately selected mine.

```sh
python3 -B run.py base_fixture.json --traces
python3 -B checks.py | cmp replay.txt
python3 -B reference.py | cmp reference.txt
python3 -B event_audit.py | cmp event-audit.txt
python3 -B parallel_slice.py | cmp parallel.txt
```

- State and event rules: [technical note](Mission_Event_Adapter.tex).
- The optional `local_visibility` field reveals a currently open local arc,
  not its availability for the whole transit. Movement failures do not count
  as successful arrival and invalidate the tested mission.
- `signals` exposes only fields configured at the reached probe. A value may
  be constant or a sorted list of `[effective_tick, value]` pairs, sampled at
  acquisition completion after that boundary's source events.
- `stock` and `absent_stock` define actual copies available before the modeled
  stage. Route guards may separately require actual delivery or observed
  acknowledgment at the destination transition. Sinks are the fixed base.
- `resources` and `needs` name physical shared failure dependencies.
  `shared_capacity` and slot `band_use` name shared reservable forwarding
  capacity. A probe can divert named slots throughout later physical use, or
  release its own reservation on successful departure.
- `arcs_down`, `slots_down`, `radio_down`, `probes_down`, and
  `coupled_resources_down` hold half-open outage intervals. Invalid declared
  source identifiers are rejected in ordinary (non-optimized) Python mode.
- Duration and availability are checked independently at each action.
  Actual delivery and visible acknowledgments are separate state. The final
  evaluator, not the controller, reads the hidden source index.
- `lake env lean EventWindow.lean` uses Mathlib in Lean 4.35.0 for two
  kernel lemmas on checked event overlap.

The solver is exact on the supplied finite model, not a guarantee of physical
radio or multi-vehicle motion. A separate independently selected input and
source calibration are still needed.

`parallel_slice.py` is a restricted two-crew check with independent local histories and one optional scoped transfer of probe evidence. It checks real overlap with a different crew’s forwarding interval; it is not a general multi-agent planner.
