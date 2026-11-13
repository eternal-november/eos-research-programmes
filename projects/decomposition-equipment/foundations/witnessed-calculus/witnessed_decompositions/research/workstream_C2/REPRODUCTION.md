# Reproduce the C2 local checkpoint

Use the unchanged `lean-toolchain` (Lean4.35.0) and `lake-manifest.json`
(mathlib revision56a005855ea17e0b0958f73ec801ae140b0a1679). Install/fetch those
public dependencies with the standard Lake workflow first. Source/package
access is separate from mathematical verification. No private credentials or
private dependencies are required by the source. The development environment's
convenience script `/workspace/shared/witnessed_B_20261024/toolchain_recovery/env.sh`
and its package cache are NOT required portable paths.

With `lean` and `lake` on PATH, from the project root run:

```
bash verify_workstream_C2.sh
```

The driver checks all445 prior source/archive files byte-for-byte, frozen
contract/target and C2 source hashes; reruns the unchanged full C1/A/B driver;
compiles all inherited project modules and the new actual generic relation
Calc into a fresh directory; audits named Lean declarations; reruns both
independently implemented finite suites and four executed source mutations;
compares deterministic certificates; and rechecks source preservation.
Logs and result.json are placed under `reproduction_C2/<timestamp>/`.

Installed proof objects for the pinned public dependencies are reused; project
proof objects are generated afresh. This is not a bootstrap rebuild of Lean
or all mathlib. Python uses only its standard library. Expect a few minutes
and less than one additional GiB on this environment, excluding installing
public dependencies. Exact wall times are in the logs.

Standalone finite reruns:

```
python3 research/workstream_C2/finite/check_c2_model.py --output /tmp/c2-author.json
python3 research/workstream_C2/finite/run_mutations.py --output /tmp/c2-mutants.json
python3 research/workstream_C2/review/IndependentFinite.py --output /tmp/c2-independent.json
```

The independent checker does not import the author's evaluator. It separately
recomputes the full frozen domains and the saved named fixture. Its standalone
copy/clean-path reproduction and mathematical source review are recorded under
`review/`. Parent-appointed L review additionally rebuilds the actual Lean
source and creates independent positive and deliberately failing probes.

P, L and C remain distinct assurance levels. A successful driver cannot
self-promote a local checkpoint to accepted or discharge later D2/E integration.
Full C2 remains OPEN.
