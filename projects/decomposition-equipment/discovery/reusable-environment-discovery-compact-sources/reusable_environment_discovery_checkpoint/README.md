# Reusable environment discovery checkpoint

Read the TXT report first. Its abstract states the result and the limits.

## Scope

The generic conditional-product discovery theorem is in theory/Discovery_and_Reuse.md.
The common-response construction and limited original C5 bridge are in
theory/Witnessed_Feedback_Composition.md. The growing experiment implements a
specialized nonlinear input-memory subclass, not every algorithm in the generic theorem.
All inference and feedback claims remain conditional on the stated universe and coverage.
No new Lean, external human verification, or physical robotics validation is claimed.

## Compact attachment and complete raw backup

This compact attachment includes the complete proofs, code, frozen candidates,
certificates and the n12 main raw records. The larger n24/n48/n96 and pilot raw
records are omitted ONLY to fit the chat attachment limit. The complete 54-file
checkpoint, including all raw records, is separately saved in Space as
"Reusable environment discovery sources.zip" (51061435 bytes; SHA256
f2a8b1a93ea54f04a8901eb92bc20aa5f93de08ca41346130d506cc84be079cc).

For a quick raw-data replay on this attachment, use:

    python3 examples/check_saved_artifacts.py examples/runs/n12

The exact source sampler checks and all tests/check_*.py scripts need no omitted
records. To replay all four raw-data checks, first regenerate the main datasets
using the command below with --output examples/runs, or obtain the full checkpoint
from Space. Regeneration overwrites the bundled main-run metadata with the same
seeded study's results; wall-clock fields can differ. It is not new evidence.
The SHA256SUMS in THIS archive authenticates the compact content, not the full archive.

## Reproduce checks

Tested with Python 3.12.14 and NumPy 2.3.5. From this checkpoint directory:

    python3 -m pip install -r requirements.txt
    python3 -m unittest discover -s examples -p test_discovery.py
    python3 examples/check_saved_artifacts.py examples/runs/n12 examples/runs/n24 examples/runs/n48 examples/runs/n96
    python3 examples/check_exact_source_sampler.py examples/runs/n12 examples/runs/n24 examples/runs/n48 examples/runs/n96
    for f in tests/check_*.py; do python3 "$f"; done

The records-only checker does not call the synthetic generator or truth audit, but
reuses implementation functions from the learner. Independent proof/code review and
separate exact regression scripts supplement it; this is not independent human validation.

To regenerate all main data and discovery results in a NEW directory:

    OPENBLAS_NUM_THREADS=2 python3 examples/check_growing_memory_environment.py --sizes 12 24 48 96 --output regenerated

The four main runs use the recorded fixed seed, 65536 training rows, 20480 validation
stream rows, and 262144 calibration rows per run. The two calibration halves have
different roles. Re-running the seed is reproduction, not new evidence. Wall-clock
fields and some container/archive metadata need not reproduce byte for byte.

The pilot directory retains development candidate metadata for data-cost
accounting only. It is not one of the four current statistical certificates. Development
certificate summaries are intentionally omitted. The pilot used 16384+5120+32768 rows.
The total investigation count is 1446912 vector readout rows, plus 20 warmup action rows.
These are not 1446912 independent complete episodes.

## Files and provenance

All frozen candidates and sufficient-statistic certificates are included; raw-data coverage is described above.
The exact bounded sampler uses 17 independent fair bits for EACH innovation block at
EACH tick. It does not reuse one random index across independent blocks.

The references directory contains unchanged earlier proof sources used by the C5
comparison. Older workspace-relative source names in the proof notes map to these
snapshots. They are background results, not new claims of this checkpoint.

prior_art/Discovery_Baselines.md separates known mechanisms from the present integrated
result; novelty has not been established. review/Assumption_Challenge.md records the
mathematical audit and limitations. The original research contract remains open.

SHA256SUMS lists all packaged files except itself. Verify those bytes before relying
on the checkpoint. The TXT copy inside the archive matches the separate report.
