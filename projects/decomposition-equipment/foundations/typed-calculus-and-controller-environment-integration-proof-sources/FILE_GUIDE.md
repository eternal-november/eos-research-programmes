# File guide

All paths below are relative to the extracted package root.

## Package support

- `README.md` — reading order, reproduction instructions, source mapping, and limits.
- `FILE_GUIDE.md` — this complete inventory and purpose guide.
- `run_checks.py` — integrity validation and fresh execution of all four checkers.
- `SHA256SUMS` — SHA-256 values for every other file in the package; it does not hash itself.

## Mathematical interpretation

- `theory/Original_Calculus_Dynamic_Interpretation.md` — mathematical bridge from the original ordered typed calculus to the specified dynamic interpretation, with hypotheses and scope limits.
- `theory/check_original_dynamic_bridge.py` — author finite regressions and negative controls.
- `theory/check_original_dynamic_bridge_results.json` — expected result of a fresh run of that checker.

## Finite controller and environment example

- `example/Fixture_Assisted_Quarterturn.md` — symbolic fixture tables, controller decomposition and coupling, guarantees under declared assumptions, and counterexamples.
- `example/check_fixture.py` — author executable model and regressions.
- `example/check_fixture_results.json` — expected result of a fresh run of that checker.

## Separate executable checks

- `review/core_bridge_independent.py` — separate finite graph and map enumeration and mutation controls for the core bridge.
- `review/core_bridge_independent_results.json` — expected result, including hashes of the theory note and included Lean files.
- `review/fixture_independent_check.py` — separate finite reference, comparison with author tables and functions, controller coupling checks, and mutations.
- `review/fixture_independent_results.json` — expected result, including hashes of the fixture note and author checker.

The `review` directory contains reproducible programs and their results only, not review correspondence or prose review notes.

## Unchanged original reference excerpts

- `theory/original/Core.lean` — original typed component, path, occurrence, and signature definitions.
- `theory/original/Calculus.lean` — original calculus and homomorphism definitions.
- `theory/original/FreeCalculus.lean` — original free-calculus context.
- `theory/original/FreeExtension.lean` — original interpretation extension and uniqueness machinery.
- `theory/original/PathOccurrences.lean` — original path occurrence indexing context.
- `theory/original/RawRefinement.lean` — original grafting and occurrence transports.
- `theory/original/RefinementFunctoriality.lean` — original refinement functoriality context.
- `theory/original/SemanticRefinement.lean` — original semantic refinement arrows and induced maps.
- `theory/original/PresentedCalculus.lean` — original presentation models and quotient interpretation.
- `theory/original/CompletionContract.md` — original completion criteria, included to distinguish this integration result from the full contract.
- `theory/original/SOURCE_MANIFEST.json` — original archive member names and hashes for these ten reference excerpts.

These eleven files are a reference subset, not a complete or newly verified Lean build. No previous archive is replaced or modified by this package.
