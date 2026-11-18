# Reproducing the portability evidence

Use unoptimized Python 3.12, Lean 4.33.0, a Git checkout containing the recorded scientific commits, and the contextual-composition Git repository. The [replay driver](program_replay.py) lists each check's actual code revision and whether it verifies a historical receipt, a current application, the current Lean proof closure or the old baseline. It checks the proposal ancestry before execution. For a result-generating historical check it replays the Git revision that last changed the particular result file through the requested revision. A historical reproduction establishes the receipt at that revision. Transfer to a changed source requires its actual comparison in the [dependency register](EXPORT-DEPENDENCIES.md). A failed case remains visible with its output and revision.

From the portability directory run:

    python -B program_replay.py --at <scientific-commit> --list
    python -B program_replay.py --at <scientific-commit> --lean <lean-4.33.0-executable> --research-repo <contextual-composition-repository-root> --jobs 4 --output <new-result-path>

For a bounded recheck add one or more exact `--only` names from the roster. The result states whether every listed check was selected. Separate temporary, locally shared Git clones give historical checkers their true working trees and access to the retained worker/archived Git objects. Each clone checks out one immutable commit at a time. Ordinary programme branches and user working files retain their checkout and index. Run records are created exclusively at a new path. The driver also checks that the invoked checkers leave their source trees unmodified.

The resulting JSON binds the scientific commit and tree, contract, checked historical and current receipts, Lean and Python versions, driver bytes and actual Git objects of the cited contextual-composition source files. A few documents cite a mathematical directory rather than one manuscript; those entries bind its tree. These source bindings also preserve the chronology of the raw-data and proof inputs. A run record records actual checks and failures; the semantic claim and the institutional acceptance of the research have separate evidence. The independent selector, unchanged frozen core, held-out adaptation, final scientific audit and both positive families must be bound to their own artifacts to label the entire portability program complete.

For a held-out transfer, invoke the reviewed runner with the independently retained full commit IDs as well as the target scientific revision. The original freeze contains the canonical manifest. The later selection binds that manifest and the hashes of its primitive target files. A candidate-only invocation can reproduce development observations. See the [transfer evidence rule](TRANSFER-INTERFACE.md) for the exact record formats.

    python -B program_replay.py --at <scientific-commit> --freeze-commit <full-freeze-commit> --selection-commit <full-selection-commit> --lean <lean-4.33.0-executable> --research-repo <research-root> --jobs 4 --output <new-result-path>
