# Typed calculus and controller environment integration proof sources

This package accompanies the separate integration results report dated 27 October 2026. It contains the mathematical integration notes, executable finite symbolic checks, their recorded JSON results, and unchanged excerpts from the original Lean development.

The result is a mathematical interpretation and a finite controller and environment instance. The checks support the stated arguments within their declared finite scopes. They are not a new Lean formalization, a complete build of the original Lean project, a proof of the full research contract, or a physical robot certification.

## Read and reproduce

1. Read [the calculus interpretation](theory/Original_Calculus_Dynamic_Interpretation.md).
2. Read [the fixture and controller example](example/Fixture_Assisted_Quarterturn.md).
3. From the extracted package directory, run:

   ```sh
   ```

Python 3.10 or later and its standard library are sufficient. The delivery was checked with Python 3.12. No package installation, network connection, or Lean toolchain is required. Do not run Python with assertion-disabling optimization flags.

The runner verifies `SHA256SUMS`, checks the original-source manifest, and runs all four checkers with assertions enabled in a temporary copy. It requires each freshly generated JSON result to match the packaged result byte for byte. No JSON normalization is used. It also checks the theory author's freshly written JSON file against that checker's freshly generated stdout. A successful run prints a JSON summary with `status: PASS` and exits with code zero. It leaves the extracted sources and recorded results unchanged.

The four checkers can also be invoked individually from the package root. Each prints JSON to stdout. The theory author checker additionally writes its result next to its own script; use the runner to avoid that write in the extracted package.

## Verification boundaries

- The theory author checker exercises finite instances and negative controls for the mathematical arguments. It does not enumerate all finite graphs.
- The independent core checker uses separate finite graph and map enumeration rather than the theory author's implementation.
- The fixture author checker constructs and checks the declared finite symbolic tables, controller, coupling, and negative examples.
- The independent fixture checker constructs a separate finite transition reference and mutation tests. It imports the author module to compare its tables and functions; “independent” does not mean an implementation with no shared assumptions or no access to that module.
- All four checks retain the scopes and limitations stated in their source and JSON. Passing them is not Lean compilation, continuous dynamics verification, empirical validation, or an external certification.

## Original source reference subset

The files under [theory/original](theory/original/) are selected, unchanged reference excerpts, not a complete Lean project. Imports may refer to files outside this subset, and no build configuration is supplied. Do not interpret the inclusion of `.lean` files as a claim that this package itself has been compiled.

When the integration note names an original declaration, the included locations are:

| Original declarations or context | Included file |
| --- | --- |
| `Component`, `Path.Slot`, `Path.componentAt`, `Path.expand`, `Signature` | [Core.lean](theory/original/Core.lean) |
| `CalcData`, `Calc`, `Calc.Hom` | [Calculus.lean](theory/original/Calculus.lean) |
| `Signature.Assignment`, `Tree.interpretOperation`, `Tree.extend`, `Tree.homEquiv` | [FreeExtension.lean](theory/original/FreeExtension.lean) |
| `Presentation.Model`, `Presentation.extend`, `Presentation.projection_extend` | [PresentedCalculus.lean](theory/original/PresentedCalculus.lean) |
| `SemanticRefinement.Arrow`, `mapArrow`, `functor`, `mapArrow_injective` | [SemanticRefinement.lean](theory/original/SemanticRefinement.lean) |
| Occurrence indexing and grafting transports | [RawRefinement.lean](theory/original/RawRefinement.lean), [PathOccurrences.lean](theory/original/PathOccurrences.lean) |
| Free calculus and refinement context | [FreeCalculus.lean](theory/original/FreeCalculus.lean), [RefinementFunctoriality.lean](theory/original/RefinementFunctoriality.lean) |
| Original research completion scope | [CompletionContract.md](theory/original/CompletionContract.md) |

Paths naming the original `witnessed_decompositions/` archive in the notes and manifest identify historical source locations. The fixture note also cites the earlier `Causal_Implementation_and_Control_Transfer.md`; that earlier note is background and is not included in this package. The files above are the included reference locations. The executable checks do not depend on the earlier archive or earlier note.


Verification scope: use the standalone mathematical checks identified in the project VERIFICATION.md. The original archive replay is not a supported repository command. No fresh Lean replay is claimed.
