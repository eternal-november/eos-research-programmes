# Checked occurrence interfaces and linear claim packages

Read the [TeX manuscript](Checked_Occurrence_Interfaces_and_Claim_Packages.tex). **Classification: scoped operational realization.** The preservation theorems below concern this particular checked language and runtime. They do not define the general contextual-composition theory or discharge its general interaction, refinement or feedback obligations. The channel and claim-right structures are one realization, not mandatory ingredients of the theory. Executable tests are diagnostics for that realization, not substitutes for its written arguments.

This extends the [recursive occurrence machine](../recursive-occurrence-machine/README.md) with an explicit checked subset rather than calling arbitrary host-language callbacks typed code.

## What is checked

- A finite explicit ordinary signature and syntax, including every primitive table row and every syntactic branch, even zero-weight outcomes and unused alternatives.
- Simultaneous recursive procedure declarations. Calls need not terminate; declared leaf bounds constrain successful returns, not eventual service.
- Actual addressed result trees and repeated equal-valued occurrences. A leaf-type bound does not flatten a tree or merge its holes.
- A private ordered-slot interpretation, so heterogeneous types and slot permutations do not accidentally depend on sorting token names.
- An elaborator for the no-mint ordinary core, using revalidated copied declarations and generated lookups rather than submitted callbacks.
- Protected linear claim rights for dynamic child results, distinct from copyable public handles.
- Finite checked administrative scripts that spawn verified ordinary children, transfer paired handle/right/resource packages through homogeneous channels, receive under local binders, and terminate with whole-tree await or return.

The closed-network assertion combines live ownership, ordered private interfaces, unique claim rights, matching queued package witnesses and each child's checked return bound. Historical result records remain provenance, not extra authority or assertions about current token kinds.

## Scope that matters

Ordinary signatures enumerate finite public, world and private-store domains. Execution may still diverge, grow arbitrarily many internal jobs and produce arbitrarily large finite occurrence trees. Administrative scripts are finite and have no nominal recursion; the number of their public spawn instructions is bounded. Their children may be mutually recursive.

Ordinary minting is excluded by the elaborator. Claim-spawn issues a fresh **administrative right**, not physical resource stock; ordinary primitives cannot forge or retarget that protected right. Await is terminal in the checked script layer and preserves the complete child tree plus a separate caller reserve. General continuations after multi-hole await are not yet checked.

Channel preservation is for a **closed network of checked participants using the same schema**. An arbitrary raw sender or bare public-handle await is not silently admitted. Receive introduces a new logical binder, not a newly allocated actual handle: it may name a handle already known elsewhere.

These written rule/invariant arguments and executable diagnostics are not Lean certification, a host-language security boundary, a complete dependent typechecker, or completion of RC1/RC7. They do not establish physical availability, termination, fairness, delivery or Byzantine safety. No historical novelty or TeX compilation is claimed.

## Reproduce

From this directory:

    python3 runtime/test_checker.py
    python3 runtime/test_ordered_runtime.py
    python3 runtime/test_elaborator.py
    python3 runtime/test_claim_runtime.py
    python3 runtime/test_typed_admin.py
    sha256sum -c MANIFEST.sha256

Diagnostics include hidden malformed branches, consumed-slot aliases, zero-weight rows, heterogeneous slot permutations, unbounded recursive prefixes, declaration mutation after validation, live retyping versus historical records, namespace collisions, multi-hole await, real message escrow, swapped handle/ticket packages, and per-prefix queue/child-interface checks.

The included base runtime is unchanged from the preceding tranche; the new ordered and claim layers are separate subclasses.
