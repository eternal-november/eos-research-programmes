I2 MINIMAL OBSERVABLE REALIZATION — SOURCE PACKAGE
31 October 2026

Read I2_minimal_compositional_realization_results.txt first, then
 i2_minimal_realization_theorem.md (main theorem, explicit scope and cost ledger),
 proof_review.md and scope_review.md (independent mathematical/scope reviews).

Proof companions:
 realization_theorem_draft.md — quotient operations, exact joint cuts, universal
   comparison map, finite-index/effectivity distinction and characteristic DAG;
 encoder_decoder_draft.md — actual coefficient codec and constructor contract;
 index_boundary_theorem.md — natural-number obstruction and capped mechanisms;
 baseline_comparison.md — primary literature and import boundaries.
The retained 'draft' filenames are citation identifiers, not claims of formal
verification. This is a reviewed paper proof, not a kernel-checked proof.
Mathematical and scope reviews were performed by separate automated reviewers;
they may share model assumptions and correlated reasoning errors. This is not
external human certification or proof-assistant verification.

REPRODUCIBLE FINITE EVIDENCE (Python 3; standard library)
 python verify_i2.py
 sh verify_i2_replay.sh
 python verify_encoder_decoder.py
 python finite_typed_realization.py
 python verify_index_boundary.py
 python audit_independent_relation_check.py

The independent verifier's JSON must equal verify_i2_results.json byte for byte.
The replay shell script makes a fresh extracted temporary source tree, compiles
its executable sources, and repeats that equality test. Other outputs match
encoder_decoder_results.json, finite_typed_realization_results.json,
index_boundary_results.json and audit_independent_relation_results.json.
The index-boundary script also rewrites its own results JSON deterministically.
These checks cover coefficient kernels, bounded concrete examples, and a closed
finite typed constructor, not an implemented whole old-graph engine. Arbitrary
partial deterministic maps and arbitrary extra finite cut-record Z values are
not implemented. The paper's all-profile and arbitrary finite-depth claims use
its proofs, not extrapolation of finite test counts.

PINNED MATHEMATICAL DEPENDENCIES
The dependencies/I5 directory contains byte-preserved mathematical dependencies
from the completed I5 delivery, including its prior_math old-C5 dependencies.
Bare I5 filenames cited in I2 documents resolve in dependencies/I5. A bare
baseline_comparison.md in an I2 document means the I2 comparison at package root;
inside dependencies/I5 it means the I5 comparison. The historical I5 citation
original_C5/THEOREM.md resolves to dependencies/I5/prior_math/THEOREM.md;
Completion_Comparison.md resolves to dependencies/I5/prior_math/Completion_Comparison.md.
I5 model_and_core_comparison.md gives the original dependency hashes and roles.
Only mathematical I5 dependencies and their proof review are imported: this
package does not claim to rerun I5 verification outputs. Current I2 tests and
results are separate and listed above.

INTEGRITY AND SCOPE
SHA256SUMS.txt hashes every other shipped source file. verify_i2_sourcepins.json
records current delivered I2 source and imported I5 dependency hashes. Replacing
a theory-input pin with the delivered self-contained main manuscript changes
metadata only; all original independent verification non-pin fields are equal.
Internal exploratory notes and review chronology are not part of this package.
No claim is made of unrestricted I2 or whole-contract closure, count-preserving
or unique witness lifting, generic finite-index decidability, finite all-profile
state space, access to hidden labels, or minimal physical realization.
