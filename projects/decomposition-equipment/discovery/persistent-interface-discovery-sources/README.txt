Persistent interface discovery source checkpoint
28 October 2026
Scope clarification revision 1

This revision explicitly identifies the finest mixing partition and clarifies structural assumptions, class-relative checking, deployment initialization and physical hazard transfer. Audit_Scope_Clarifications.md records the pre-revision audit and subsequent verification. The core discovery and resource proofs are unchanged.

Start with Persistent interface discovery results.txt. It opens with a plain-language abstract. This checkpoint establishes scoped constructive discovery and verification results, not a physical robot study or full research-contract discharge.

Proof order
1. Coupled_Family.md gives the main common-class theorem: bounded local noisy moments recover unknown sparse delayed binary dynamics and sensor mixing; lag-defined crossing regions and compressed persistent influence transducers follow. It includes explicit finite-trajectory confidence, Fourier mixing, parameter-error transfer and controlled predictive rank.
2. Proposal_Validation.md gives class-relative O(n^2) moment checking of a supplied recurrence/frame proposal without repeating sparse support search. It is not a test of arbitrary-world membership in the model class.
3. Discovery_Calculus_Bridge.md specifies exact state/event and probability certificates through the existing Dynamic.Assignment APIs. It retains common initialization and one owner per random event. The certificate is specified and proved, not a new completed software checker or Lean build.
4. Shared_Interface_Realization.md proves the joint storage/read criterion and repair certificates. Section 2A extends tight-budget impossibility to arbitrary deterministic fixed-port register encodings. General repair enumeration and optional coding tradeoffs remain linear-only.
5. Constructive_Target.md is a complementary hidden-correlation family. Its final heterogeneous extension uses three-tick independent stationary episodes; this is a different data resource from the main single-trajectory theorem.
6. Target_Fidelity.md records independent AI review and corrections. Earlier provisional passages are explicitly review history. Distributed_Realization_Baselines.md, Linear_Sharing_Realization_Addendum.md and Finite_Field_ICA_Source_Credits.md give exact primary comparisons and attribution.

Reproducible bounded checks
Tested with Python 3.12.14, NumPy 2.3.5 and SymPy 1.14.0. Run:
    python3 check_constructive_target.py
    python3 check_coupled_family.py
    python3 check_heterogeneous_pair_path.py
    python3 check_proposal_validation.py
    python3 check_shared_interface_realization.py
The scripts print checks; some regenerate their corresponding QA JSON. The small path checks use explicit matrices as an independent reference, not as the claimed learning algorithm. Checks combine exact finite-field/rational calculations and floating-point probability identities. They are bounded regressions, not empirical learning trials or proofs of all-size theorems. No full data-learning application, new Lean formalization, or external human verification is supplied.

Main limitations
Known calibrated sensor noise, bounded linear mixing, sparse binary dynamics, biased independent innovations and the stated initialization/access conditions remain premises. Latent states and actual partitions are not supplied. Resource bounds depend on the declared stream, read, timing, sharing and wiring contracts. Retiming, additional private state or shared randomness may change those bounds and must be charged. Internal model messages are not automatically observable by a deployed controller.

The source-specific mathematical integration is established at its written scope. Scientific priority, a unique physical ontology, necessity of the categorical language, and superiority over every matched structured baseline are not established. The original contract and earlier acceptance decisions were not changed.

Integrity and sources
Manifest.json lists byte sizes and SHA256 for every other archive member. Primary papers are linked in the authored notes and are not redistributed. The original Dynamic Lean sources belong to previously delivered checkpoints; this archive specializes their documented APIs rather than supplying a new formal build.
