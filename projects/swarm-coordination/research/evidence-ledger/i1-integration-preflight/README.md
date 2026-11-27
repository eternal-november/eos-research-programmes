# I1 integration preflight at PR #678

**Decision: do not freeze the reference stack or spend the independent case yet.** The warehouse/radio clips justify building a common execution driver, not putting an architecture disposition on any inventory entry. This docket fixes the exact contract and evidence as reviewed, the permitted interpretations and the next discriminating work. It does not amend v0.3.1 or declare a positive envelope for confirmatory evaluation.

[Source obligations, proposed first gate and falsifiers](I1_Integration_Preflight.tex) · [Manifest](manifest.json)

## Reproduce the audit

Materialize the exact Git blobs named by `manifest.json` as INPUT/`<key>` (e.g. `contract`, `primary`, `crosswalk`, `670`). Run:

    python3 -B check.py INPUT | cmp expected.json -

The script checks bytes, the inventory label set and the open dispositions of this pinned docket. It exercises corrupt and overclaimed copies. It does not verify a proof, a simulator-to-model relation, or an experimental outcome. `expected.json` is not an acceptance certificate.

Full scope: [v0.3.1](https://github.com/eternal-november/eos-research-programmes/blob/8300069d616c03b5cf3a769e69ac165264af320f/projects/swarm-coordination/contracts/Swarm_Fault_Tolerance_Research_Contract_v0_3_1.tex) · [inventory evaluation](../../../fault-inventory/evaluation/README.md) · [existing paired-outcome audit](../../integration/paired-acceptance-audit/README.md).
