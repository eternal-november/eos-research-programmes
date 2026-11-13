# C2 prior theory and credit boundary

Verified 2026-10-24 through the primary-source arXiv PDF, version 3:
G.S.H. Cruttwell and Michael A. Shulman, *A unified framework for generalized
multicategories*, Theory and Applications of Categories 24 (2010), no.21,
580–655. [Primary PDF](https://arxiv.org/pdf/0907.2460v3).

Example 2.6 (PDF page12) defines V-Mat with sets, functions, matrices and
multiary cells; the two-element chain specialization is explicitly Rel.
Definition 7.1 and Examples 7.3 (PDF page37) define cartesian restriction and
identify matrix restrictions with reindexing. These are the applicable mature
baseline, not discoveries of this project. The paper's matrix convention lists
target then source; ours lists source then target. Transposing that notation
and taking identity vertical boundaries turns its Boolean cell condition into
our C(p)⊆W. Its zero-input condition becomes reflexivity, Delta⊆W.

For broader context, Shulman, *Framed bicategories and monoidal fibrations*,
[version2](https://arxiv.org/html/0706.1286v2), §4 develops the base-change
framework. We do not import an equipment universal property from that reference
as a substitute for the still-open E obligations.

The all-parameter proofs in `proof/C2_Model_Theorem.md` are self-contained
specialized proofs, not claims of originality. The deliverable's value is the
checked implementation in the existing typed occurrence API, explicit exact /
nonexact boundary bookkeeping, and independently reproduced finite fixtures.
These are model infrastructure. This local checkpoint does not discharge C4's
program-wide prior-art comparison, D2's sharp classification, or E's witness-
sensitive universal/reconstruction package. No broader novelty search or new
research phase is represented as completed.
