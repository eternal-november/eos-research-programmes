EVIDENCE-TO-MISSION COMPATIBILITY — SOURCE PACKAGE
2026-10-30

This is a new, standalone research checkpoint. It supplements, and does not
replace, the structural comparison proofs included under structural_dependencies/.
The separate companion TXT gives the readable checkpoint; this archive contains
the proofs, attribution notes, and reproducible finite check.

READING ORDER
1. two_sided_linear_evidence_theorem.md
2. stratified_relational_interface_theorem.md
3. two_sided_linear_prior_art.md and attempt5_prior_art.md
4. proof_review.txt and the relevant structural_dependencies/ notes

ESTABLISHED SCOPE
The first theorem gives an exact criterion for a fixed single-loop kernel-image
(KI) readout mission with finite-dimensional exact two-sided linear evidence.
It includes constructive positive witnesses and rank-at-most-one failure
witnesses. An original inverse-domain requirement, if imposed by the mission,
is an additional guard; KI does not silently impose or replace that contract.
Transport through known linear contexts is covered. Closure under composition
of independently unknown boxes is not proved by this single-loop criterion.
Projected known-context families must retain their lift correlation when they
are combined with other unknowns; independent resampling is not valid.

The second theorem constructs exact finite shared-parameter rank-stratified
relational interfaces, witness sections, invisible freedoms, and transition
maps for a declared finite closure of homogeneous linear-in-wire systems.
Rank drops and original admission guards are retained. Relational composition
is fiberwise in the SAME parameter tuple and keeps shared witnesses at cuts.
Under the stated v2 smallness, actual-cylinder, and context/wiring hypotheses,
the existing free-Isbell comparison construction supplies coherent two-sided
comparison families. Separately extracted and assembled raw carriers are not
identified merely because their normalized middle agrees.

Finite rational raw matrices do NOT imply finite free-Isbell apices, finite
matrix presentations of those apices, or effective size bounds. Exactly one
controller/policy is fixed before quantifying over supported worlds. Parameter-
dependent sections are proof witnesses only, not executable hidden-world
controllers or observable selectors.

LIMITS AND OPEN QUESTIONS
Neither theorem infers model-class adequacy, actual omitted couplings, or
physical topology from incomplete evidence. Completeness is relative to the
stated model class and the fixed mission. Practical smallness/size bounds,
noisy acquisition, safely choosing experiments, and acquisition budgets remain
open. The structural constructions retain their explicitly stated mathematical
smallness hypotheses. Unlimited-context closure and a universal finite atlas
are not asserted. Classical ingredients include matrix completion, rank/kernel
analysis, comprehensive Gaussian elimination, and relational semantics.
Priority remains unresolved; no novelty or general network-acquisition claim
is made. The prior-art notes retain their source and comparison qualifications.

REPRODUCIBLE CHECK
Requires Python 3.10 or later; no third-party packages are needed.
From the extracted directory run:

    python3 two_sided_linear_audit_binary.py

Expected output is in binary_check_output.txt. It exhaustively checks the
single-loop feasibility/output branching equivalence over GF(2), with one-
dimensional uncertainty codomain and readout, for the three dimension pairs
listed in proof_review.txt: 69,952 cases in total. It is finite corroboration,
not a proof of the real theorem or a test of all other claims in the package.

INTEGRITY
SHA256SUMS lists every payload file other than itself. On systems with sha256sum,
run `sha256sum -c SHA256SUMS` from the extracted directory. The theorem files,
check script, and six structural dependency notes are unchanged source copies.
The two prior-art notes have presentation/process references cleaned while
retaining mathematical qualifications and source limitations.
