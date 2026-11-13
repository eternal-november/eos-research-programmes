F2 original typed bridge source package
31 October 2026

Start with F2_original_typed_bridge_verification.txt. The original F2 proof,
finite certificate and minimum floor have a dated non-author PASS review.
This does not certify larger F1–F3 novelty, all dependencies or the full program.
No I4 work is included.

Read in this order
1. contract/F2_VERBATIM.md and the full original contract.
2. proof/proof_instantiation.md for the all-degree original-slice argument.
3. verification/DOMAIN_AND_METHOD.md for the exact finite domain and reductions.
4. verification/results.json and review/acceptance_review.md for the findings.

Run the complete certificate with Python 3 and only the standard library

    python3 replay.py

The wrapper verifies SHA256SUMS, runs both source modules in a fresh temporary
working directory, compares the complete deterministic JSON bytes, validates
its embedded source hashes, and tests -O and PYTHONOPTIMIZE=1 rejection. It does
not require network access, third-party packages or the original workspace.
It leaves the release unchanged. Optionally save new replay evidence outside
the package using

    python3 replay.py --output-dir /tmp/f2-replay-evidence

Do not use -I: isolated mode omits the adjacent support-module import path.
Do not use -O or PYTHONOPTIMIZE: assertion-disabled execution is refused.
Timing appears only in console logs, outside deterministic results.json.

Package hierarchy
contract       Exact original F2 and unedited full contract.
proof          Explicit F2 proof instantiation and original-source map.
verification   Full verifier, original C1 support, domain and expected JSON.
review         Clean review and independent replay receipt.
reproduction   Reviewed final-run output and assertion guard evidence.
sources        Direct imported C1, CUT, recognition and A3/C5/B3 proof sources.

Mathematical sources are byte-preserved; reviewer attribution has only a
publication-only wording edit. PROVENANCE.json maps packaged paths to the
canonical original paths and hashes. Historical OPEN or submitted statements
inside imported sources remain historical, not new verdicts. Their original
relative references are preserved and may point outside this minimal package;
the direct sources used for this F2 instantiation are included under sources.
The package does not claim a complete Lean source dependency closure.

The recognition theorem is used only at M=1 and H_G={id} on all ordered graphs.
Its cluster quotient examples and their smaller finite checker are not F2's
domain. Original A3_LOCAL_COMPARISON.md and THEOREM.md supply the actual C5
presentation; Completion_Comparison.md supplies the full B3 tuple comparison.
Semantics_Transport_Factorization and fixed-endpoint quotient classifications
are not premises of this unquotiented F2 instantiation and are not duplicated.

Reviews are separate-agent checks with correlated-model/source/tool limits,
not external human certification or kernel checking. The report records those
limits and the precise mathematical and computational evidence boundaries.
