CROSSING INTERFACES AND MISSION CERTIFICATES — 31 October 2026

A new bounded contract-bridge checkpoint, not a replacement for the earlier
bounded protocol delivery and not completion or adoption of the whole contract.
Start with Crossing_interfaces_and_mission_certificates.txt; the full argument
is crossing_certificate_transport.md, including its precise positive scope.
proof_review.md summarizes the final independent mathematical/code review.

Reproduce with Python 3.12 (standard library only), from this directory:
  python -m py_compile compile_crossing_certificate.py verify_crossing_certificate.py
  python verify_crossing_certificate.py > replay_certificate.stdout.txt
  python compile_crossing_certificate.py > replay_compiler.stdout.txt
  cmp replay_certificate.stdout.txt verification_crossing_certificate.stdout.txt
  cmp replay_compiler.stdout.txt verification_crossing_compiler.stdout.txt
The scripts regenerate their corresponding JSON result files. Both stdout
files and JSON results must match their supplied counterparts byte for byte.
The probability verifier checks 112676 finite assertions. The compiler has
12 positive runs and 8 rejection tests; its derived normalized word-RAM core
ledger is 445n+597, with admission, normalization, provenance and physical
premise verification external and separately charged. These are finite tests
and an abstract operation model, not a theorem prover or hardware benchmark.

The prior_math tree contains the required earlier mathematical sources:
uncertain-coupling physical semantics/support learning; common-response and
ownership construction; the ordered C5 distinction; and the contextual
first-loss preservation pattern; and the fixed-cylinder CFS comparison and
normalizer laws. Short source names in the new notes refer
to these files. Historical/background citations in those prior documents are
not needed for the new proof or executable replay and are not bundled.
No physical premises have been empirically certified by this package.

Verification-note commands have been made relative and internal agent identifiers
removed for portability/privacy; executable
sources, theorem and prior mathematics retain their source bytes.
SHA256SUMS lists every included file other than itself. The ZIP has fixed
entry order, timestamps and permissions. Private audit/process artifacts,
workspace recovery files and caches are intentionally excluded.
