# Shared-lane withdrawal

When the old owner withdraws, an in-flight proposal can still become a firm duty before the physical port is fenced. Fencing prevents later old starts but does not release an occupied lane. The proof gives sharp bounds for local physical dispatch, a certified dwell timeout, and a rule requiring affirmative settlement receipts. It separates a compliant refusal from a jam and a false owner declaration, and charges independent reserve capacity separately.

[Proof](Withdrawal_With_Live_Lane_Use.tex) · [Checker](replay.py)

Run `sha256sum -c SHA256SUMS` and `python3 -B replay.py | cmp results.json` here. The replay checks 7,500 traces and 22,500 decisions against a separate interval oracle.
