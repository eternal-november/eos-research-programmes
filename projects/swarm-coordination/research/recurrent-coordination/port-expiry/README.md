# Receipt expiry at a shared custody port

Two scopes with the same standalone rate guarantees can differ in whether both rates are achievable at one port. The exact criterion tracks handoff phases as well as expiry and arrival spacing.

[Source and proof](Receipt_Expiry_And_Shared_Port.tex)

```sh
set -o pipefail
python3 -B model.py | cmp replay.txt -
python3 -B verify.py | cmp proof-replay.txt -
```

`certificate.py` regenerates the integer potential in `potential.json`. The verifier does not import the generator or the calendar search. The numerical model concerns actual custody effects at a trusted clocked port. It establishes no independent deployment or deadline guarantee.
