# Separate clearance providers

[Proof and scope](Separate_Clearance_Providers.tex). Two provider implementations
interact only through distinct permitted sensor ports. The frozen lane receiver and
resource oracle are unchanged; a late otherwise-valid report passes standalone
service but fails the earlier joint deadline.

Run `sha256sum -c SHA256SUMS` and `python3 -B replay.py | cmp results.json`.
