# Active evidence for a simultaneous warehouse move

[Plant, rule and exact cost/slack bound](Probe_Complementarity.tex) · [Event replay and separate exhaustive local-table reference](replay.py).

Run `sha256sum -c SHA256SUMS` and `python3 -B replay.py | cmp results.json`. Both probes can jointly reduce delay even when neither alone pays off. One extra tick of old inspection can make the worthwhile pair physically unavailable. The simulated crews never receive the pooled observations.

The independently bookable bypass reservation has its own old inspection, preparation deadline and opportunity cost. The comparison also replays cases where reservation, both probes, one probe, or unreserved slow service is optimal.
