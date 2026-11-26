# A last bare check that certifies the whole choice

Bare reads can still guarantee a live joint commitment if each state has a coordinate that differs in all alternatives reachable within the change budget. Without that coordinate, changing the state just before the last read defeats any finite guarantee.

[Proof and scope](Final_Check_Without_Reservations.tex) · [Exact replay](replay.py) · [Recorded results](results.json)

Run python3 replay.py and compare its output to results.json. The round budget is a constructive upper bound, not an optimality claim. A final atomic multi-group read has an exact minimum scope given by a hitting set.
