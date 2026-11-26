# Live site checks with one reservation

In the three-state recovery model, making just one resource reservable is sufficient to maintain the exact s+3 worst-case read budget under s state changes. Without any reservation, even one change can defeat a guarantee regardless of how many bare checks are allowed.

[Proof, source scope and assumptions](One_Reservation_Through_Reconfiguration.tex) · [Independent policy search and trace replay](replay.py) · [Recorded results](results.json)

Run python3 replay.py and compare its output with results.json.

[The exact boundary without reservations](last-bare-check/) decides when one last bare inspection, or one atomic multi-group inspection, can certify a whole decision.
