# Spare capacity after a role change

An exclusive gate role changes twice while older tote closures remain due, and every relay tick consumes a worker slot. The exact admission profile determines which slots can be kept spare together after meeting those duties. Disjoint job groups can combine profiles over the same named slots. The profile answers admissions, not who must perform or prove an old duty.

[Written proof and scope](Role_Changes_With_Pending_Work.tex) · [Replay](replay.py) · [Expected results and traces](results.json)

Verify with python3 replay.py --verify.

The replay compares 89,088 admission queries with a direct matching algorithm and checks 512 triples for assembly. A planned transfer is followed by a transfer under partial loss observation. An unfinished tote can require the only backup worker and prevent the same additional admission; already owed work is served in both cases. A control with later evidence shows why the frozen-schedule hypothesis matters. This is not physical validation, Lean certification, or full C3 acceptance.
