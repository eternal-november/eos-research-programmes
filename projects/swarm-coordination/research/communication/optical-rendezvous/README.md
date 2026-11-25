# Two reports and an optical rendezvous

[Statement, deadline proof and comparison](Two_Report_Optical_Rendezvous.tex). Both reports must be physically delivered. The first report prevents B from listening before its initial visit to base. A and B can choose a coupled optical action to avoid checking the wrong corridor.

Run `python3 replay.py | cmp replay-final.txt`. The finite solver uses local-history classes and then rolls out the selected policy using only each actor's local view. It verifies the exact 6-tick per-world, 8-tick no-optics, 7-tick reliable-optics, and 8-tick possible-erasure bounds.

This is an authored development case, not a held-out physical validation or contract closure.


The receiver policy is frozen as `receiver_policy.json`. `python3 freeze_receiver.py | cmp freeze_receiver.txt` checks the original policy without rewriting it. `python3 replace_transducer.py | cmp replace_transducer.txt` compares the unchanged receiver on the mechanical flag source to the exact read-cut bound in 84 configurations.
