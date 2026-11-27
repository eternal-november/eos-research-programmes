# Allocation lineage through a qualified state restore

[State_Lifetime.tex](State_Lifetime.tex) compares coalesced state inputs
with the same inputs split across source application cuts. The latter can
recreate the same number without rewinding the world. Only the new-birth
cut, not a later successful reply or clock reading, justifies replacing
the old allocation evidence in the fixture.

Stage INPUTS.tsv under the sibling pins directory, run
python3 -B replay.py ../pins, and compare stdout with results.txt.
The pin is not a full server or a field test. State changes in this
test come from an authorized, synthetic fixture supplier.
