"""Finite scoped handoff model, separate from the pinned C++ source."""
from itertools import product

MOVES = (("forward", "corridor"), ("reverse", "corridor"), ("south", "south"))
# Empty footprints sampled at the end of slot zero; transfer at the end of 3.
# Gate cut 1 blocks all slots 1..3, 4 blocks none of them. Gates include all
# already-issued movements if enabled. A sampled empty space can fill again.
DECISION = 3

def changed(initial, events):
    current = set(initial)
    for move, tick in events.items():
        footprint = dict(MOVES)[move]
        if 1 <= tick <= DECISION:
            current.add(footprint)  # entrants may stay to the decision
    return current

def actual_possible(gates, footprint, sample):
    candidates = [range(g+1) for g in gates]
    # Care: option 0 encodes no entry; 1..g encodes entry before fence g+1.
    for entry_times in product(*candidates):
        if footprint in changed(sample, dict(zip(dict(MOVES), entry_times))):
            return True
    return False

def allowed(gates, footprints, sample):
    footprint_gated = {p for p in footprints if
                       all(g == 0 for (_, zone), g in zip(MOVES, gates) if zone == p)}
    return footprint_gated - sample

def main():
    total = 0
    for gates in product(range(DECISION+1), repeat=len(MOVES)):
        for c, s in product((False, True), repeat=2):
            sample = {p for p,b in [("corridor",c),("south",s)] if b}
            plans = allowed(gates, {"corridor", "south"}, sample)
            for z in ["corridor", "south"]:
                assert (z in plans) == (not actual_possible(gates, z, sample))
                total += 1
    naive = allowed((0,3,3), {"corridor","south"}, set())
    selective = allowed((0,0,3), {"corridor","south"}, set())
    assert naive == set() and selective == {"corridor"}
    print("matched maximal scoped releases:", total)
    print("close forward only: corridor stays with fleet; reversal can still enter")
    print("fence both corridor directions and verify empty: maintenance can start; south remains independent")

if __name__ == "__main__":
    main()
