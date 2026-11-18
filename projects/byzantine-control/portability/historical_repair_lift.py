"""Recover the common-cut ADC comparison from the immutable source receipts."""
from fractions import Fraction as Q
import json
from pathlib import Path
import subprocess


HERE = Path(__file__).resolve().parent
SOURCE = "43d6674b8b4f7eac75bee7ea5d08ce12e3a83d29"
PREFIX = "theories-and-designs/byzantine-control/portability/"


def main():
    blob = subprocess.check_output(["git", "show", SOURCE + ":" + PREFIX + "native_clock_source_results.json"], cwd=HERE)
    result = json.loads(blob)
    rows = {(r["cut"], r["adc_first"]): r for r in result["entry_cut"] if r["cut"] != "none"}
    labels = [(cut, first) for cut in ("before", "after") for first in (False, True)]
    if set(rows) != set(labels):
        raise ValueError("The joint source does not supply these four cuts")
    residual = tuple(rows[label]["count_after_tie"] for label in labels)
    if residual != (0, 0, 62, 63) or any(rows[x]["pc"] != 267 or rows[x]["retired"] != 0 for x in labels):
        raise ValueError("Different PC, retirement or outstanding conversion")
    if any(rows[("after", first)]["source_conversions"] != 1 or rows[("before", first)]["source_conversions"] != 0 for first in (False, True)):
        raise ValueError("The delivered and refused histories were merged")
    delta = (1,-1,-1,1)
    marginals = lambda x: (x[0]+x[1],x[2]+x[3],x[0]+x[2],x[1]+x[3])
    if marginals(delta) != (0,0,0,0) or sum(a*b for a,b in zip(delta,residual)) != 1:
        raise ValueError("Lost the historical direction distinguishing conversion deadlines")
    # The diagonal and anti-diagonal are two sets of admitted local traces.
    # Equal half-masses are also test coefficient vectors; no random source is assumed.
    diagonal, anti = (Q(1,2),0,0,Q(1,2)), (0,Q(1,2),Q(1,2),0)
    if marginals(diagonal) != marginals(anti):
        raise ValueError("Different per-owner marginals")
    accepted = lambda x: {residual[i] for i in (2,3) if x[i]}
    if accepted(diagonal) != {63} or accepted(anti) != {62}:
        raise ValueError("A lost correlation no longer changes the accepted-job bound")
    elapsed = Q(rows[("after",True)]["elapsed"]) - Q(rows[("after",False)]["elapsed"])
    if elapsed != Q(1,4096):
        raise ValueError("Physical completion time did not distinguish the two accepted histories")
    print("PC267 common cut: four retained strobe counts", residual)
    print("The missing cross term changes the completion time by", elapsed, "quanta")


if __name__ == "__main__":
    main()
