"""Verify the held-in timing overlay. This is not a distance-to-power map."""
import json
import sys
with open(sys.argv[1]) as f:
    rows=json.load(f)["source_cases"]
x,=[r for r in rows if (r["dimension"],r["accel"],r["dwell"])==(2,1,.25)]
lo=x["certified_motion_upper"]-x["dwell"]
hi=x["certified_motion_upper"]
assert lo+1e-6 < 1 < hi-1e-6
assert x["dwell_start_gap"]<1.54 and x["rest_gap"] < x["dwell_start_gap"]
assert hi < 1.5 and x["stationary_first_lower"]>1
print("synthetic transport cut 1 inside pinned geometric dwell; late retry 1.5")
