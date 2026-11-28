#!/usr/bin/env python3
"""Factored resource and clock control for the native joined fixture."""
from pathlib import Path
import json

def main():
    a={}
    for line in Path(__file__).with_name("NATIVE.txt").read_text().splitlines():
        row=tuple(map(int,line.split()))
        cap,gap,alternate,when,mode,budget,w,raw,step,charge,travel,turn=row
        assert row[:7] not in a
        charged=int(alternate or cap==5 or gap>8)
        emitted=charged and mode!=2
        assert charge==charged and raw==(w if emitted else -1)
        good=emitted and mode==0
        d=when+2
        assert step==(d if good else -1)
        feasible=(good and ((d==2 and budget>=8) or (d==3 and budget>=9)))
        if good and d==2:
            assert travel==32
        else:
            assert travel==budget*4
        should=(4*w if feasible else (0 if budget==8 else 4))
        assert turn==should
        a[row[:7]]=row[7:]
    assert len(a)==432
    positives=0
    for cap,gap,alt,t,mode,b,_ in list(a)[::2]:
        rep=[a[cap,gap,alt,t,mode,b,x] for x in (0,1)]
        pair=rep[0][-1]==0 and rep[1][-1]==4
        expected=bool((alt or cap==5 or gap>8) and mode==0 and t+2<=b-6)
        assert pair==expected
        positives+=pair
    # Same raw receipt at the same stamp, two semantically different cuts.
    assert a[5,8,0,0,0,8,1]==(1,2,1,32,4)
    assert a[5,8,0,1,0,8,1]==(1,3,1,32,0)
    # Retaining the robust prefix for arc allowance nine recovers one slot.
    assert a[5,8,0,1,0,9,1]==(1,3,1,36,4)
    # Adding receiver capacity alone is not a bypass for the selected
    # sender-side bottleneck in the pinned common-cap model.
    assert a[4,8,0,0,0,8,1][0:3]==(-1,-1,0)
    assert a[4,8,1,0,0,8,1][0:3]==(1,2,1)
    assert a[4,9,0,0,2,8,1][0:3]==(-1,-1,1)
    assert a[5,8,0,0,1,8,1][0:3]==(1,-1,1)
    print(json.dumps(dict(native_rows=len(a),paired_cases=len(a)//2,
                          paired_heading_safety=positives),sort_keys=True))
if __name__=="__main__":
    main()
