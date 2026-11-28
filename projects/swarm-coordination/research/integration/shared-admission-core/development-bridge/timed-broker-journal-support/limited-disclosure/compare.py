#!/usr/bin/env python3
from itertools import product
from pathlib import Path
import json

H=Path(__file__).resolve().parent

def main():
    rows={}
    for line in (H/"NATIVE.txt").read_text().splitlines():
        v=tuple(map(int,line.split()))
        g,s,c,l,z,a,bind,b,permit,priv,ack,act=v
        active=not (s&1) or bool(a)
        sent=active and (z==2 or (z==1 and b))
        shared=(g & ~s)!=0 and l<=8
        expected=(b if active else -1,b if sent else -1,int(not(sent and shared and c==4)),int(sent and b and not bind))
        assert v[8:]==expected
        rows[v[:8]]=v[8:]
    assert len(rows)==2304
    leak=all_met=0
    for g,s,c,l,z,a,bind in product(range(4),range(4),(4,5),(4,8,9),range(3),range(2),range(2)):
        m0,q0,p0,e0=rows[g,s,c,l,z,a,bind,0]
        m1,q1,p1,e1=rows[g,s,c,l,z,a,bind,1]
        private_view=q1==1 and q0!=1 and not bind and e1==1 and e0==0
        observer_same=p0==p1
        disjoint_progress=min(p0,p1)==1
        both=private_view and observer_same and disjoint_progress
        allowed=not (s&1) or bool(a)
        fits=not (g & ~s) or c>=5 or l>8
        assert both==bool(allowed and z and fits and not bind)
        leak+=not observer_same
        all_met+=both
    def views(g,s,c=4,l=8,z=1,a=1):
        return tuple(rows[g,s,c,l,z,a,0,b][1:3] for b in (0,1))
    assert views(3,0)==((-1,1),(1,0))
    assert views(3,0,z=2)==((0,0),(1,0))
    assert views(3,1)==((-1,1),(1,0))
    assert views(3,2)==((-1,1),(1,0))
    assert views(3,3)==((-1,1),(1,1))
    assert views(3,3,a=0)==((-1,1),(-1,1))
    assert views(3,0,l=9)==((-1,1),(1,1))
    # After supersession use is denied while public receipts still differ.
    assert rows[3,0,4,8,1,1,1,0][2:]==(1,0)
    assert rows[3,0,4,8,1,1,1,1][2:]==(0,0)
    # Exhaust count-level Pareto frontier of mixtures of early padded
    # schedule and public-only schedule, at exclusive cap-four overlap.
    grid=0
    def choices(b):
        # From the pinned overlap case at cap four. Add intentional
        # idle when the robust objective only requires lower rates.
        return {(int(q==1),ok) for z in range(3)
                for _,q,ok,_ in [rows[3,0,4,8,z,1,0,b]]} | {(0,0)}
    private_world={(0,0)}
    public_world={(0,0)}
    for n in range(1,129):
        private_world={(p+x,s+y) for p,s in private_world for x,y in choices(1)}
        public_world={(p+x,s+y) for p,s in public_world for x,y in choices(0)}
        common_ack={s for _,s in public_world}
        actual={(p,s) for p,s in private_world if s in common_ack}
        expected={(p,s) for p in range(n+1) for s in range(n+1-p)}
        assert actual==expected
        grid+=len(actual)
    print(json.dumps(dict(native_cases=len(rows),trace_pairs=len(rows)//2,
                          observable_leak=leak,lawful_live_and_private=all_met,
                          feasible_count_grid=grid),sort_keys=True))
if __name__=="__main__":
    main()
