#!/usr/bin/env python3
"""Source-command slew, hardware-state pairing and independent duty evidence."""
from dataclasses import dataclass
from itertools import product
from pathlib import Path
import hashlib,json,sys
from prior_model import transition

H=Path(__file__).resolve().parent
payload=(H/"prior_model.py").read_bytes()
assert hashlib.sha1(f"blob {len(payload)}\0".encode()+payload).hexdigest()=="a84b9cb20aa29378b89bca1daa5ca1b4a9a1288e"
U=4
T=5
FIRST=(U,U,0,0)
COMMANDS=tuple(product(range(U+1),repeat=2))
WEAK=((1,2),(2,1))

def slew(before,after,axis):
    return axis==0 or sum(abs(u-v) for u,v in zip(before,after))<=2*axis

def final(path):
    if not all(s[:2]==(0,0) for s in path):
        return None
    return tuple(s[3]-s[2] for s in path),max(s[2]+s[3] for s in path)

def direct(mask,axis):
    """Independent coordinate profiles; join on actual shared target slew."""
    independent=[]
    for col in (0,1):
        data=[]
        for word in product(range(U+1),repeat=T):
            ends=[]
            for w in range(2):
                x=U;d=0
                for y in word:
                    b=WEAK[w][col]
                    if y>x or (x-y>b and not mask&(1<<col)):
                        break
                    v=x-min(x-y,b)
                    d+=x+v;x=v
                else:
                    if x==0:
                        ends.append(d)
            if len(ends)==2:
                data.append((word,ends))
        independent.append(data)
    values={}
    by_seen=[[{} for _ in range(T+1)] for _ in (0,1)]
    for ((a,ds),(b,dt)) in product(*independent):
        plan=tuple(zip(a,b))
        if not all(slew(x,y,axis) for x,y in zip(((U,U),)+plan,plan)):
            continue
        heads=(dt[0]-ds[0],dt[1]-ds[1])
        assert heads[0]<=heads[1] # every blind path has this ordering
        states=tuple((0,0,ds[w],dt[w]) for w in (0,1))
        row=max(ds[0]+dt[0],ds[1]+dt[1]),plan,states
        if heads not in values or row<values[heads]:
            values[heads]=row
        if heads in ((0,0),(4,4)):
            g=heads[0]//4
            assert ds[0]==ds[1] and dt[0]==dt[1]
            for d in range(T+1):
                key=plan[:d]
                t=by_seen[g][d]
                if key not in t or row<t[key]:
                    t[key]=row
    out=[]
    for d in range(T+1):
        a,b=(by_seen[g][d] for g in (0,1))
        common=a.keys()&b.keys()
        out.append(min((max(a[k][0],b[k][0]),k,(a[k],b[k])) for k in common) if common else None)
    return values,out

def state_dynamics(mask,axis):
    states={(FIRST,FIRST,(U,U))}
    for _ in range(T):
        after=set()
        for a,b,c in states:
            for cmd in COMMANDS:
                if not slew(c,cmd,axis):
                    continue
                x=transition(a,0,cmd,mask);y=transition(b,1,cmd,mask)
                if x is not None and y is not None:
                    after.add((x,y,cmd))
        states=after
    scores={}
    for x,y,_ in states:
        r=final((x,y))
        if r:
            heads,d=r
            if heads not in scores or d<scores[heads]:
                scores[heads]=d
    return scores

def main():
    counts=0
    reports={}
    for mask,axis in product(range(4),(0,1,2)):
        result,by_delay=direct(mask,axis)
        assert {k:v[0] for k,v in result.items()}==state_dynamics(mask,axis)
        assert [v[0] if v else None for v in by_delay]==[36,36,36,None,None,None]
        assert (4,0) not in result
        counts+=len(result)
        reports[f"{mask}/{axis}"]=result.get((0,4))
    assert [reports[f"{mask}/1"][0] if reports[f"{mask}/1"] else None
            for mask in range(4)]==[None,None,44,40]
    _,branch=direct(0,1)
    _,pref,goals=branch[2]
    assert all(r[1][:2]==pref for r in goals)
    sequences=[]
    for mask in (2,3):
        sequences.append((mask,1,0,reports[f"{mask}/1"]))
    for g,row in enumerate(goals):
        sequences.append((0,1,1+g,row))
    if sys.argv[1:]==["--rows"]:
        for mask,axis,case,row in sequences:
            _,plan,pair=row
            for w,t in enumerate(pair):
                print(mask,axis,case,w,*(v for a in plan for v in a),*t[2:])
        return
    print(json.dumps(dict(grid=12,matched_heading_queries=counts,
                         complete_goal_notice=[36,36,36,None,None,None],
                         branch_at_two=branch[2],correlated=reports),sort_keys=True))
if __name__=="__main__":
    main()
