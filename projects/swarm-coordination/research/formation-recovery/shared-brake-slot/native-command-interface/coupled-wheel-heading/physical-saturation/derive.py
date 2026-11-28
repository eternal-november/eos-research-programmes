#!/usr/bin/env python3
"""Exact blind viability with stipulated wheelwise saturating response."""
from itertools import product
import json,sys

bounds=((1,2),(2,1))

def transition(s,w,request,mask):
    left,right,x,y=s
    values=[]
    for idx,(v,b,c) in enumerate(zip((left,right),bounds[w],request)):
        # Command itself must never request acceleration in either world.
        if c>v or (v-c>b and not (mask&(1<<idx))):
            return None
        values.append(max(v-b,c))
    a,b=values
    return a,b,x+left+a,y+right+b

def commands(u):
    return tuple(product(range(u+1),repeat=2))

def solve(u,h,mask):
    first=(u,u,0,0)
    reached={(first,first):()}
    actions=commands(u)
    for _ in range(h):
        new={}
        for ds,plan in reached.items():
            for a in actions:
                z=tuple(transition(s,w,a,mask) for w,s in enumerate(ds))
                if None not in z:
                    q=plan+(a,)
                    if z not in new or q<new[z]:
                        new[z]=q
        reached=new
    return reached

def table(states):
    best={}
    for ds,plan in states.items():
        if not all(s[:2]==(0,0) for s in ds):
            continue
        heads=tuple(s[3]-s[2] for s in ds)
        score=max(s[2]+s[3] for s in ds)
        key=score,plan,ds
        if heads not in best or key<best[heads]:
            best[heads]=key
    return best

def no_accel_profile(s,w,plan,mask):
    # Independent simple per-wheel recurrence over desired sequences.
    speed=[[],[]]
    for i in range(2):
        value=s
        for a in plan:
            v=a[i]
            if v>value:
                return None
            remaining=value-v
            if remaining>bounds[w][i] and not (mask&(1<<i)):
                return None
            nxt=value-min(remaining,bounds[w][i])
            speed[i].append(nxt)
            value=nxt
    if speed[0][-1] or speed[1][-1]:
        return None
    return (0,0,s+2*sum(speed[0][:-1]),s+2*sum(speed[1][:-1]))

def enumerate_direct(u,h,mask):
    best={}
    # The single-wheel causal recurrence can be enumerated as two
    # independent target vectors before checking their shared mission.
    histories=[]
    for idx in (0,1):
        ans=[]
        for word in product(range(u+1),repeat=h):
            values=[]
            for w in range(2):
                x=u; dist=0
                for cap_req in word:
                    b=bounds[w][idx]
                    if cap_req>x or (x-cap_req>b and not(mask&(1<<idx))):
                        break
                    nxt=max(cap_req,x-b)
                    dist+=x+nxt
                    x=nxt
                else:
                    if x==0:
                        values.append(dist)
            if len(values)==2:
                ans.append((word,values))
        histories.append(ans)
    for (l,x),(r,y) in product(*histories):
        heads=y[0]-x[0],y[1]-x[1]
        z=max(x[0]+y[0],x[1]+y[1])
        if heads not in best or z<best[heads]:
            best[heads]=z
    return best

def example():
    plan=((3,3),(2,1),(0,1),(0,1),(0,0))
    pair=tuple(no_accel_profile(4,w,plan,3) for w in range(2))
    assert pair==((0,0,16,16),(0,0,14,18))
    chosen={1:((3,3),(1,2),(0,1),(0,0),(0,0)),
            2:((3,2),(2,2),(1,2),(0,0),(0,0)),
            3:plan}
    examples=[(0,table(solve(4,5,0)).get((0,4)))]
    for mask,seq in chosen.items():
        assert all(x>=u and y>=v for (x,y),(u,v) in zip(seq,seq[1:]))
        signals=tuple(no_accel_profile(4,w,seq,mask) for w in range(2))
        assert tuple(y-x for _,_,x,y in signals)==(0,4)
        cost=max(x+y for _,_,x,y in signals)
        assert cost==table(solve(4,5,mask))[(0,4)][0]
        examples.append((mask,(cost,seq,signals)))
    return examples

def main():
    examples=example()
    assert [r[0] if r else None for _,r in examples]==[None,32,36,32]
    if sys.argv[1:]==["--rows"]:
        for mask,row in examples:
            if row:
                for w,expected in enumerate(row[2]):
                    print(mask,w,*(v for cmd in row[1] for v in cmd),*expected[2:])
        return
    cases=compared=0
    for u,h,mask in product(range(2,6),range(3,7),range(4)):
        candidate={k:v[0] for k,v in table(solve(u,h,mask)).items()}
        ref=enumerate_direct(u,h,mask)
        assert candidate==ref,(u,h,mask,candidate,ref)
        cases+=1
        compared+=len(ref)
    print(json.dumps(dict(scope_cases=cases,heading_pairs_compared=compared,
                          model_witnesses=examples),sort_keys=True))
if __name__=="__main__":
    main()
