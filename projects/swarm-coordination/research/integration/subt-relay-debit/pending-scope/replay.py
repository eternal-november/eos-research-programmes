"""Compute direct trace reference and exact common authorized cutoff."""
from itertools import product
from math import nextafter,inf
import json
import subprocess
import sys
from engine import assess,choose

H=(.75,.875)
CUTS=(.25,.5,.75,.875,1.,nextafter(1.,inf),1.25,1.75,1.875,2.)
MODES=tuple(product((0,1),repeat=2))
def src(v):
    return (' '.join(map(str,v))+'\n').encode()

def run(binary):
    raw=[]
    parameters=[]
    for c in range(2,9):
        for a,b,x in product(range(1,c),range(1,c),range(1,c+1)):
            if a+b>c:continue
            for h in H:
                parameters.append((c,a,b,x,h))
                for t,(s,r) in product(CUTS,MODES):
                    raw.append((c,a,b,x,h,t,s,r))
    extra=[(*v,cp,cq,cr) for v in [(6,2,2,2,.75,t,s,r)
                                 for t,(s,r) in product(CUTS,MODES)]
           for (cp,cq),cr in product(((5,6),(6,5),(6,6)),(3,7))]
    encoded=[(*x,x[0],x[0],x[0]) for x in raw]+extra
    capture=subprocess.run([binary],input=b''.join(map(src,encoded)),stdout=subprocess.PIPE,check=True)
    data={}
    def bounded_sim(C,a,b,x,h,t,s,r,cp=None,cq=None,cr=None):
        sender={};recv={};out={}
        cap={"P":C if cp is None else cp,"Q":C if cq is None else cq, "R":C}
        items=[(0.,0,'P','A',a),(.125,1,'R','D',1),
               (h,2,'P' if s else 'Q','A' if r else 'B',b),
               (t,3,'P','A',x)]
        for at,k,who,where,size in sorted(items):
            tx=sender.setdefault(who,[]);rx=recv.setdefault(where,[])
            fits=lambda seq,limit:sum(n for when,n in seq if when>=at-1)+size<=limit
            out[k]=False
            if fits(tx,cap[who]):
                tx.append((at,size))
                if fits(rx,cap[who]):
                    rx.append((at,size));out[k]=True
        return tuple(out[q] for q in (0,2,3,1))
    lines=capture.stdout.decode().splitlines()
    assert len(lines)==len(raw)+len(extra)
    for key,line in zip(raw,lines[:len(raw)],strict=True):
        vals=tuple(bool(int(x)) for x in line.split())
        assert vals==bounded_sim(*key), (key,vals)
        assert vals[:1]==(True,) and vals[-1:]==(True,)
        assert assess(*key[:-2],key[-2:])==vals[1:3],(key,vals)
        data[key]=vals
    controls={}
    for key,line in zip(extra,lines[len(raw):],strict=True):
        vals=tuple(bool(int(x)) for x in line.split())
        assert vals==bounded_sim(*key), (key,vals,bounded_sim(*key))
        _,_,_,_,h,t,s,r,cp,cq,cr=key
        # If only the receiver's configured radio changes while it never
        # transmits, all four physical receipts are unchanged.
        prior_control=controls.setdefault((cp,cq,s,r,t),vals[1:3])
        assert prior_control==vals[1:3],key
    assert controls[5,6,1,0,.5]==(False,True) and controls[5,6,0,1,.5]==(True,True)
    assert controls[6,5,0,1,.5]==(False,True) and controls[6,5,1,0,.5]==(True,True)
    ref=0; risk=0; comparisons={}
    for args in parameters:
        for mask in range(16):
            admit=tuple(m for i,m in enumerate(MODES) if mask>>i&1)
            for d in (.5,.875,1.,1.25,2.):
                times=tuple(t for t in CUTS if t<=d)
                chosen=choose(*args,times,admit)
                exact=next((t for t in times if admit and all(all(data[(*args,t,*m)]) for m in admit)),None)
                assert chosen==exact
                ref+=1
        for t in CUTS:
            if t<args[-1] and data[(*args,t,0,0)][2]:
                risk+=sum(not data[(*args,t,*m)][1] for m in MODES)
    example=(5,2,2,3,.75)
    for s,r in MODES:
        comparisons[f'{s}-{r}']={str(t):data[(*example,t,s,r)] for t in (.5,.75,1.,nextafter(1.,inf),1.25)}
    for t in (.5,.75,1.,nextafter(1.,inf),1.25):
        assert len({data[(*example,t,*m)] for m in MODES if any(m)})==1
    assert choose(*example,(.5,),((0,0),))==.5
    assert choose(*example,(.5,),MODES) is None
    assert choose(*example,CUTS,MODES)==nextafter(1.,inf)
    print(json.dumps(dict(native_effect_rows=len(raw),common_cut_rows=ref, unequal_capacity_rows=len(extra),
                          equal_overlap_not_equal_capacity={str(k):v for k,v in controls.items() if k[-1]==.5},
                          new_currently_affordable_but_loses_old=risk,example=comparisons),
                     sort_keys=True,indent=2))

if __name__=='__main__':run(sys.argv[1])
