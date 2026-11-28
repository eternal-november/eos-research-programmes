from hashlib import sha256
from pathlib import Path
import json,sys
from math import isqrt
from decimal import Decimal as D
import survey,ride
from positive_discovery import boxzonotope

def read():
    f=Path(sys.argv[3])
    p=json.loads(f.read_text())
    assert set(p)=={"A","B"}
    m={}
    for k,a in p.items():
        m[k]=[tuple(q) for q in a["polyline"]]
    return m

def main():
    survey.verify();T,poses,types,tiles=survey.source()
    domain=set(ride.read_lut(set(poses)))
    assert len(domain)==138777
    m=survey.Map(T,[])
    q=read()
    expected=(275,-175,2),(350,-300,13)
    result={}
    for label,closed in (("A",(118,132)),("B",(117,132))):
        path=q[label]
        assert all(len(p)==3 and all(type(x) is int for x in p) and p in domain for p in path)
        assert (path[0],path[-1])==expected
        edges=list(zip(path,path[1:]))
        m.fences=[ride.closures[closed]]
        assert all(ride.within(u,v,domain) for u,v in edges)
        pad=[]
        for r in map(D,(".3005",".301",".302",".305",".31",".32")):
            if all(boxzonotope(m,u,v,True,r) for u,v in edges):pad.append(str(r))
        assert pad and pad[0]==".3005" or pad and pad[0]=="0.3005"
        def metres(u,v):
           n=sum((a-b)**2 for a,b in zip(u,v))*10**12
           x=isqrt(n)
           return x+int(x*x!=n)
        result[label]=dict(upper_um=2*sum(metres(u,v) for u,v in edges),
                            legs=len(edges),padding_checks=pad)
    p=json.loads(Path(sys.argv[3]).read_text())
    assert all(result[a]["upper_um"]==p[a]["up_um"] for a in result)
    lower=json.loads(Path(sys.argv[4]).read_text())
    hi=max(item["upper_um"] for item in result.values())
    low=lower["local_lower"]
    # Compare exact displayed numerator units; D=20e6 per metre.
    assert lower["dual_denominator"]==20000000
    assert hi*20<low
    print(json.dumps(dict(upper=result,upper_um=hi,local_lower_numer=low,
                 certified_gap_numer=low-20*hi,denom=20000000),sort_keys=True))
if __name__=="__main__":main()
