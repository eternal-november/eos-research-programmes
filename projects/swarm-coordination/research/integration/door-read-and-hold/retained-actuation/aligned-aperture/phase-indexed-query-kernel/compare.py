"""Exact task-relative profile kernel under a prospective phase menu."""
import json
from pathlib import Path
import sys
from collections import defaultdict

def source(path):
    result={}
    for line in Path(path).read_text().splitlines():
        a,b,c,*p=map(int,line.split())
        assert len(p)==24
        assert (a,b,c) not in result
        result[a,b,c]=tuple(p)
    assert len(result)==203
    return result

def classes(keys,C):
    groups=defaultdict(set)
    for k in keys:groups[C[k]].add(k)
    return groups

def main():
    p=source(sys.argv[1]); keys=tuple(sorted(p))
    # Joint environment can independently take or omit each requested pulse.
    z={k:tuple(map(max,zip(p[k],p[k[0],0,0]))) for k in keys}
    def peak(left,right):return max(a+b for a,b in zip(z[left],z[right]))
    M={(x,y):peak(x,y) for x in keys for y in keys}
    def check(band):
        cert={k:tuple(M[k,j] for j in keys if j[1]<=band) for k in keys}
        sizes=len(classes(keys,cert))
        return sizes,cert
    curve=[(b,*check(b)[:1]) for b in (0,1,3,5,7,9,11,13)]
    assert curve==[(0,94),(1,158),(3,158),(5,158),(7,158),(9,158),(11,159),(13,159)]
    _,old=check(5);_,new=check(13)
    oldgroups=classes(keys,old);newgroups=classes(keys,new)
    split=[sorted(C) for C in oldgroups.values() if len({new[x] for x in C})>1]
    assert split==[[(3,3,3),(5,5,2)]]
    a,b=split[0]
    for y in keys:
        for level in sorted({M[a,y],M[b,y]}):
            assert ((M[a,y]<=level)!=(M[b,y]<=level))==(min(M[a,y],M[b,y])<=level<max(M[a,y],M[b,y]))
    repl=[(y,M[a,y],M[b,y]) for y in keys if M[a,y]!=M[b,y]]
    assert ((0,11,4),38,36) in repl
    # Before replacement, retained command depth is a material computable
    # source distinction on the only fibre that will split. This already
    # exists in the staged profile fixture; a fleet OPEN report does not
    # give it to the architecture. No future leaf motion is observed.
    def repair(k):
        return old[k],(int(k[0]>4) if k in split[0] else None)
    decode={}
    for k in keys:
       g=repair(k)
       assert g not in decode or decode[g]==new[k]
       decode[g]=new[k]
    assert len(decode)==len(newgroups)==159
    assert all(decode[repair(k)]==new[k] for k in keys)
    print(json.dumps(dict(raw_keys=len(keys),traces=len(set(z.values())),questions=len(M),
                          classes=curve,split=split,new_discriminators=repl),sort_keys=True))
if __name__=="__main__":main()
