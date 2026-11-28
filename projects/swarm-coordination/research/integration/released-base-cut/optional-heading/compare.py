#!/usr/bin/env python3
from itertools import product
from pathlib import Path
import json

def word_dist(u,b,n):
    if not n:
        return {0} if not u else set()
    return {u+v+d for v in range(max(0,u-b),u+1)
            for d in word_dist(v,b,n-1)}

def optional():
    costs=[]
    for L,R in ((1,2),(2,1)):
        allp=list(product(word_dist(4,L,5),word_dist(4,R,5)))
        costs.append([min(x+y for x,y in allp),min(x+y for x,y in allp if x==y)])
    assert costs==[[24,32],[24,32]]
    return costs

def main():
    checked=accepted=updates_during_task=0
    for row in Path(__file__).with_name("NATIVE.txt").read_text().splitlines():
        phase,form,old,new,result,returned,version,after=map(int,row.split())
        allow=not phase if form==0 else bool(phase and old==new)
        known=allow or bool(phase)
        assert result==allow
        assert returned==(old if phase else new) if known else returned==-1
        assert version==(-1 if not known else 1 if phase==2 or not allow else 2)
        assert after==(2 if allow and form==1 else -1)
        if phase and form and {old,new}=={3,4}:
            assert not allow and returned==old
        updates_during_task+=int(phase==2 and allow)
        checked+=1
        accepted+=allow
    assert (checked,accepted,updates_during_task)==(150,35,5)
    print(json.dumps(dict(native_cases=checked,accepted=accepted,
                          accepted_future_appends_during_B=updates_during_task,
                          doubled_paths_sum_absent_vs_zero=optional()),sort_keys=True))
if __name__=="__main__":
    main()
