"""A physical discharge witness can replace clock time only under its own law."""
from dataclasses import replace
from source import scenario,step
from timed_evidence import opt
from collections import defaultdict
from functools import lru_cache
from random import Random
from math import inf

def optimum_with_physical_record(models,observe):
    # Compile commands using conditional cells of actual observation tokens.
    # Actual time remains source-side data; it never enters a local read
    # except through observe, which is a declared typed supplier.
    n=len(models[0])
    @lru_cache(None)
    def go(rows,rs):
        options=[]
        for i in rs:
            scored=[];bb=defaultdict(list)
            for key,prior in rows:
                physical=models[key][i]
                actual,dur,_=step(physical,i)
                total=prior+dur
                if actual:scored.append(total)
                else:bb[observe(physical,dur)].append((key,total))
            next=tuple(k for k in rs if k!=i)
            options.append(max(scored+[go(tuple(branch),next) for branch in bb.values()]))
        return min(options,default=inf)
    return go(tuple((i,0) for i in range(len(models))),tuple(range(n)))

def four():
    rows=(
        ((False,1),(True,1),(False,5)),
        ((False,2),(False,5),(True,1)),
        ((True,1),(False,5),(False,5)))
    stable=tuple(tuple(scenario('power',r) for r in row) for row in rows)
    drift=[list(row) for row in stable]
    drift[0][0]=replace(drift[0][0],residual=6,rate=6)
    drift=tuple(tuple(row) for row in drift)
    amount=lambda model,_:model.residual
    time=lambda _,dur:dur
    scoped=lambda model,_:(model.residual,model.rate)
    one_bit=lambda model,_:model.residual>=6
    miss=lambda *_:None
    for models,answer in ((stable,3),(drift,7)):
        assert optimum_with_physical_record(models,time)==3
        assert optimum_with_physical_record(models,amount)==answer
        assert optimum_with_physical_record(models,one_bit)==answer
        assert optimum_with_physical_record(models,scoped)==3
        assert optimum_with_physical_record(models,miss)==7
    print('at fixed drain rate one bit of material evidence replaces the clock; a real rate change can erase that distinction')
    rng=Random(60112)
    for _ in range(400):
        matrices=tuple(tuple((bool(rng.randrange(2)),rng.randrange(1,7))
                             for _ in range(4)) for k in range(rng.randrange(2,6)))
        for plant in ('dock','power'):
            models=tuple(tuple(scenario(plant,r) for r in row) for row in matrices)
            assert optimum_with_physical_record(models,time)==opt(matrices,True)[0]
            assert optimum_with_physical_record(models,amount)==opt(matrices,True)[0]
    print('800 actual-source diagnostic comparison cases under a fixed tagged-rate law')
if __name__=='__main__':four()
