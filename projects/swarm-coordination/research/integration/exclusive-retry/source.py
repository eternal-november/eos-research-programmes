"""Two effect-side suppliers and an explicitly scoped one-shot guard."""
from dataclasses import dataclass
from itertools import product
from timed_evidence import opt

@dataclass(frozen=True)
class Physical:
    resource: str
    # Available true means the effect may commit. A failed attempt requires
    # converting a retained physical obstruction; no command cancels it.
    available: bool
    stroke: int
    residual: int
    rate: int

def step(model,old_generation):
    t=0;budget=model.stroke if model.available else model.residual
    trace=[(0,old_generation,'entered')]
    while budget>0:
        t+=1
        if model.available:
            budget-=1
            trace.append((t,old_generation,'advance physical effect'))
        elif model.resource=='dock':
            budget-=model.rate
            trace.append((t,old_generation,'retract obstruction'))
        elif model.resource=='power':
            budget-=model.rate
            trace.append((t,old_generation,'drain physical current'))
        else:raise ValueError(model.resource)
    if model.available:
        trace.append((t,old_generation,'durable effect committed'))
    else:
        trace.append((t,old_generation,'verified no remaining occupation'))
    return model.available,t,tuple(trace)

def scenario(plant,law):
    ok,dur=law
    rate=1 if plant=='dock' else 3
    return Physical(plant,ok,dur if ok else 2,1 if ok else dur*rate,rate)

def same_policy_different_plant(worlds):
    for plant in ('dock','power'):
        source=tuple(tuple(step(scenario(plant,r),i) for i,r in enumerate(w)) for w in worlds)
        projected=tuple(tuple(tr[:2] for tr in w) for w in source)
        assert projected==worlds
        for w in source:
            for i,(committed,d,s) in enumerate(w):
                assert s[0]==(0,i,'entered')
                assert (d,i,'durable effect committed' if committed else
                               'verified no remaining occupation')==s[-1]
        assert opt(projected,True)[0]==3
        assert opt(projected,False)[0]==7

def post_guard(cert,scope,gen):
    # Model authoritative physical attestation only; no authentication claim.
    return cert is not None and cert==(scope,gen,'released-without-commit')

def main():
    n=0
    for plant,ok,d,v,i in product(('dock','power'),(False,True),range(1,10),range(1,5),range(1,10)):
        available,t,trace=step(Physical(plant,ok,d,i*v,v),7)
        assert available==ok and t==(d if ok else i)
        n+=1
    print(n,'physical-event-source and typed time-bound checks')
    worlds=(
        ((False,1),(True,1),(False,5)),
        ((False,2),(False,5),(True,1)),
        ((True,1),(False,5),(False,5)))
    same_policy_different_plant(worlds)
    for old_committed in (False,True):
        # Both branches can look idle. Retry passes safety and one-shot
        # completion exactly when it is the opposite of old commit.
        assert (not old_committed)==post_guard(('hand',3,'released-without-commit' if not old_committed
                                                else 'old-effect-committed'),'hand',3)
        assert not post_guard(('hand',2,'released-without-commit'),'hand',3)
        assert not post_guard(('other',3,'released-without-commit'),'hand',3)
        assert not post_guard(('hand',3,'now idle'),'hand',3)
    assert all(any(retry==old for old in (False,True)) for retry in (False,True))
    print('physical release alone does not certify a retry after an unobserved completed effect')
if __name__=='__main__':main()
