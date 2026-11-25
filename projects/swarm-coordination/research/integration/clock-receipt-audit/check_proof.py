"""Independent integer verifier, no import of timing graph solvers."""
from itertools import product
from pathlib import Path
import json

def good(a,s):
    return all(s[v]<=s[u]+b for u,v,b in a)

def check(d):
    n=d['n']; B=d['base'];R=d['routes']
    if 'schedule' in d:
        s=d['schedule']
        assert len(s)==n and good(B,s) and not any(good(z,s) for z in R)
        return 'rejected by explicit schedule'
    assert len(d['base_example'])==n and good(B,d['base_example'])
    claims=d['cycles']
    assert set(tuple(indices) for indices,_ in claims)==set(product(*(range(len(z)) for z in R)))
    for indices,ks in claims:
        ext=B[:]
        for route,k in zip(R,indices):
            u,v,t=route[k];ext.append([v,u,-t-1])
        cycle=[ext[k] for k in ks]
        assert cycle
        assert all(x[1]==y[0] for x,y in zip(cycle,cycle[1:]+cycle[:1]))
        assert sum(e[2] for e in cycle)<0
    return 'certified for every calibrated trace'

if __name__=='__main__':
    for d in json.loads(Path('certificates.json').read_text()):
        print(d['case']+': '+check(d))
