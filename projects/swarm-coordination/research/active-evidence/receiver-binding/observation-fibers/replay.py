"""Re-run pinned native callbacks; model the observation relay afterward."""
from itertools import product
from pathlib import Path
from subprocess import run
import json
import sys

from fiber import Trace, candidates, projection_then_expand, support_index, verdict


def direct(c,q,p,x,y,z,same,shared,drop):
    """Independent capacity calculation for the selected native epoch."""
    sent=min(x,p) if x<=p else 0
    used=q if shared else 0
    probe=not drop and bool(sent) and used+x<=p
    if probe:
        used+=x
    sent=sent if same else 0
    paid=[]
    for k in [y,z]:
        start=sent+k<=c
        if start:
            sent+=k
        paid.append(start and used+k<=c)
        if paid[-1]:
            used+=k
    return (probe,*paid)


def report(effect,erase):
    return 'missing' if erase else 'yes' if effect else 'no'


def reference(results,admitted,seen,index):
    # No Trace schema or projection operator: identify outcomes by the
    # corresponding replay rows for each candidate, through raw effect bits.
    output=set()
    for a,d in product(admitted,(0,1)):
        r=results[a,d]; value=r[index+1]
        if seen=='missing' or (r[0] and seen=='yes') or (not r[0] and seen=='no'):
            output.add(value)
    return {frozenset():'inconsistent',frozenset((True,)):'safe',
            frozenset((False,)):'all-bad',frozenset((True,False)):'mixed'}[frozenset(output)]


def gather(binary):
    cases=set()
    for c in range(1,8):
        for q,p,x,y,z,same in product(range(c+1),range(1,c+1),range(1,c+1),
                                      range(1,c+1),range(1,c+1),(0,1)):
            if same and c!=p: continue
            cases.add((c,q,p,x,y,z,same))
    cases=sorted(cases)
    args=[(*params,a,d) for params in cases for a,d in product((0,1),(0,1))]
    data=''.join(' '.join(map(str,row))+'\n' for row in args)
    native=run([binary],input=data,text=True,stdout=-1,check=True)
    outcomes=dict(zip(args,(tuple(bool(int(i)) for i in ln.split()[:3])
                            for ln in native.stdout.splitlines()),strict=True))
    assert all(direct(*a)==outcomes[a] for a in args)
    return cases,outcomes


def campaign(binary):
    cases,outcomes=gather(binary)
    n=changes=0
    by_kind={}
    all_qualified=None
    for p in cases:
        effects={(a,d):outcomes[(*p,a,d)] for a,d in product((0,1),(0,1))}
        rows=[Trace((a,),(d,e),report(r[0],e),r[1:]) for (a,d),r in effects.items()
              for e in (0,1)]
        v=[support_index(rows,i) for i in (0,1)]
        result={}
        for adm,s,i in product(((),(0,),(1,),(0,1)),('no','yes','missing'),(0,1)):
            family=tuple((a,) for a in adm)
            kept=candidates(rows,family,s)
            exact=verdict(kept,i)
            broader=verdict(projection_then_expand(rows,family,s),i)
            assert exact==reference(effects,adm,s,i)
            assert (exact=='inconsistent')==(broader=='inconsistent')
            assert broader==exact or (broader=='mixed' and exact in ('safe','all-bad'))
            guessed=set().union(*(v[i][1][a,s] for a in family))
            assert guessed=={r.paid[i] for r in kept}
            n+=1
            if exact!=broader:
                changes+=1
                kk=f'{s}:{i}:{exact}->{broader}'
                by_kind[kk]=by_kind.get(kk,0)+1
            result[adm,s,i]=(exact,broader)
        if p==(5,2,2,1,2,3,0):
            all_qualified={s:result[(0,),s,1] for s in ('no','yes','missing')}
            assert all_qualified=={'no':('safe','mixed'),'yes':('all-bad','mixed'),
                                   'missing':('mixed','mixed')}
            assert all(result[(0,),s,0][0]=='safe' for s in ('no','yes','missing'))
            assert result[(0,1),'no',1]==('mixed','mixed')
            assert result[(0,1),'yes',1]==('all-bad','mixed')
    print(json.dumps(dict(source_rows=len(outcomes),unique_installed_inputs=len(cases),
                          verdicts=n,forgotten_distinctions=changes,
                          by_observation=by_kind,example_fixed_distinct=all_qualified),
                     indent=2,sort_keys=True))


if __name__=='__main__':
    campaign(sys.argv[1])
