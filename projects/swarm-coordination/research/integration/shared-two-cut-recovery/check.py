"""Shared two-cut policy synthesis and independent extensional comparator."""
from itertools import product, combinations
from pathlib import Path
from subprocess import check_output
import sys

def table(path):
    d={}
    for line in Path(path).read_text().splitlines():
        key,*raw=line.split()
        d[tuple(key)]=tuple(map(int,raw))
    assert len(d)==18
    return d

def local_cut(row, use_alternate_evidence):
    # The decision bit is the fresh successful-delivery observation.
    # The optional second bit is an installed alternate preparation witness.
    return tuple([row[0],row[3]] if use_alternate_evidence else [row[0]])

def local_actions(rows):
    return frozenset(a for a,done in rows.items() if done)

def solve(rows,worlds,early_view,use_alternate_evidence):
    """One locally realizable strategy, or an empty choice cell."""
    policy={}
    unresolved={}
    for v in sorted(set(early_view(w) for w in worlds)):
        fiber=[w for w in worlds if early_view(w)==v]
        for early in 'wp':
            classes={}
            for w in fiber:
                obs=local_cut(rows[w,early,'s'],use_alternate_evidence)
                if obs[0]:continue
                A=local_actions({a:rows[w,early,a][1] for a in 'sab'})
                classes.setdefault(obs,[]).append((w,A))
            meet={o:set.intersection(*(set(A) for _,A in picks)) for o,picks in classes.items()}
            if all(meet.values()):
                policy[v]=early,{o:min(A) for o,A in meet.items()}
                break
            unresolved[v,early]={o:sorted(w for w,_ in classes[o]) for o,A in meet.items() if not A}
        if v not in policy:
            return None,unresolved
    return policy,unresolved

def oracle(rows,worlds,early_view,extra):
    # Enumerates all local deterministic response tables. No use of the
    # factored cell/intersection implementation.
    prefix=sorted(set(early_view(w) for w in worlds))
    for word in product('wp',repeat=len(prefix)):
        first=dict(zip(prefix,word))
        reached=set()
        for w in worlds:
            v=early_view(w);e=first[v]
            o=local_cut(rows[w,e,'s'],extra)
            reached.add((v,o))
        reached=sorted(reached)
        for response in product('sab',repeat=len(reached)):
            reg=dict(zip(reached,response))
            if all(rows[w,(e:=first[v:=early_view(w)]),reg[v,local_cut(rows[w,e,'s'],extra)]][1]
                   for w in worlds):
                return True
    return False

def apply(rows,policy,w,view,extra):
    e,second=policy[view(w)]
    o=local_cut(rows[w,e,'s'],extra)
    l='s' if o[0] else second[o]
    a,b,claim,copy=rows[w,e,l]
    return e,l,a,b,claim,copy

def main():
    W=table('warehouse.tsv'); N=table('network.tsv')
    assert set(W)==set(N)
    for k,w in W.items():
        n=N[k]
        assert (w[0],w[1],w[2]*3,w[3])==n
    worlds='GFZ'
    controls=0
    for rows in (W,N):
        for m in range(1,4):
            for subset in combinations(worlds,m):
                for bits in product((0,1),repeat=len(subset)):
                    v=dict(zip(subset,bits)).__getitem__
                    for extra in (False,True):
                        policy,bad=solve(rows,subset,v,extra)
                        assert bool(policy)==oracle(rows,subset,v,extra)
                        if policy:
                            assert all(apply(rows,policy,w,v,extra)[3] for w in subset)
                        controls+=1
    eq=lambda _:0
    pass_both,why=solve(W,'GF',eq,False)
    assert pass_both=={0:('p',{(0,):'b'})}
    impossible,why=solve(W,'GFZ',eq,False)
    assert impossible is None
    assert why=={(0,'w'):{(0,):['F','G','Z']},(0,'p'):{(0,):['F','Z']}}
    print('same abstract native transitions',len(W),'per source')
    print('same-information existential policy comparisons',controls)
    print('joint successful strategy (early and recovery)',pass_both)
    print('warehouse witnesses',[apply(W,pass_both,w,eq,False) for w in 'GF'])
    print('relay witnesses',[apply(N,pass_both,w,eq,False) for w in 'GF'])
    print('both losing prefixes for opaque Z',why)
    if len(sys.argv)==2:
        first,second=pass_both[0]
        args=[first,second[0,]]
        Nactual=check_output([sys.argv[1],*args],text=True)
        Wactual=check_output([sys.executable,'-B','warehouse.py',*args],text=True)
        assert Nactual=='Gps 1 1 3 0\nFpb 0 1 3 1\n'
        assert Wactual=='Gps 1 1 1 0\nFpb 0 1 1 1\n'
        print('synthesized policy executed from native observations in both plants')
    # A genuinely observed early distinction of Z is a hypothetical condition,
    # not supplied by these native sources or claimed by this work.
if __name__=='__main__':
    main()
