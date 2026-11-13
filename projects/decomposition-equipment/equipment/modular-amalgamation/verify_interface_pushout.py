"""Exhaustive finite-model checks; universal property is proved in companion text."""
import itertools, json
from pathlib import Path

def compose(f,g):
    return tuple(-1 if v == -1 else f[v] for v in g)

def check(m):
    n=m+2; z=m+1
    empty=(-1,)*n
    maps={'0':empty, '1':tuple(range(n)), 'e':tuple(z if i==z else -1 for i in range(n)),
          'c':tuple(0 if i==z else -1 for i in range(n)),
          'u':tuple(z if i==0 else -1 for i in range(n))}
    for s in range(1<<m):
        maps[s]=tuple(i if i==0 or (1<=i<=m and s & (1<<(i-1))) else -1 for i in range(n))
    inv={v:k for k,v in maps.items()}
    assert len(inv)==(1<<m)+5
    mul={(a,b):inv[compose(f,g)] for a,f in maps.items() for b,g in maps.items()}
    A=set(maps)-{'u'}
    assert all(mul[a,b] in A for a in A for b in A)
    triples=0
    for J in range(1<<m):
        def q(a): return 0 if isinstance(a,int) and a & ~J == 0 else a
        elems={q(a) for a in maps}
        assert len(elems)==(1<<m)-(1<<J.bit_count())+6
        qm={}
        for a,b in itertools.product(maps,repeat=2):
            key=q(a),q(b); value=q(mul[a,b])
            assert key not in qm or qm[key]==value
            qm[key]=value
        for a,b,c in itertools.product(elems,repeat=3):
            assert qm[qm[a,b],c]==qm[a,qm[b,c]]
            triples+=1
        B={'0','1','e','c','u',0}
        C=B-{'u'}
        assert len({q(x) for x in B})==6
        assert {q(a) for a in A}&{q(b) for b in B}=={q(c) for c in C}
        assert (len({q(a) for a in A})==len(A)) == (J==0)
        for s in range(1<<m):
            # The literal mixed peak, under d -> y_J.
            assert q(mul[mul[s,'c'],'u'])==q(mul[s,J])
        if J==(1<<m)-1: assert len(elems)==6
    return {'m':m,'interface_embeddings':1<<m,'associativity_triples':triples,'passed':True}

if __name__=='__main__':
    out={'scope':'Finite-model and congruence regression, not a computational proof of universality.',
         'results':[check(m) for m in range(6)]}
    out['total_embeddings']=sum(x['interface_embeddings'] for x in out['results'])
    out['total_associativity_triples']=sum(x['associativity_triples'] for x in out['results'])
    path=Path(__file__).with_suffix('.json'); path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
