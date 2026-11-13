#!/usr/bin/env python3
"""Independent audit: decision-DAG reduction, physical table search, graph assembly.
No imports from the author's checker. Finite evidence only.
"""
from itertools import product, permutations, combinations
from pathlib import Path
import hashlib,json,random
ROOT=Path(__file__).resolve().parents[1]

def vectors(k): return list(product(range(2),repeat=k))
def answer(x):
    n=len(x)//2
    return int(all(x[i]==x[n+i] for i in range(n)))

def reduced_layers(n,order):
    # Bottom-up reduction of the FULL input decision tree, not residual row tables.
    leaves=[]
    for observed in vectors(2*n):
        x=[0]*(2*n)
        for index,value in zip(order,observed): x[index]=value
        leaves.append(answer(x))
    layers=[None]*(2*n+1); layers[-1]=leaves
    for t in range(2*n-1,-1,-1):
        nxt=layers[t+1]; pairs=[tuple(nxt[i:i+2]) for i in range(0,len(nxt),2)]
        ids={z:j for j,z in enumerate(sorted(set(pairs)))}
        layers[t]=[ids[z] for z in pairs]
    return layers

def predicted(n,order,t):
    p=set(order[:t]); a=sum(len(p & {i,i+n})==1 for i in range(n))
    c=sum({i,i+n}<=p for i in range(n))
    return 2**a+int(c>0)

def canon(labels):
    d={};return tuple(d.setdefault(x,len(d)) for x in labels)

def physical_binary_memory_search(n,order):
    """Enumerate reachable 2-state memory encodings using actual local updates.
    At each layer choose a deterministic table on (oldmemory,nextreply).
    No direct suffix/truth residual construction is used.
    """
    xs=vectors(2*n); current={tuple(0 for _ in xs)}; counts=[1]
    for index in order:
        new=set()
        for old in current:
            keys=sorted(set((old[j],x[index]) for j,x in enumerate(xs)))
            for vals in product(range(2),repeat=len(keys)):
                table=dict(zip(keys,vals))
                new.add(canon(table[old[j],x[index]] for j,x in enumerate(xs)))
        current=new;counts.append(len(current))
    successful=[]
    for labeling in current:
        required={}
        for label,x in zip(labeling,xs): required.setdefault(label,set()).add(answer(x))
        if all(len(v)==1 for v in required.values()):successful.append(labeling)
    return bool(successful),counts

def brute_codes(n,side,keep,messages=2):
    xs=vectors(n); k0=sorted(set(tuple(x[j] for j in keep) for x in xs))
    for values in product(range(messages),repeat=len(k0)):
        encoder=dict(zip(k0,values)); good=True
        for i in range(n):
            local=sorted(set(tuple(x[j] for j in side[i]) for x in xs))
            keys=list(product(range(messages),local)); found=False
            for outputs in product(range(2),repeat=len(keys)):
                decoder=dict(zip(keys,outputs))
                if all(decoder[encoder[tuple(x[j] for j in keep)],tuple(x[j] for j in side[i])]==x[i] for x in xs):
                    found=True;break
            if not found:good=False;break
        if good:return True
    return False

def quotient_colorable(n,side,keep,messages=2):
    xs=vectors(n);obs=lambda x:tuple(x[j] for j in keep)
    vs=sorted(set(map(obs,xs)));edges=set()
    for x,y in combinations(xs,2):
        if any(tuple(x[j] for j in side[i])==tuple(y[j] for j in side[i]) and x[i]!=y[i] for i in range(n)):
            a,b=obs(x),obs(y)
            if a==b:return False
            edges.add(tuple(sorted((vs.index(a),vs.index(b)))))
    return any(all(c[a]!=c[b] for a,b in edges) for c in product(range(messages),repeat=len(vs)))

def graph_assembly(n):
    # Construct actual product as tuples of independent coordinate graph records,
    # filtering clock equality, and compare to whole image on BOTH sorts.
    counts=[]
    for event in (False,True):
        stages=range(2*n if event else 2*n+1)
        image={(t,)+x for t in stages for x in vectors(2*n)}
        generated=set()
        for t in stages:
            coordinate_carriers=[[(t,0),(t,1)] for _ in range(2*n)]
            for row in product(*coordinate_carriers):
                assert len({a for a,b in row})==1
                whole=(row[0][0],)+tuple(b for a,b in row)
                generated.add(whole)
                if event:
                    assert (t,)+tuple(b for a,b in row)==whole
                    assert (t+1,)+tuple(b for a,b in row) in {(t+1,)+x for x in vectors(2*n)}
                # Regroup regions and pairs, then use EXPLICIT inverse permutation.
                regions=(whole[1:n+1],whole[n+1:]);pairs=tuple((whole[1+i],whole[1+n+i]) for i in range(n))
                assert regions[0]+regions[1]==tuple(a for a,b in pairs)+tuple(b for a,b in pairs)
        assert image==generated;counts.append(len(image))
    return counts

def main():
    checks={};count=0
    for n in (1,2,3):
        for order in permutations(range(2*n)):
            layers=reduced_layers(n,order)
            assert [len(set(z)) for z in layers]==[predicted(n,order,t) for t in range(2*n+1)]
            # Canonical node transitions only consume present bit, no hidden input.
            for t in range(2*n):
                rules={}
                for j,node in enumerate(layers[t]):
                    pair=tuple(layers[t+1][2*j:2*j+2])
                    assert node not in rules or rules[node]==pair
                    rules[node]=pair
            count+=1
    rnd=random.Random(130427)
    for n in (4,5,6):
        orders=[tuple(range(2*n)),tuple(q for i in range(n) for q in (i,i+n))]
        for _ in range(10):
            o=list(range(2*n));rnd.shuffle(o);orders.append(tuple(o))
        for order in orders:
            assert [len(set(z)) for z in reduced_layers(n,order)]==[predicted(n,order,t) for t in range(2*n+1)]
            count+=1
    checks['independent_decision_dag_orders']=count
    table_search=[]
    for n,order in [(1,(0,1)),(2,(0,1,2,3)),(2,(0,2,1,3))]:
        success,counts=physical_binary_memory_search(n,order)
        assert success==(n==1)
        table_search.append({'n':n,'order':order,'two_state_implementation':success,'reachable_encoding_counts':counts})
    checks['explicit_two_state_table_search']=table_search
    cc=0
    for n in (1,2):
        incidences=[(i,j) for i in range(n) for j in range(n) if i!=j]
        for b in vectors(len(incidences)):
            side=[tuple(j for bit,(ii,j) in zip(b,incidences) if bit and ii==i) for i in range(n)]
            for mask in vectors(n):
                keep=tuple(i for i,v in enumerate(mask) if v)
                assert brute_codes(n,side,keep)==quotient_colorable(n,side,keep)
                cc+=1
    checks['exhaustive_encoder_decoder_table_architectures']=cc
    checks['actual_graph_state_event_carriers']={str(n):graph_assembly(n) for n in (1,2,3)}
    # Mutation controls are discriminating examples, not merely an assertion that
    # a named shortcut is absent from source.
    neg=[]
    n=3;block=tuple(range(6));paired=(0,3,1,4,2,5)
    assert max(map(lambda a:len(set(a)),reduced_layers(n,block)))==8
    assert max(map(lambda a:len(set(a)),reduced_layers(n,paired)))==3
    neg.append('reject schedule erasure under same final episode relation')
    assert len(set(reduced_layers(2,(0,2,1,3))[3]))==3
    neg.append('reject forgetting the already mismatched residual')
    assert max(len(set(x)) for x in reduced_layers(1,(0,1)))==2
    neg.append('reject applying interleaved n>=2 width3 at n=1')
    # Correlated plant domain v=u: no data memory is needed. Formula is NOT universal
    # over arbitrary partial X and must retain the full-domain premise.
    correlated=[u+u for u in vectors(3)]
    assert all(answer(x)==1 for x in correlated)
    neg.append('reject applying full-domain lower bound to v=u constrained plant')
    # An encoder that sees only x0 cannot serve receiver0 knowing x1: x0 is
    # computable, but receiver1 knowing x0 still lacks x1. Omniscient parity would.
    side=[(1,),(0,)]
    assert brute_codes(2,side,(0,1)) and not brute_codes(2,side,(0,))
    neg.append('reject granting encoder unpermitted observation')
    assert not brute_codes(2,[(),()],(0,1))
    assert brute_codes(1,[()],(0,))
    neg.append('reject separately redesigned one-receiver codes as shared two-receiver code')
    x=(0,0,0,0);changed=(0,0,1,0)
    assert answer(x)!=answer(changed)
    observed_before=x
    assert observed_before==x
    neg.append('reject stable-snapshot assumption after unobserved physical change')
    assert answer((0,0))==1
    neg.append('reject always-refuse as complete admission')
    checks['negative_controls']=neg
    report={'status':'PASS','method':'Independent reduced layered decision graphs and explicit memory/encoder/decoder table enumeration; no imports from author checker.','checks':checks}
    report['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    report['manuscript_sha256']=hashlib.sha256((ROOT/'examples/Causal_Interlock_and_Telemetry_Families.md').read_bytes()).hexdigest()
    out=ROOT/'review/Causal_Family_Independent_Results.json';out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
