"""Independent substitution; the frozen receiver/factors and ordinary replay are imported unchanged."""
from pathlib import Path
from collections import Counter
from itertools import product
from hashlib import sha256
import importlib.util
import inspect
import json
import types
import sys

HERE=Path(__file__).resolve().parent
SELECTION='9b8b2cf87e17c7fa327c41ae97bdaa965a94c1531b75a99db4a2830a9a4ff74d'
assert sha256((HERE/'SELECTION.txt').read_bytes()).hexdigest()==SELECTION
for entry in (HERE/'SELECTION.SHA256').read_text().splitlines():
    h,p=entry.split()
    assert sha256((HERE/p).read_bytes()).hexdigest()==h
spec=importlib.util.spec_from_file_location('frozen_interface',HERE.parent/'swarm-c11-interface'/'interface.py')
i=importlib.util.module_from_spec(spec)
outer_argv=sys.argv
try:
    sys.argv=[str(spec.origin)]
    spec.loader.exec_module(i)
finally:
    sys.argv=outer_argv

def replace_once(text,before,after):
    assert text.count(before)==1
    return text.replace(before,after)

# Introduce only a replacement first-hop plant. The downstream physical model,
# local reads, and installed dispatch expression remain byte-for-byte frozen.
src=inspect.getsource(i.simulate)
src=replace_once(src,'    wire = []','    wire = []\n    ingress = []\n    fifo = []')
src=replace_once(src,'        wire.append((t + 1 + int(jam and src == 0), src, token))',
'''        if src == 0:
            assert not ingress and not fifo
            ingress.append((t+1, token))
        else:
            wire.append((t + 1 + int(jam and src == 0), src, token))''')
src=replace_once(src,'        if t or before:\n            deliver(t)',
'''        for due,tok in ingress[:]:
            if due == t:
                ingress.remove((due,tok))
                assert not fifo
                fifo.append(tok)
                event(t,'bridge_intake',tok)
        if fifo and t >= gate:
            tok = fifo.pop(0)
            wire.append((t+1,0,tok))
            event(t,'bridge_forward',tok)
        if t or before:
            deliver(t)''')
src=replace_once(src,'    return dict(completion=completion,','    assert not ingress and not fifo\n    return dict(completion=completion,')

def bridge_run(base,gate):
    live,d,D=base
    env=dict(i.simulate.__globals__,gate=gate)
    exec(compile(src,'<bridge substituted plant>','exec'),env)
    run=env['simulate'](live,False,d,True,True,D)
    events=[(t,k,tuple(v[-1])) for t,k,*v in run['trace'] if k.startswith('bridge_')]
    assert events==[(0,'bridge_intake',i.TOKEN),(gate,'bridge_forward',i.TOKEN)]
    assert all(not e[1].startswith('bridge_') for es in run['local'].values() for e in es)
    assert [(t,tuple(v[-1])) for t,k,*v in run['trace'] if k=='receive' and v[0]==1]==[(gate+1,i.TOKEN)]
    audit_allocation(run,D)
    return run,tuple(events)

def audit_allocation(run,D):
    stock=[None]*5
    fixed=set()
    pending={}
    starts=[]
    root_accepts=[]
    for t,k,*p in run['trace']:
        if k=='place_on_native_support':
            (j,)=p
            assert stock[j] is None
            stock[j]=j
        elif k=='settled_on_fixed_rack':
            (j,)=p
            assert stock[j]==j and j not in fixed
            fixed.add(j)
            stock[j]=None
        elif k=='begin':
            a,b,j=p
            assert b==a+1 and stock[a]==a==j and stock[b] is None and 0<=t<D
            assert all(a not in g[:2] and b not in g[:2] for g in pending)
            pending[tuple(p)]=t
            if a==0: starts.append(t)
        elif k=='accept':
            a,b,j=p
            assert stock[a]==a==j and stock[b] is None
            time=pending.pop(tuple(p))
            assert t-time in (1,2)
            if a==0:
                assert t==time+1
                root_accepts.append(t)
            stock[a],stock[b]=None,j
        if t>=0:
            assert Counter(j for j in (*stock,*fixed) if j is not None)==Counter(range(4))
    assert not pending and len(starts)==len(root_accepts)<=1
    assert run['served']==any(t<=D for t in root_accepts)
    assert run['completion']==next(iter(root_accepts),None)
    assert stock==run['final']

def bridge_frames(base,gate):
    run,events=bridge_run(base,gate)
    # Replay extraction uses the frozen code object with only the run supplier
    # substituted. Its legacy variant selector merely supplies the preissue
    # assertion and default provenance; provenance is then replaced explicitly.
    extract=types.FunctionType(i.frames.__code__,dict(i.frames.__globals__,simulate=lambda *args:run))
    rows=extract(base,'early-onset')
    actual_issue=tuple(t for t,k,*p in run['trace'] if k=='send' and p[0]==0)
    out=[]
    for c,s,k,start,accept in rows:
        stamp=c[0][-1]
        provenance=('bridge',gate)
        observed_events=tuple(x for x in events if x[0]<=stamp)
        c=(c[0],c[1],(*provenance,actual_issue,observed_events))
        s=(s[0],s[1],provenance)
        k=(k[0],k[1],provenance)
        out.append((c,s,k,start,accept))
    return out,run

def ordinary_frames(base,variant):
    live,d,D=base
    run=i.simulate(live,False,d,False,variant=='ordinary-a',D)
    audit_allocation(run,D)
    extract=types.FunctionType(i.frames.__code__,dict(i.frames.__globals__,simulate=lambda *args:run))
    return extract(base,variant),run

def check(source,target_a,target_b,positive):
    assert len(source)==len(target_a)==len(target_b)
    keyed=[{r[d][0]:r[d] for r in target_a} for d in range(3)]
    S=[tuple(r[d] for r in source) for d in range(3)]
    T=[tuple(dict.fromkeys(r[d] for r in target_a+target_b)) for d in range(3)]
    M=[{x:keyed[d][x[0]] for x in S[d]} for d in range(3)]
    assert all(len(m)==len(source) for m in M)
    assert all(len(m)<len(t) and all(x[0]==y[0] and x[2]!=y[2] for x,y in m.items()) for m,t in zip(M,T))
    # Exact target residual quotient: unary factors distinguish distinct
    # payloads; neighbor key witnesses distinguish any distinct join indices.
    # Conversely equal (key,payload) is a congruence for every frozen factor.
    residual=lambda w:w[:2]
    uncovered={}
    new_source={}
    for d,m in enumerate(M):
        other=0 if d==1 else 1
        assert {x[0] for x in T[d]}=={x[0] for x in T[other]}
        source_res={residual(x) for x in m}
        target_res={residual(x) for x in T[d]}
        image_res={residual(y) for y in m.values()}
        assert image_res==target_res  # C checked independent of T
        assert len(target_res)==len(source)
        uncovered[i.KINDS[d]]=len(target_res-source_res) # profile-identical lift
        new_source[i.KINDS[d]]=len(source_res-target_res)
    ncases={}
    failures={}
    first={}
    undef=0
    for name,scope,test in i.FACTORS:
        ncases[name]=failures[name]=0
        for row in product(*(S[d] for d in scope)):
            val=test(*row)
            mapped=test(*(M[d][w] for d,w in zip(scope,row)))
            undef+= val==i.UNDEF
            ncases[name]+=1
            if val!=mapped:
                failures[name]+=1
                first.setdefault(name,(tuple(w[0] for w in row),val,mapped))
    matched_direct={}
    heldout=[]
    for x,y,z in zip(source,target_a,target_b,strict=True):
        cut=x[0][0]
        assert all(M[d][x[d]]==y[d] and y[d][:2]==z[d][:2] for d in range(3))
        for r in (x,y,z):
            assert i.dispatch(*r[:3])==r[3]
            # Cached baseline uses the decision guard directly on actual
            # receiver read values; no residual classes or raw products.
            assert i.guard_values(*(w[1] for w in r[:3]))==r[3]
        if any(x[d][1]!=y[d][1] for d in range(3)):
            matched_direct.setdefault('first_observation_mismatch',cut)
            matched_direct['observation_mismatches']=matched_direct.get('observation_mismatches',0)+1
        if x[3:]!=y[3:]:
            heldout.append((cut,x[3:],y[3:]))
    assert (not any(failures.values()))==positive
    if positive:
        assert not matched_direct and not heldout
    else:
        assert first['authority'][0][0][-1]==1
    result=dict(source_rows=len(source), target_rows=len(target_a+target_b),
                native_target=tuple(map(len,T)),residual_target=tuple(len({residual(w) for w in td}) for td in T),
                map_counts=tuple(map(len,M)),image_class_counts=tuple(len({residual(w) for w in m.values()}) for m in M),
                no_equal_profile_source_witness=uncovered,new_source_classes=new_source,
                raw_counts=ncases,failures=failures,first_failure=first,
                incompatible=undef,direct=matched_direct,actual_outcome_mismatches=heldout)
    return result, M

def main():
    traces={}
    def replay_family(label,runner):
        out=[]
        records={}
        for base in i.BASES:
            frames,run=runner(base)
            assert {r[0][0] for r in frames}=={(*base,t) for t in range(base[-1]+3)}
            out.extend(frames)
            records[str(base)]=run
        traces[label]=records
        return out
    ordinary_a=replay_family('ordinary-a',lambda b:ordinary_frames(b,'ordinary-a'))
    ordinary_b=replay_family('ordinary-b',lambda b:ordinary_frames(b,'ordinary-b'))
    out={}
    maps={}
    for label,gate,positive in [('bridge',0,True),('rejected_bridge',1,False)]:
        rows=replay_family(label,lambda b:bridge_frames(b,gate))
        out[label],M=check(rows,ordinary_a,ordinary_b,positive)
        out[label]['root_accepts']={v:{key:r['completion'] for key,r in traces[v].items()} for v in (label,'ordinary-a','ordinary-b')}
        out[label]['served_count']={v:sum(r['served'] for r in traces[v].values()) for v in (label,'ordinary-a','ordinary-b')}
        maps[label]={k:list(m.items()) for k,m in zip(i.KINDS,M)}
    assert sys.argv[1:] in ([],['--export'])
    for name,payload in [('traces.json',traces),('maps.json',maps)]:
        expected=(json.dumps(payload,sort_keys=True,indent=1)+'\n').encode()
        path=HERE/name
        if sys.argv[1:]:
            path.write_bytes(expected)
        else:
            assert path.read_bytes()==expected, name
    print(json.dumps(out,sort_keys=True,indent=2))

if __name__=='__main__':
    main()
