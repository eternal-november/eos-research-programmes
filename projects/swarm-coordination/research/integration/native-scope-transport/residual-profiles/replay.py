"""Decide the named residual-profile hypotheses against pinned native tables."""
from hashlib import sha1
from itertools import product
import json
from pathlib import Path
import sys
from profiles import audit,assembled_profile

root=Path(__file__).resolve().parent
paths=Path(sys.argv[1]),Path(sys.argv[2])
blobs=[]
for p,row in zip(paths,(root/'SOURCE.tsv').read_text().splitlines(),strict=True):
    b=p.read_bytes()
    assert sha1(f"blob {len(b)}\0".encode()+b).hexdigest()==row.split()[0]
    blobs.append(b)
native=json.loads(blobs[0])
assert native['cases']==64
receiver=(('R','L'),('-','R'))
extra=('-','L')
idle=('-','-')


class Native:
    def __init__(self,plant,times,actions):
        self.plant=plant
        self.witness=tuple(product(times,(False,True)))
        self.actions=actions
        self.observation={}
        self.effects={}
        for t in times:
            by=native['contexts'][f"{plant}:{t!r}"]
            for row in by['source_rows']:
                recorded_p,recorded_t,works,cmd=row['trace']
                cut=(t,works)
                assert (recorded_p,recorded_t)==(plant,t)
                assert row['action']==cmd
                if cut in self.observation:
                    assert self.observation[cut]==row['status']
                self.observation[cut]=row['status']
                action=tuple(cmd)
                assert (cut,action) not in self.effects
                self.effects[cut,action]=tuple(row['paid'])

    def obs(self,w):
        assert w in self.witness
        return self.observation[w]

    def auth(self,w,a):
        assert w in self.witness and a in self.actions
        permitted=a[0]=='-' or self.obs(w)=='LIVE'
        assert permitted==((w,a) in self.effects)
        return permitted

    def payment(self,i,w,a):
        if not self.auth(w,a):
            return None
        return self.effects[w,a][i]


def laws(X,Y):
    both=(0,1)
    return [('old_observation',(0,),X.obs,Y.obs),
            ('issuer_eligible',both,X.auth,Y.auth),
            *((n,both,lambda w,a,i=i:X.payment(i,w,a),
                      lambda w,a,i=i:Y.payment(i,w,a))
              for i,n in enumerate(('paid_old','paid_rescue','paid_independent')))]


def partitions(n):
    def rec(labels):
        if len(labels)==n:
            yield tuple(labels)
        else:
            for x in range(max(labels,default=-1)+2):
                yield from rec([*labels,x])
    yield from rec([])


def partition_reference(X,Y,ms,L,q):
    """Enumerate quotient possibilities without constructing residual sections."""
    offset=[{x:j for j,x in enumerate(d)} for d in Y]
    candidate_count=adequate_count=common_count=0
    for tags in product(*(tuple(partitions(len(d))) for d in Y)):
        candidate_count+=1
        def code(scope,x):
            return tuple(tags[i][offset[i][v]] for i,v in zip(scope,x,strict=True))
        works=True
        for _,scope,_,target in L:
            f={}
            for y in product(*(Y[i] for i in scope)):
                k=code(scope,y)
                out=target(*y)
                if k in f and f[k]!=out:
                    works=False
                    break
                f[k]=out
            if not works: break
        if not works: continue
        adequate_count+=1
        # Every adequate partition refines the candidate residual quotient.
        for i,(d,t) in enumerate(zip(Y,tags,strict=True)):
            assert all(t[x]!=t[y] or q[i][d[x]]==q[i][d[y]]
                       for x,y in product(range(len(t)),repeat=2))
        cover=all(set(t)=={t[offset[i][ms[i][x]]] for x in X[i]}
                  for i,t in enumerate(tags))
        reflected=all(source(*xs)==target(*(ms[i][x] for i,x in zip(scope,xs,strict=True)))
                      for _,scope,source,target in L
                      for xs in product(*(X[i] for i in scope)))
        common_count+=cover and reflected
    return candidate_count,adequate_count,common_count


def replay(name,sy,ta,expected_T,expected_C):
    source=Native('warehouse',(.75,1.),sy)
    target=Native('radio',ta[0],ta[1])
    ms=({(t,works):(ta[0][0],works) for t,works in source.witness},
         {a:a for a in sy})
    X=(source.witness,source.actions)
    Y=(target.witness,target.actions)
    L=laws(source,target)
    q,T,C=audit(X,Y,ms,L)
    assert (not T)==expected_T,(name,T,C)
    assert (not any(C))==expected_C,(name,T,C)
    signature=assembled_profile(q,L)
    count_partition=partition_reference(X,Y,ms,L,q)
    assert bool(count_partition[-1])==(expected_T and expected_C)
    n=0
    for factor,scope,own,other in L:
        for xs in product(*(X[i] for i in scope)):
            before=own(*xs)
            ys=tuple(ms[i][x] for i,x in zip(scope,xs,strict=True))
            after=other(*ys)
            identifiers=tuple(q[i][y] for i,y in zip(scope,ys,strict=True))
            # Every target primitive is recovered exactly. Source only where
            # the premises allow the substitution (count failures separately).
            assert signature[factor][identifiers]==after
            assert (before!=after)==((factor,xs,before,after) in T)
            n+=1
    result=dict(reflects=not T,coverage=not any(C),reflection_failures=T,
                 missing_classes=C,target_residual_class_counts=[len(set(t.values())) for t in q],
                 native_raw_surjective=[set(m.values())==set(d) for m,d in zip(ms,Y,strict=True)],
                 source_factor_calls=n, partition_controls=count_partition)
    if expected_T and expected_C:
        table={'LIVE':('R','L'),'SETTLED':('-','R')}
        # Claim only within frozen policy and exact three present predicates.
        def by_cached_factor(w,act):
            k=(q[0][w],q[1][act])
            return tuple(signature[f][k] for f in ('paid_old','paid_rescue','paid_independent'))
        count=0
        for Z,w,a in [(source,w,a) for w,a in product(*X)] + [(target,w,a) for w,a in product(*Y)]:
            w0,a0=(ms[0][w],ms[1][a]) if Z is source else (w,a)
            obs=Z.obs(w)
            cached=by_cached_factor(w0,a0)
            native_actual=tuple(Z.payment(i,w,a) for i in range(3))
            assert cached==native_actual
            if a==table[obs]:
                assert all(cached)
                count+=1
        assert count==8
        result['verified_frozen_continuation_calls']=count
    return result


settled=(1.0000000000000002,1.25)
results={
 'exact':replay('exact',receiver,(settled,(*receiver,extra)),True,True),
 'early_budget':replay('early_budget',receiver,((.75,1.),receiver),False,True),
 'extra_target_residual':replay('extra_target_residual',receiver,(settled,(*receiver,extra,idle)),True,False),
 'new_source_primitive_scope':replay('new_source_primitive_scope',(*receiver,extra),(settled,(*receiver,extra)),False,True)}
assert results['exact']['target_residual_class_counts']==[2,2]
assert results['exact']['native_raw_surjective']==[False,False]
assert results['extra_target_residual']['target_residual_class_counts']==[2,3]
assert {r[0] for r in results['early_budget']['reflection_failures']}=={'paid_rescue'}
assert {r[0] for r in results['new_source_primitive_scope']['reflection_failures']}=={'paid_rescue'}
print(json.dumps(results,sort_keys=True,indent=2))
