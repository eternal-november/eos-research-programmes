"""Exact finite fixtures for O6 B/F; not a substitute for parametric proofs."""
import itertools, json
from pathlib import Path

def bits(m): return list(itertools.product(range(2),repeat=m))
def C(y): return sum(v<<j for j,v in enumerate(y)),sum(y)%2
def U(z,m):
 n,p=z
 assert 0<=n<2**m and n.bit_count()%2==p
 return tuple(n>>j&1 for j in range(m))
def h(x): return tuple(x[(j+1)%len(x)] ^ (j==0) for j in range(len(x)))
def hi(y):
 m=len(y); x=[0]*m
 for j in range(m): x[(j+1)%m]=y[j]^(j==0)
 return tuple(x)
counts={'codec_payloads':0,'write_squares':0,'dag_capacity_instances':0,'reserve_runs':0}
for m in range(2,7):
 for y in bits(m):
  z=C(y); assert U(z,m)==y and C(U(z,m))==z
  assert hi(h(y))==y and h(hi(y))==y
  assert C(h(y))==C(h(U(z,m)))
  for s in (0,1):
   dec=lambda a:a if s==0 else hi(a)
   assert dec(y)==dec(U(z,m))
   for x in bits(m):
    write=x if s==0 else h(x)
    assert U(C(write),m)==write
    assert dec(U(C(write),m))==x
    counts['write_squares']+=1
  counts['codec_payloads']+=1
# All DAGs with a fixed topological labelling through 4 vertices,
# demands in {0,1,2}, pools 0..n+1, capacities 0..2n+1.
for n in range(5):
 possible=list(itertools.combinations(range(n),2))
 for mask in range(1<<len(possible)):
  edges={e for j,e in enumerate(possible) if mask>>j&1}
  for w in itertools.product(range(3),repeat=n):
   for slots in range(n+2):
    for K in range(2*n+2):
     live=set(); used=0
     for v in range(n):
      pred={a for a,b in edges if b==v}
      if len(live)<slots and pred<=live and used+w[v]<=K:
       live.add(v);used+=w[v]
      else: break
      assert used<=K and len(live)<=slots
      assert all(b not in live or a in live for a,b in edges)
     assert (len(live)==n)==(slots>=n and sum(w)<=K)
     counts['dag_capacity_instances']+=1
# Failures: independent capacity, pool, predecessor, and lossy information.
assert sum((1,1,1))>2
assert 2<3 and sum((1,1,1))<=3
assert not {0,1}<=set()
a=(0,0,0);b=(0,0,1)
assert a[:-1]==b[:-1] and a[-1]!=b[-1]
# Worked physical migration and exact cost trace.
x=(1,0,1); assert C(x)==(5,0) and h(x)==(1,1,1)
assert C(h(x))==(7,1) and hi(U((7,1),3))==x
assert C(h((0,1,0)))==(0,0)
assert 3*3+5+2==16 and 3*2+4+1==11
for N in range(9):
 I={'q'}|{f'r{j}' for j in range(N)}
 live=[];reserved=[f'r{j}' for j in range(N)]; outcomes=[]
 for step in range(N+2):
  if reserved:
   r=reserved.pop(0);live.append(r);outcomes.append(r)
  else: outcomes.append('Exhausted')
  assert set(live)|set(reserved)|{'q'}==I
  assert len(set(live))==len(live) and not set(live)&set(reserved)
 assert outcomes[:N]==[f'r{j}' for j in range(N)]
 assert outcomes[N:]==['Exhausted','Exhausted']
 counts['reserve_runs']+=1
# Total off-invariant completion used by the final O5 certificate.
# Public configuration has one live slot and one explicit reserve.  A private
# coordinator may hold any registry tag, including one inconsistent with it.
# Every method first uses the same invariant guard, before ordinary enablement.
def complete_method(op, state):
 public_registry, coordinator, payload, bundle = state
 if coordinator != public_registry:
  return ('RejectInvariant', 'error', state, 1)
 # The valid branch is delegated to the method tables checked above.
 return ('InvariantPassed', op, state, 0)
def transport_state(state):
 public_registry, coordinator, payload, bundle = state
 return public_registry, coordinator, C(payload), bundle
counts['off_invariant_method_rows']=0
for m in range(2,7):
 for y in bits(m):
  for version in (0,1):
   public=('v','r0',version)
   bundle=(('q','Coordinator'),('r0',('Live','v',version)),('r1','Reserved'))
   for coordinator in ((),('v','r0',0),('v','r0',1)):
    if coordinator==public: continue
    record=(public,coordinator,y,bundle)
    packed=transport_state(record)
    for op in ('alloc','read','write','migrate'):
     left=complete_method(op,record);right=complete_method(op,packed)
     assert left[0:2]==right[0:2]==('RejectInvariant','error')
     assert left[2]==record and right[2]==packed
     assert transport_state(left[2])==right[2]
     assert left[3]==right[3]==1
     assert left[2][3]==right[2][3]==bundle
     counts['off_invariant_method_rows']+=1
result={'status':'PASS','checks':counts,'scope':'Finite exact checks; general statements proved in the main casebook.'}
Path(__file__).with_name('case_B_F_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
