"""Independent finite checks: no imports of author's solver/model/checker."""
from functools import lru_cache
from itertools import product, combinations
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parents[1]
W=[(None,None),(None,0),(1,None)]
controls=[(0,0),(1,0),(0,1),(2,0),(0,2)]
def terminal(s):
 t,e,prev,done,k=s
 if t>=4 and done!=3:return False
 if done==3 and prev==(0,0):return True
 if t>=5:return False
 return None
def actions(s,start):
 return [a for a in controls if sum(a)<=s[1] and (s[0]>=start or a==(0,0))]
def step(s,a):
 t,e,prev,done,k=s; out={}; bad=[]
 for w,p in enumerate(W):
  if not (k>>w)&1:continue
  obs=tuple(a[i]+(0 if p[i] is None else prev[p[i]]) for i in range(2))
  if max(obs)>3:bad.append((w,obs))
  out[obs]=out.get(obs,0)|(1<<w)
 if bad:return bad,{}
 if t in (2,3):
  for i in range(2):
   if a[i]==2:done|=1<<i
 return [],{o:(t+1,e-sum(a),a,done,ks) for o,ks in out.items()}
def solve(start,energy):
 @lru_cache(None)
 def f(s):
  z=terminal(s)
  if z is not None:return z
  for a in actions(s,start):
   bad,out=step(s,a)
   if not bad and all(f(v) for v in out.values()):return True
  return False
 return f((0,energy,(0,0),0,7)),f.cache_info().currsize

def encode(s):return [s[0],s[1],list(s[2]),s[3],s[4]]
def nid(s):return hashlib.sha256(json.dumps(encode(s),sort_keys=True,separators=(',',':')).encode()).hexdigest()
def check_saved(r,start):
 cert=r['certificate'];seen=set()
 def visit(s,want):
  n=nid(s);c=cert[n];assert c['state']==encode(s) and c['status']==want
  if n in seen:return
  seen.add(n); term=terminal(s)
  if term is not None:
   assert c['kind']=='terminal' and (want=='WIN')==term;return
  aa=actions(s,start)
  if want=='WIN':
   assert c['kind']=='choice';a=tuple(c['action']);assert a in aa
   bad,outs=step(s,a);assert not bad
   edges={tuple(x['observation']):x for x in c['outcomes']}
   assert len(edges)==len(c['outcomes']) and set(edges)==set(outs)
   for obs,sn in outs.items():
    assert edges[obs]['next']==nid(sn);visit(sn,want)
  else:
   assert c['kind']=='refutation'
   cover={tuple(x['action']):x for x in c['actions']}
   assert len(cover)==len(c['actions']) and set(cover)==set(aa)
   for a,e in cover.items():
    bad,outs=step(s,a)
    if 'unsafe' in e:
     assert (e['unsafe']['world'],tuple(e['unsafe']['load'])) in bad
    else:
     assert not bad;sn=outs[tuple(e['observation'])]
     assert e['next']==nid(sn);visit(sn,want)
 visit((0,5,(0,0),0,7),r['status']);assert set(cert)==seen
 return len(seen)
results={'gate_truth':{},'certificate_nodes':{}}
for start in range(3):
 for energy in range(4,8):
  v,n=solve(start,energy);results['gate_truth'][f'start{start}_E{energy}']={'win':v,'states':n}
assert solve(0,5)[0] and not solve(0,4)[0]
assert not solve(1,5)[0] and not solve(2,5)[0]
r=json.loads((ROOT/'example/strict_pair_gate_results.json').read_text())
for name,start in [('early_acquisition',0),('late_acquisition',1),('no_prerelease_acquisition',2)]:
 assert (r[name]['status']=='WIN')==solve(start,5)[0]
 results['certificate_nodes'][name]=check_saved(r[name],start)
# Exhaustive direct conditional-functional-dependence test and restriction reuse.
worlds=list(product(range(2),repeat=3)); subsets=[tuple(worlds[i] for i in range(8) if mask>>i&1) for mask in range(1,256)]
func=lambda w:(w[0]^w[1],w[1]&w[2])
checks=0;reuse=0;obstructions=0
for K in subsets:
 for D in [(),(0,),(1,),(2,),(0,1),(0,2),(1,2),(0,1,2)]:
  fibers={};valid=True
  for w in K:
   d=tuple(w[i] for i in D)
   if d in fibers and fibers[d]!=func(w):valid=False
   fibers[d]=func(w)
  pairtest=all(tuple(a[i] for i in D)!=tuple(b[i] for i in D) or func(a)==func(b) for a in K for b in K)
  assert valid==pairtest;checks+=1
  if valid:
   for mask in range(1,1<<len(K)):
    kp=[K[i] for i in range(len(K)) if mask>>i&1]
    assert all(fibers[tuple(w[i] for i in D)]==func(w) for w in kp);reuse+=1
  else:obstructions+=1
results['crs']={'equivalence_checks':checks,'monotone_reuse_checks':reuse,'rejected_supports':obstructions}
# Distinguish current losing from initial infeasibility: spending two units cannot
# make an initially feasible world's negative initial-feasibility claim true.
assert solve(0,5)[0] and not solve(2,5)[0]
results['status']='PASS'
(ROOT/'review/independent_theory_checks.json').write_text(json.dumps(results,indent=2,sort_keys=True)+'\n')
print(json.dumps(results,indent=2))
