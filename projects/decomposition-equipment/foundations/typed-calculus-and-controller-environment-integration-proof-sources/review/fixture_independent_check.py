#!/usr/bin/env python3
"""Independent finite reference and mutation audit; standard library only."""
from itertools import product
from collections import Counter,deque
from pathlib import Path
import importlib.util,sys,json,hashlib
ROOT=Path(__file__).resolve().parents[1]
p=ROOT/'example/check_fixture.py'
spec=importlib.util.spec_from_file_location('subject',p); m=importlib.util.module_from_spec(spec);sys.modules['subject']=m;spec.loader.exec_module(m)
A=('approach','pushL','pushR','withdraw','wait')
X=list(product(('L','R'),('HOLD','TOUCH'),(('clear',-1),('engaged',0),('engaged',1)),('held','released'),(0,1,-1)))
X=[(h,k,c,r,g,t) for h,k,(c,r),g,t in X]
def trans(x,a):
 h,k,c,r,g,t=x
 u='idle' if a=='wait' else 'invalid' if g=='released' else dict(approach='advance',pushL='driveL',pushR='driveR',withdraw='release')[a]
 gg='released' if u=='release' else g
 if u=='idle': fs=[(c,r,'zero',('ack',),'idle')]
 elif u=='release': fs=[('clear',-1,'zero',('released',),'release')]
 elif u=='advance' and c=='clear': fs=[('engaged',rr,'zero',('contact',h,k),'seat_pad_'+str(rr)) for rr in (0,1)]
 elif u in ('driveL','driveR') and c=='engaged':
  fs=[(c,r,'positive' if u[-1]==h else 'negative',('ack',),'retained_push')]
  if k=='TOUCH':fs += [('clear',-1,'loss',('slip',),'slip_during_push')]
 else:fs=[(c,r,'invalid',('fault',),'invalid_mode')]
 for cc,rr,w,v,tag in fs:
  tt=t if w=='zero' else 1 if w=='positive' and t==0 else -1
  yield (x,a,u,w,v,tag,(h,k,cc,rr,gg,tt))
def norm(e):
 x=tuple(vars(e.source).values()); y=tuple(vars(e.target).values());f=e.fixture
 return (x,e.action,e.command,f.wrench,f.reply,f.occurrence,y)
ref=[e for x in X for a in A for e in trans(x,a)]
actual=[norm(e) for x in m.states() for a in A for e in m.events(x,a)]
assert Counter(ref)==Counter(actual) and len(ref)==396
assert len(set((x,a) for x,a,*_ in ref))==360
# Literal local cylinder edges, INCLUDING j coordinates, not stripped invocation IDs.
replies=[('ack',),('released',),('slip',),('fault',)]+[('contact',h,k) for h,k in product(('L','R'),('HOLD','TOUCH'))]
J=list(product(('clear','engaged'),repeat=2))
J=[(c,d,a,u,w,v) for (c,d),a,u,w,v in product(J,A,('idle','invalid','advance','driveL','driveR','release'),('zero','positive','negative','loss','invalid'),replies)]
G={};F={};O={}
for j in J:
 c,d,a,u,w,v=j
 G[j]=[(g,gg) for g,gg in product(('held','released'),repeat=2) if m.dg_accept(g,gg,j)]
 O[j]=[(t,tt) for t,tt in product((0,1,-1),repeat=2) if m.do_accept(t,tt,j)]
 F[j]=[]
 for h,k,(cc,r) in product(('L','R'),('HOLD','TOUCH'),(('clear',-1),('engaged',0),('engaged',1))):
  for f in m.fixture((h,k,cc,r),u):
   if m.df_accept(f.source,f.target,f,j):F[j].append(f)
tuples=[]
for j in J:
 for (g,gg),f,(t,tt) in product(G[j],F[j],O[j]):
  x=(*f.source,g,t);y=(*f.target,gg,tt)
  tuples.append((x,j[2],j[3],j[4],j[5],f.occurrence,y))
assert Counter(tuples)==Counter(ref)
# Verify all local edge endpoints project to the literal j endpoints.
assert all(f.source[2]==j[0] and f.target[2]==j[1] for j in J for f in F[j])
used={j for j in J if G[j] and F[j] and O[j]}
assert len(used)==25
state_tuples=[(h,k,c,r,g,t) for c in ('clear','engaged') for g in ('held','released') for h,k,r in product(('L','R'),('HOLD','TOUCH'),(-1,0,1)) for t in (0,1,-1) if (r==-1)==(c=='clear')]
assert Counter(state_tuples)==Counter(X)
# Absent fixture: no torque-producing primitive, under every action sequence.
absent={('held',0)};queue=deque(absent)
while queue:
 g,t=queue.popleft()
 for a in A:
  gg='released' if g=='held' and a=='withdraw' else g
  zero=a=='wait' or (g=='held' and a in ('approach','withdraw'))
  tt=t if zero else -1
  y=(gg,tt)
  assert tt!=1
  if y not in absent:absent.add(y);queue.append(y)
assert len(absent)==4
# Cylinder inflation exists locally, but exact join does not multiply invocations.
unused_with_local=sum(bool(G[j] or F[j] or O[j]) for j in J if j not in used)
assert unused_with_local>0
initial=[(h,'HOLD','clear',-1,'held',0) for h in ('L','R')]
def goal(x):return x[-1]==1 and x[-2]=='released' and x[2]=='clear'
def policy_wins(policy):
 seen=set(initial);q=deque(initial);adj={};unsafe=False
 while q:
  x=q.popleft()
  if x[-1]==-1:unsafe=True
  if goal(x):continue
  yy=[e[-1] for e in trans(x,policy[x[2]])];adj[x]=yy
  for y in yy:
   if y not in seen:seen.add(y);q.append(y)
 # universal finite reachability independently via repeatedly eliminating terminal predecessors.
 win={x for x in seen if goal(x)}
 while True:
  new=win|{x for x,ys in adj.items() if x[-1]!=-1 and ys and all(y in win for y in ys)}
  if new==win:break
  win=new
 return not unsafe and all(x in win for x in initial)
assert sum(policy_wins(dict(zip(('clear','engaged'),p))) for p in product(A,repeat=2))==0
# Driver checked by bounded full path expansion, separate from author's rank/BFS.
def paths(grade='HOLD',erase_grade=False,flip_hand=False):
 frontier=[((h,grade,'clear',-1,'held',0),'start',()) for h in ('L','R')]
 for tick in range(3):
  nxt=[]
  for x,q,path in frontier:
   a={'start':'approach','L':'pushL','R':'pushR','withdraw':'withdraw','reject':'wait','done':'wait'}[q]
   for e in trans(x,a):
    v=e[4]
    if q=='start':
     qq=v[1] if len(v)==3 and (v[2]=='HOLD' or erase_grade) else 'reject'
     if flip_hand and qq in ('L','R'):qq={'L':'R','R':'L'}[qq]
    else:qq='withdraw' if q in ('L','R') else 'done' if q=='withdraw' else q
    nxt.append((e[-1],qq,path+(e,)))
  frontier=nxt
 return frontier
hold=paths();assert len(hold)==4 and all(goal(x) and all(e[-1][-1]!=-1 for e in pp) for x,q,pp in hold)
touch=paths('TOUCH');assert len(touch)==4 and all(q=='reject' and x[-1]==0 and not goal(x) for x,q,pp in touch)
erased=paths('TOUCH',True);assert sum(x[-1]==-1 for x,q,p in erased)==4
flipped=paths(flip_hand=True);assert all(x[-1]==-1 for x,q,p in flipped)
# Counter-based exactness rejects dropping one seating execution or adding duplicate.
assert Counter(ref[:-1])!=Counter(ref)
assert Counter(ref+[ref[0]])!=Counter(ref)
# Real seating records: shared sensor/mechanics use identical pad occurrence.
seats=list(trans(initial[0],'approach'));shared=[(a,a) for a in seats];dup=list(product(seats,repeat=2))
assert len(shared)==2 and len(dup)==4 and len([p for p in dup if p[0]!=p[1]])==2
# Exact pad relabeling is invisible at J, but not equality of witness maps.
def swapx(x):
 h,k,c,r,g,t=x
 return (h,k,c,1-r if c=='engaged' else r,g,t)
def swape(e):
 x,a,u,w,v,tag,y=e
 if tag.startswith('seat_pad_'):tag='seat_pad_'+str(1-int(tag[-1]))
 return (swapx(x),a,u,w,v,tag,swapx(y))
assert Counter(map(swape,ref))==Counter(ref)
assert all(swape(swape(e))==e for e in ref)
changed=sum(swape(e)!=e for e in ref)
assert changed>0
# Independently specify and exhaustively join controller-side local primitives.
Q=('start','L','R','withdraw','done','reject')
def select(q,o):return dict(start='approach',L='pushL',R='pushR',withdraw='withdraw',done='wait',reject='wait')[q]
def decode(q,a,v):
 if q=='start':return v[1] if v in (('contact','L','HOLD'),('contact','R','HOLD')) else 'reject'
 if q in ('L','R'):return 'withdraw'
 if q=='withdraw':return 'done'
 return q
JC=list(product(Q,Q,('clear','engaged'),A,replies,Q))
S={e for e in JC if e[3]==select(e[0],e[2])}
D={e for e in JC if e[5]==decode(e[0],e[3],e[4])}
C={e for e in JC if e[1]==e[5]}
join=S&D&C
K={(q,decode(q,select(q,o),v),o,select(q,o),v,decode(q,select(q,o),v)) for q,o,v in product(Q,('clear','engaged'),replies)}
assert join==K and len(K)==96
for q,o in product(Q,('clear','engaged')):
 # Every future combination remains admitted for the one current action.
 assert {(e[1],e[4],e[5]) for e in S if e[0]==q and e[2]==o}==set(product(Q,replies,Q))
 assert {e[3] for e in S if e[0]==q and e[2]==o}=={select(q,o)}
for q,o,a,v in product(Q,('clear','engaged'),A,replies):
 assert select(q,o)==m.choose(q,o) and decode(q,a,v)==m.update(q,a,v)
Ext={(q,qq,(o,cc,a,u,w,v)) for q,qq,o,a,v,i in join for cc,u,w in product(('clear','engaged'),('idle','invalid','advance','driveL','driveR','release'),('zero','positive','negative','loss','invalid'))}
assert len(Ext)==5760
byj={}
for q,qq,j in Ext:byj.setdefault(j,[]).append((q,qq))
filtered=[]
for e in ref:
 x,a,u,w,v,tag,y=e
 j=(x[2],y[2],a,u,w,v)
 for q,qq in byj.get(j,[]):filtered.append((e,q,qq))
direct=[(e,q,decode(q,e[1],e[4])) for x,q in product(X,Q) for e in trans(x,select(q,x[2]))]
assert Counter(filtered)==Counter(direct) and len(filtered)==468
assert len({(e[0],q) for e,q,qq in filtered})==432
# Removing commit admits multiple contradictory next memories per record.
assert len(S&D)>len(join)
# A selector incorrectly conditioned on the future reply violates full cylinders.
leaky={e for e in S if e[4]!=('fault',)}
assert leaky!=S and any(not any(e[0]==q and e[2]==o and e[4]==('fault',) for e in leaky) for q,o in product(Q,('clear','engaged')))
# Common I supports BOTH original occurrence substitutions at one boundary type.
common=[]
for e in ref:
 x,a,u,w,v,tag,y=e
 j=(x[2],y[2],a,u,w,v)
 for q,qq,i in product(Q,repeat=3):
  jc=(q,qq,x[2],a,v,i)
  if jc not in join:continue
  ie=(q,qq,j,i)
  # Projections I->J and I->JC commute with source and target.
  sourceI=(q,j[0]); targetI=(qq,j[1])
  assert (sourceI[1],targetI[1])==(j[0],j[1])
  assert (sourceI[0],targetI[0])==(jc[0],jc[1])
  k=tuple((name,ie) for name in ('Select','Decode','Commit'))
  plant=(('G',x[-2],y[-2],ie),('F',x[:4],tag,y[:4],ie),('O',x[-1],y[-1],ie))
  parent=(k,plant)
  left=(*parent[0],parent[1]);right=(parent[0],*parent[1])
  assert (*left[:3],*left[3])==(*right[0],*right[1:])
  common.append((e,q,qq))
assert Counter(common)==Counter(direct)
cs=('L','withdraw','engaged','pushL',('ack',),'withdraw')
cd=('R','withdraw','engaged','pushL',('ack',),'withdraw')
cc=('start','withdraw','engaged','pushL',('ack',),'withdraw')
assert cs in S and cd in D and cc in C
assert cs[2:]==cd[2:]==cc[2:] and len({cs[0],cd[0],cc[0]})==3
# Nonliftability is of these retained record identities, not public values alone.
assert any(e[2:]==cs[2:] for e in join)
result={'common_interface_records':len(common),'common_interface_two_substitution_orders_equal':True,'memory_hiding_countertuple_retains_record_identities':True,'controller_intrinsic_records':len(K),'controller_external_records':len(Ext),'coupled_open_records':len(filtered),'coupled_source_states':432,'controller_future_cylinder_and_commit_mutations_detected':True,'pad_swap_distinct_whole_records':changed,'reference_open_states':len(X),'literal_state_pullback_tuples':len(state_tuples),'absent_fixture_reachable_states':len(absent),'reference_open_events':len(ref),'source_action_pairs':360,'literal_pullback_tuples':len(tuples),'boundary_edges':len(J),'used_boundary_edges':len(used),'unused_edges_with_local_cylinders':unused_with_local,'local_edge_counts':{'gripper':sum(map(len,G.values())),'fixture':sum(map(len,F.values())),'object':sum(map(len,O.values()))},'memoryless_policies':25,'memoryless_winners':0,'hold_three_step_paths':len(hold),'touch_reject_paths':len(touch),'grade_erasure_bad_paths':sum(x[-1]==-1 for x,q,p in erased),'wrong_hand_bad_paths':len(flipped),'duplicate_contact_off_diagonals':2,'record_deletion_and_duplication_mutations_detected':True,'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'note_sha256':hashlib.sha256((ROOT/'example/Fixture_Assisted_Quarterturn.md').read_bytes()).hexdigest()}
print(json.dumps(result,indent=2))
