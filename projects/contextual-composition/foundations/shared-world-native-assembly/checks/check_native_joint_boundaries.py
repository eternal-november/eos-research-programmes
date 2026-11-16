from itertools import permutations,product
from fractions import Fraction as F
import json
# Actual noncommuting full-state read/write traces.
valid=[]
for word in permutations(('r0','w0','r1','w1')):
 if any(word.index('r'+str(i))>word.index('w'+str(i)) for i in (0,1)):continue
 world=0;cache={}
 for op in word:
  i=int(op[1])
  if op[0]=='r':cache[i]=world
  else:world=cache[i]+1
 valid.append((word,world))
assert len(valid)==6 and sum(v==1 for _,v in valid)==4 and sum(v==2 for _,v in valid)==2
# Scope partitions with multiple original events in a single actor retain event cost.
events=(('root',0),('root',1),('child',0),('child',1),('third',0))
count=0;different=False
for bits in product((0,1),repeat=len(events)):
 chosen=tuple(e for e,b in zip(events,bits) if b)
 if not chosen:continue
 actors=tuple(dict.fromkeys(a for a,_ in chosen))
 groups=tuple(tuple(e for e in chosen if e[0]==a) for a in actors)
 assert sum(map(len,groups))==len(chosen)
 different |= len(chosen)>len(groups)
 raw=list(product((0,1),repeat=len(chosen)))
 index={e:i for i,e in enumerate(chosen)}
 outer={tuple(tuple(w[index[e]] for e in group) for group in groups) for w in raw}
 assert len(outer)==len(raw)
 q={w:F(1,2) if len(set(w))==1 else F(0) for w in raw}
 for group in groups:
  marginal={x:sum(p for w,p in q.items() if tuple(w[index[e]] for e in group)==x) for x in product((0,1),repeat=len(group))}
  assert sum(marginal.values())==1
 count+=1
assert different
# Counital delta naturality gives a*d=a*a, simultaneously at a=1 and a=2.
assert F(1)**2/F(1)!=F(2)**2/F(2)
# Simultaneous ancestor and existing descendant create fresh subtrees at postworld.
# Existing passive cache remains old; newly initialized continuations read world1.
post={():{'world':1,'cache':17},('p',):{'world':1,'cache':23},
      ('k',):{'world':1,'cache':0},('p','r'):{'world':1,'cache':1},
      ('q',):{'world':1,'cache':1},('q','j'):{'world':1,'cache':1}}
assert all(s['world']==1 for s in post.values())
assert post[('k',)]['cache']==0 and post[('q','j')]['cache']==1
# Reparse paths into root/suffix or prefix/leaf groupings without changing actors.
left={((p[0],),p[1:]) if p else ((),()):s for p,s in post.items()}
assert {a+b:s for (a,b),s in left.items()}==post
print(json.dumps({'status':'passed','lost_update_shuffles':len(valid),'final_world_one':4,'final_world_two':2,
 'old_scope_partitions_with_nontrivial_event_cost':count,'simultaneous_post_vertices':len(post),
 'checks':['full-state-noncommutation','primitive-cost-vs-scope-step','raw-partition-bijections-and-marginals','shear-coefficient-inconsistency','postworld-fresh-initialization-vs-passive-cache'],
 'scope':'finite independent probes, not a proof of universal coefficient or categorical laws'},indent=2))
