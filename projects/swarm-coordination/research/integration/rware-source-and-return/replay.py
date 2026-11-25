"""Headless, exact selected native code; one mover, no installed Gym or NetworkX."""
from __future__ import annotations
import ast
from collections import deque
import hashlib
from itertools import product
from pathlib import Path
import json
from enum import Enum
import sys
from types import SimpleNamespace as NS
from typing import Dict,List,Optional,Tuple
import numpy as np

PINS={
 'native_source.py':'9797bf36970d5eb14fef7a150fab7562c450dff6',
 'published_labels.py':'f8735c9e46a8a64981da126b7c1ac48237d6a651'}
def read(p):
 b=p.read_bytes()
 assert hashlib.sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==PINS[p.name]
 return ast.parse(b)
def funcs(tree,names):
 classes=[x for x in tree.body if isinstance(x,ast.ClassDef)]
 code=[]
 for n in names:
  res=[f for c in classes for f in c.body if isinstance(f,ast.FunctionDef) and f.name==n]
  assert len(res)==1,(n,len(res))
  code.append(res[0])
 return code

class Graph:
 def __init__(self): self.s={}
 def add_edge(self,a,b):
  assert a not in self.s
  self.s[a]=b
 def subgraph(self,nodes):
  g=Graph();g.s={a:b for a,b in self.s.items() if a in nodes and b in nodes}
  return g
 def copy(self):return self.subgraph(set(self.s)|set(self.s.values()))
class NoCycle(Exception):pass
def weak(g):
 unseen=set(g.s)|set(g.s.values())
 while unseen:
  nodes={min(unseen)}
  while True:
   new=nodes|{p for a,b in g.s.items() if a in nodes or b in nodes for p in (a,b)}
   if new==nodes:break
   nodes=new
  unseen-=nodes
  yield nodes
def cycle(g):
 # All test calls request at most one FORWARD, so weak components contain
 # at most one moving arc. A stationary self-loop commits that occupant.
 assert sum(a!=b for a,b in g.s.items())<=1
 self_loops=[(a,b) for a,b in g.s.items() if a==b]
 assert len(self_loops)<=1
 if self_loops:return self_loops
 raise NoCycle
def longest(g):
 assert len(g.s)==1
 return list(next(iter(g.s.items())))
nx=NS(DiGraph=Graph,NetworkXNoCycle=NoCycle,weakly_connected_components=weak,
      algorithms=NS(find_cycle=cycle,dag_longest_path=longest))

def load_native(p):
 tree=read(p)
 keys={'Action','Direction','RewardType','Entity','Agent','Shelf'}
 e=[n for n in tree.body if isinstance(n,ast.ClassDef) and n.name in keys]
 defs=funcs(tree,['step','_recalc_grid','_is_highway'])
 g=dict(globals(),_LAYER_AGENTS=0,_LAYER_SHELFS=1)
 exec(compile(ast.Module(body=e+defs,type_ignores=[]),str(p),'exec'),g)
 return NS(**{k:g[k] for k in keys|{x.name for x in defs}})

def load_labels(p):
 tree=read(p)
 defs=funcs(tree,['_protocol_violations',
                  '_agent_carrying_requested','_requested_location','_delivery_lane_cells_for_carrier'])
 g=dict(globals(),_FORWARD=1,RWAREState=NS,RWAREAgentState=NS)
 exec(compile(ast.Module(body=defs,type_ignores=[]),str(p),'exec'),g)
 return type('PublishedLabelPredicates',(),{x.name:g[x.name] for x in defs})

class OneChoice:
 def choice(self,candidates):
  assert len(candidates)==1
  return candidates[0]
def make(n,loaded):
 n.Agent.counter=n.Shelf.counter=0
 orig=n.Shelf(2,1);second=n.Shelf(4,4)
 w=NS(grid_size=(5,5),msg_bits=0,n_agents=2,agents=[n.Agent(2,0,n.Direction.DOWN,0),n.Agent(1,1,n.Direction.RIGHT,0)],
      grid=np.zeros((2,5,5),dtype=int),goals=[(4,1)],highways=np.zeros((5,5),dtype=bool),
      shelfs=[orig,second],request_queue=[orig],reward_type=n.RewardType.TWO_STAGE,
      np_random=OneChoice(),_cur_steps=0,_cur_inactive_steps=0,max_steps=30,max_inactivity_steps=None,
      _make_obs=lambda a:None,_get_info=lambda:{})
 w._recalc_grid=lambda:n._recalc_grid(w)
 w._is_highway=lambda x,y:n._is_highway(w,x,y)
 w.highways[1,4]=True
 if loaded:
  w.agents[0].carrying_shelf=second;second.x,second.y=2,0
 w._recalc_grid()
 return w

def repr_state(w):
 return NS(agents=tuple(NS(x=a.x,y=a.y,direction=a.dir.name,loaded=bool(a.carrying_shelf),
             carrying_shelf=a.carrying_shelf.id if a.carrying_shelf else None,
             has_delivered=a.has_delivered) for a in w.agents),shelves=w.shelfs,
           request_queue=tuple(s.id for s in w.request_queue))

def route(n,w,actor,target,forbid):
 a=w.agents[actor]; other=w.agents[1-actor]
 start=(a.x,a.y,a.dir);q=deque([(start,[])])
 seen={start}; safe=set(forbid)|{(other.x,other.y)}
 if a.carrying_shelf:safe|={(s.x,s.y) for s in w.shelfs if s is not a.carrying_shelf}
 while q:
  state,actions=q.popleft()
  if state[:2]==target:return actions
  x,y,d=state
  v=NS(x=x,y=y,dir=d,req_action=n.Action.FORWARD)
  p=n.Agent.req_location(v,w.grid_size)
  for action in (n.Action.FORWARD,n.Action.LEFT,n.Action.RIGHT):
   if action==n.Action.FORWARD:
    if p in safe:continue
    nxt=(*p,d)
   else:
    v.req_action=action
    nxt=(x,y,n.Agent.req_direction(v))
   if nxt not in seen:
    seen.add(nxt);q.append((nxt,actions+[action]))
 return None

def scenario(n,lab,stop,guard,loaded,second_stop):
 w=make(n,loaded)
 checked=lab();checked.env=w;checked.benchmark='queue_conflict';checked._goal_cells=((4,1),)
 checked._queue_cells={(4,y) for y in range(5)}
 trace=[];credit=0;drop=None;deliver=None;halt=None
 mode='return'
 for tick in range(1,16):
  a=w.agents[0];b=w.agents[1]
  if mode=='return' and tick==stop:
   halt=(a.x,a.y);mode='spare'
  if mode=='return' and (a.x,a.y)==(2,3):mode='spare'
  acts=[n.Action.NOOP]*2
  if mode=='return':
   forbid={(s.x,s.y) for s in w.request_queue} if guard else set()
   planned=route(n,w,0,(2,3),forbid)
   assert planned
   acts[0]=planned[0]
  elif not (second_stop and deliver is not None):
   if b.carrying_shelf is None and not deliver:
    if (b.x,b.y)==(2,1):acts[1]=n.Action.TOGGLE_LOAD
    else:
     planned=route(n,w,1,(2,1),set())
     if planned:acts[1]=planned[0]
   elif b.carrying_shelf and not deliver:
    planned=route(n,w,1,(4,1),set())
    if planned:acts[1]=planned[0]
   elif b.carrying_shelf and deliver:
    if (b.x,b.y)==(4,2):acts[1]=n.Action.TOGGLE_LOAD
    else:
     planned=route(n,w,1,(4,2),set())
     if planned:acts[1]=planned[0]
  assert sum(i!=n.Action.NOOP for i in acts)<=1
  pre=repr_state(w)
  native=n.step(w,[i.value for i in acts])
  post=repr_state(w)
  bad=checked._protocol_violations(pre,post,tuple(i.value for i in acts))
  assert len(set((a.x,a.y) for a in w.agents))==2
  assert not bad[0]
  credit+=float(native[1][1])
  if not deliver and credit==.5:deliver=tick
  if not drop and credit==1:drop=tick
  trace.append((tick,mode,[i.name for i in acts],[[r.x,r.y,r.has_delivered,r.carrying_shelf] for r in post.agents],
                list(post.request_queue),float(native[1][1]),sorted(bad[0])))
 return dict(stop=stop,guard=guard,loaded=loaded,second_stop=second_stop,
            deliver=deliver,drop=drop,physical_halt=halt,trace=trace)

def detector_controls(n,lab):
 w=make(n,False);a,b=w.agents
 a.x,a.y,a.dir=4,2,n.Direction.UP
 b.x,b.y,b.dir=4,3,n.Direction.UP
 shelf=w.shelfs[0];shelf.x,shelf.y=4,3;b.carrying_shelf=shelf;w._recalc_grid()
 c=lab();c.env=w;c.benchmark='queue_conflict';c._goal_cells=((4,1),)
 c._queue_cells={(4,y) for y in range(5)}
 pre=repr_state(w)
 n.step(w,[0,0])
 bad=c._protocol_violations(pre,repr_state(w),(0,0))
 assert bad[0]==frozenset({0})
 n.step(w,[1,0])
 improved=c._protocol_violations(pre,repr_state(w),(1,0))
 assert improved[0]==frozenset() and (a.x,a.y)==(4,1)
 w=make(n,True)
 n.step(w,[1,0])
 assert (w.agents[0].x,w.agents[0].y)==(2,0)
 assert w.agents[0].req_action==n.Action.NOOP
 return {'visible_loaded_queue_conflict_detected':True,'successful_yield_clears_label':True,
         'native_loaded_shelf_entry_refused':True}

def main(src,labfile):
 n=load_native(src);lab=load_labels(labfile)
 rows=[scenario(n,lab,f,g,l,s) for f,g,l,s in product([None,1,2,3,4,5,6],(False,True),(False,True),(False,True))]
 d={(r['stop'],r['guard'],r['loaded'],r['second_stop']):r for r in rows}
 lost=d[2,False,False,False];ok=d[2,True,False,False]
 assert lost['physical_halt']==(2,1) and lost['drop'] is None
 assert ok['physical_halt']!=(2,1) and ok['drop'] is not None
 assert [r['trace'] for r in rows if r['loaded'] and not r['guard']]==[r['trace'] for r in rows if r['loaded'] and r['guard']]
 post=d[2,True,False,True]
 assert post['deliver']==ok['deliver'] and post['drop'] is None
 assert post['trace'][-1][3][1][2:] == [True,1]
 assert post['trace'][-1][4]==[2]
 return dict(rows=rows,detector_controls=detector_controls(n,lab))
if __name__=='__main__':
 p=Path(sys.argv[1]);out=Path(sys.argv[2])
 result=main(p/'native_source.py',p/'published_labels.py');rows=result['rows']
 out.write_text(json.dumps(result,sort_keys=True,separators=(',',':'))+'\n')
 for r in rows:
  if r['stop']==2:print({k:v for k,v in r.items() if k!='trace'})
 print(len(rows),'rows',sum(len(r['trace']) for r in rows),'selected native cycles')
