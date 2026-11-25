"""Civil fixture: live monitor seeding, exact scoped retirement, and prep overlap."""
from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass
from itertools import combinations,product
from functools import lru_cache
from hashlib import sha1
from pathlib import Path
from types import SimpleNamespace as NS
import ast,json,sys,time

WAIT,PREP,USE=range(3)
TARGET=13

@dataclass(frozen=True)
class History:
    fence:int                  # last old issue physically fenced
    issues:int                 # true final watermark
    close:tuple[int,...]       # times at which each successive old effect settled
    fence_report:int|None
    # (delivery tick, sample tick, seal scope, physically settled prefix)
    reads:tuple[tuple[int,int,int,int],...]
    def physical(self,t):
        return t>=self.fence and all(u<=t for u in self.close)
    def observe(self,t):
        return ((self.fence,self.issues) if self.fence_report==t else None,
                tuple((q,scope,c) for d,q,scope,c in self.reads if d==t))

def validate(h):
    assert len(h.close)==h.issues
    assert tuple(sorted(h.close))==h.close
    assert h.fence_report is None or h.fence_report>=h.fence
    for d,q,scope,c in h.reads:
        assert q<=d
        if scope==TARGET: assert c<=sum(x<=q for x in h.close)
def all_visible(h,t):return tuple(h.observe(u) for u in range(t+1))
def cert(transcript,fresh):
    anchor=next(((f,n,t) for t,(a,_) in enumerate(transcript) if a is not None for f,n in [a]),None)
    if anchor is None:return False
    _,n,received=anchor
    return any(scope==TARGET and c>=n and (not fresh or q>=received)
              for _,data in transcript for q,scope,c in data)

def direct(hs,p,d,rule):
    """Decision-tree recursion; environment picks one immutable history."""
    @lru_cache(None)
    def win(t,ids,prep):
        if t>=d:return False
        h=hs[ids[0]]
        recognized=None
        evidence=[]
        for tick in range(t+1):
            issue,reads=h.observe(tick)
            if issue is not None:
                _physical_cut,last=issue
                recognized=(tick,last)
            evidence.extend(reads)
        ok=False
        if recognized is not None:
            r,last=recognized
            covered={i for q,b,c in evidence if b==TARGET and (rule!='fresh' or q>=r)
                       for i in range(1,c+1)}
            # Demand an eligible certificate even for last==0; no empty
            # unseen transcript is a physical clearance measurement.
            ok=set(range(1,last+1))<=covered and any(
                b==TARGET and (rule!='fresh' or q>=r) for q,b,_ in evidence)
        if ok and prep==p:
            assert all(hs[j].physical(t) for j in ids)
            return True
        opts=[prep]
        if prep<p and (rule!='serial' or ok):opts.append(prep+1)
        child=defaultdict(list)
        for j in ids:child[hs[j].observe(t+1)].append(j)
        return any(all(win(t+1,tuple(cell),q) for cell in child.values()) for q in opts)
    group=defaultdict(list)
    for i,h in enumerate(hs):group[h.observe(0)].append(i)
    return all(win(0,tuple(k),0) for k in group.values())

@dataclass(frozen=True)
class State:
    env_state:tuple
    obligation_states:tuple=(0,0)
GOOD=State(('settled',))
BAD=State(('deadline_or_interlock',),(1,0))

def product_graph(hs,p,d,rule):
    starts=defaultdict(list)
    for i,h in enumerate(hs):starts[h.observe(0)].append(i)
    roots=tuple(State((0,tuple(k),0)) for k in starts.values())
    graph={GOOD:{(0,0):frozenset({GOOD})},BAD:{(0,0):frozenset({BAD})}}
    def add(node):
        if node in graph:return
        t,ids,k=node.env_state
        scope_ok=cert(all_visible(hs[ids[0]],t),rule=='fresh')
        obs=defaultdict(list)
        for i in ids:obs[hs[i].observe(t+1)].append(i)
        moves={}
        for a in (WAIT,PREP,USE):
            if a==USE:
                s=[GOOD] if k==p and scope_ok and all(hs[i].physical(t) for i in ids) else [BAD]
            elif t+1==d or (a==PREP and (k==p or rule=='serial' and not scope_ok)):
                s=[BAD]
            else:s=[State((t+1,tuple(js),k+(a==PREP))) for js in obs.values()]
            moves[0,a]=frozenset(s)
            for s0 in s:add(s0)
        graph[node]=moves
    for node in roots:add(node)
    return roots,graph

def load(p):
    b=p.read_bytes()
    assert sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()=='ee1ce2942bbea54c3d31ebfe48f25c0ce5960983'
    tree=ast.parse(b)
    keep={'_compute_assume_guarantee_fixed_point','_maximal_assume_guarantee_action_rectangle',
          '_nonempty_action_subsets','_sorted_action_rectangles','_action_rectangle_score'}
    body=[x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name in keep]
    assert len(body)==len(keep)
    ctx=dict(globals(),_contract_progress_interval_states=lambda:0,_ACTION_RECTANGLE_CACHE={})
    exec(compile(ast.Module(body=body,type_ignores=[]),str(p),'exec'),ctx)
    return ctx['_compute_assume_guarantee_fixed_point']

def compare(fn,hs,p,d,rule):
    roots,graph=product_graph(hs,p,d,rule)
    model=NS(agent_ids=('old','new'),local_actions=lambda a,s:(0,) if a=='old' else (0,1,2))
    automata={a:NS(safe_states=frozenset({0})) for a in model.agent_ids}
    win,_=fn(model,automata,graph)
    a=all(root in win for root in roots);b=direct(hs,p,d,rule)
    assert a==b,(hs,p,d,rule,a,b)
    return a

def one(h,p,rule):
    full=[t for t in range(17) if cert(all_visible(h,t),rule=='fresh')]
    if not full:return None
    ready=full[0]
    return (ready+p if rule=='serial' else max(p,ready))+1
def witness_vals(h,n):
    return {rule:one(h,n,rule) for rule in ('join','serial','fresh')}

def verify(fn):
    checks=0;query_batches=[]
    for f,read,p in product(range(1,4),range(1,5),range(3)):
        h=History(f,1,(1,),f,((read,1,TARGET,1),(f+2,f+2,TARGET,1)))
        validate(h)
        for d in range(1,9):
            for rule in ('join','serial','fresh'):
                res=compare(fn,(h,),p,d,rule)
                t=one(h,p,rule)
                assert res==(t is not None and t<=d)
                checks+=1
    # Same early old effect, two possible future old scopes. In the second
    # history old work issues one more serial before the actual fence.
    already=History(3,1,(1,),3,((1,1,TARGET,1),(5,5,TARGET,1)))
    late=History(3,2,(1,5),3,((1,1,TARGET,1),(6,5,TARGET,2)))
    stale=History(3,1,(5,),3,((1,1,12,1),(6,5,TARGET,1)))
    masked=History(3,1,(1,),None,((1,1,TARGET,1),(5,5,TARGET,1)))
    for h in (already,late,stale,masked):validate(h)
    examples=[witness_vals(h,2) for h in (already,late,stale,masked)]
    assert examples==[{'join':4,'serial':6,'fresh':6},{'join':7,'serial':9,'fresh':7},
                      {'join':7,'serial':9,'fresh':7},{'join':None,'serial':None,'fresh':None}]
    for xs in ((already,late),(already,stale),(already,masked),(already,late,stale)):
        for p,d,rule in product(range(4),range(1,12),('join','serial','fresh')):
            assert compare(fn,xs,p,d,rule)==all(
                   one(h,p,rule) is not None and one(h,p,rule)<=d for h in xs)
            checks+=1
    assert cert(all_visible(already,3),False) and not cert(all_visible(late,3),False)
    assert not cert(all_visible(stale,3),False)
    return dict(queries=checks,prepared_ticks=2,case_order=['early_drain','late_old_effect','wrong_scope','fence_erased'],
                earliest_exclusive_effect_tick=examples)
if __name__=='__main__':
 verdict=verify(load(Path(sys.argv[1])))
 data=json.dumps(verdict,indent=2,sort_keys=True)+'\n'
 if len(sys.argv)>2:Path(sys.argv[2]).write_text(data)
 else:print(data,end='')
