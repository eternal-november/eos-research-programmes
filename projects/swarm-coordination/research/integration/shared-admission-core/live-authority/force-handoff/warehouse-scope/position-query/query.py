#!/usr/bin/env python3
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import importlib.util
import json
import sys

HERE=Path(__file__).resolve().parent
PARENT=HERE if (HERE/"joined.py").is_file() else HERE.parent
spec=importlib.util.spec_from_file_location("scope",PARENT/"joined.py")
scope=importlib.util.module_from_spec(spec)
sys.modules["scope"]=scope
spec.loader.exec_module(scope)

# One source read per named agent; no free all-robot scan, no assumption about
# radio byte costs. The role and old dispatch proof are already qualified.
STATES=((0,"staged"),(1,"staged"),(0,"bay"),(0,"away"),(1,"away"))
def live(p_bit,q_mode,col,right):
    n=scope.native
    b=(col,0)
    s=(col,1)
    w=scope.iso.make(n,False)
    p,q=w.agents
    p.x,p.y,p.dir=col+1 if right else col-1,0,n.Direction.LEFT if right else n.Direction.RIGHT
    q.x,q.y,q.dir=col,1,n.Direction.UP
    side=n.Agent(1,3,n.Direction.RIGHT,0)
    w.agents.append(side);w.n_agents=3
    w._recalc_grid()
    assert (q.x,q.y)==s and (p.x,p.y)!=b
    wait=n.Action.NOOP.value
    fwd=n.Action.FORWARD.value
    # An actual turn then an orthogonal noninterfering movement takes Q
    # off standby without entering the bay.
    n.step(w,[wait,n.Action.RIGHT.value if q_mode=="away" else wait,wait])
    before=((p.x,p.y)==b,"staged")
    n.step(w,[fwd if p_bit else wait,fwd if q_mode!="staged" else wait,fwd])
    qp=(q.x,q.y)
    assert qp in (b,s,(col+1,1))
    assert (side.x,side.y)==(2,3)
    mode=("bay" if qp==b else ("staged" if qp==s else "away"))
    return before,(int((p.x,p.y)==b),mode)

def truth(table,p,q):
    row=scope.front.world_row(scope.core,table,1,1,q=="staged",p==0 and q!="bay")
    arms={m for m in scope.front.OPTIONS if scope.core.check(row,m,1,scope.front.DUE)}
    return scope.select(arms)

def minimum(weights,answers,queries):
    """Exact Bellman value under unit price for these available questions."""
    if len(set(answers[k] for k in weights))==1:
        return F(0)
    total=sum(weights.values())
    proposals=[]
    for k,query in enumerate(queries):
        classes={}
        for world,mass in weights.items():
            classes.setdefault(query(world),{})[world]=mass
        if len(classes)<2:
            continue
        costs=[]
        for cell in classes.values():
            c=minimum(cell,answers,queries[:k]+queries[k+1:])
            if c is None:
                break
            costs.append(F(sum(cell.values()),total)*c)
        else:
            proposals.append(1+sum(costs))
    return min(proposals,default=None)

def main():
    table=scope.front.native_table()
    predicted={(0,"staged"):"primary_inline",(1,"staged"):"backup",
               (0,"bay"):None,(0,"away"):"primary_inline",(1,"away"):None}
    for col,right in product((1,2,3),(False,True)):
        for p,q in STATES:
            a,b=live(p,q,col,right)
            assert a==(False,"staged") and b==(p,q)
            assert truth(table,*b)==predicted[b]
    p_query=lambda world:world[0]
    q_query=lambda world:world[1]
    q_bit=lambda world:world[1]=="staged"
    count=0
    for weights in product(range(1,5),repeat=5):
        wide=dict(zip(STATES,weights))
        short={s:wide[s] for s in STATES[:3]}
        assert minimum(wide,predicted,(p_query,q_query))==2-F(weights[2],sum(weights))
        assert minimum(short,predicted,(p_query,q_query))==2-F(max(weights[1:3]),sum(weights[:3]))
        assert minimum(wide,predicted,(p_query,q_bit)) is None
        assert minimum(short,predicted,(p_query,q_bit))==minimum(short,predicted,(p_query,q_query))
        count+=1
    # A coherent immutable cut was a premise. Retaining the earlier Q pose
    # while reading only P after the live update cannot distinguish these.
    when_clear,clear=live(0,"staged",2,True)
    when_closed,closed=live(0,"bay",2,True)
    assert (when_clear[1],clear[0])==(when_closed[1],closed[0])
    assert truth(table,*clear)!=truth(table,*closed)
    print(json.dumps(dict(native_route_rows=6*len(STATES),weighted_comparisons=count,
          uniform_initial=str(minimum(dict.fromkeys(STATES[:3],1),predicted,(p_query,q_query))),
          uniform_widened=str(minimum(dict.fromkeys(STATES,1),predicted,(p_query,q_query))),
          widened_standby_bit="insufficient",one_old_one_fresh="insufficient"),sort_keys=True))
if __name__=="__main__":main()
