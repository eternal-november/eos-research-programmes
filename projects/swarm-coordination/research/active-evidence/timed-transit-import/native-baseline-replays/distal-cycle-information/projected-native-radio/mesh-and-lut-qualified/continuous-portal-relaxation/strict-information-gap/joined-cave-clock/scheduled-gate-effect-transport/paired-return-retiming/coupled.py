"""Consumer-limited joint support for retimed return and closure."""
from pathlib import Path
from itertools import product
import json,sys
up=Path(sys.argv[1])
Z=10**6
bound=json.loads((up/'BOUND.jsonl').read_text().splitlines()[1])
T=bound['3/6/checked']['max_egress_us']
assert T+Z<455*Z<456498169
def plus(t,v):return t[0]+v,t[1]+v
def overlap(a,b):return max(a[0],b[0])<=min(a[1],b[1])
def sweep(route,close):
    seen=set()
    for when,tag,kind in sorted([(p,i,1) for i,(p,q) in enumerate((route,close))]+
                                [(q+1,i,-1) for i,(p,q) in enumerate((route,close))]):
        if kind>0:seen.add(tag)
        else:seen.remove(tag)
        if len(seen)==2:return True
    return False

def replay(row):
    outer,inner=map(tuple,row['hulls']),map(tuple,row['cores'])
    out,ret=outer
    _,inside=inner
    retimed=[ret,plus(ret,Z)]
    assert retimed[0][1]<retimed[1][0]
    effects=[inside,plus(inside,Z)]
    probe=(retimed[0][1]+1,retimed[0][1]+150000)
    assert probe[1]<retimed[1][0]
    assert all(not overlap(out,e) and all(overlap(r,e)==sweep(r,e) for r in retimed) for e in [*effects,probe])
    assert all(e0<=e1 for e0,e1 in effects)
    k=retimed[1][0]-retimed[0][1]-1
    # Causally generated couplings: earlier phase sets both the detour
    # switch and maintenance command; no effect depends on future data.
    raw={(u,v) for u,v in product((0,1),repeat=2)}
    supports={name:{(u,u^bit) for u in (0,1)} for name,bit in (("covariant",0),("contravariant",1))}
    supports["independent"]=raw
    for tape in supports.values():
        assert {u for u,v in tape}=={v for u,v in tape}=={0,1}
    good={}
    no_overlap_context={}
    for name,w in supports.items():
        cols=[(u,v,not overlap(retimed[u],effects[v])) for u,v in sorted(w)]
        assert all(ok==(u!=v) for u,v,ok in cols)
        good[name]=sum(ok for u,v,ok in cols)
        no_overlap_context[name]=all(ok for u,v,ok in cols)
    assert good==dict(covariant=0,contravariant=2,independent=2)
    assert no_overlap_context==dict(covariant=False,contravariant=True,independent=False)
    # A support abstraction under the declared joint consumer is given
    # by intersection with the forbidden diagonal. A stronger client that
    # may query either retiming separately can distinguish the diagonal bits.
    residual_classes=set()
    for m in range(1,16):
        S={w for x,w in enumerate(sorted(raw)) if m&(1<<x)}
        ref=tuple((i,i) in S for i in (0,1))
        legal=tuple(not any(u==i and u==v for u,v in S) for i in (0,1))
        assert tuple(not x for x in ref)==legal
        residual_classes.add(legal)
    assert len(residual_classes)==4
    return dict(gate=row['gate'],protected_gap_us=k, matched_absolute_closure_pairs=good,
                permits_universal_joint_service=no_overlap_context, extra_safe_short_slot=list(probe),
                egress_upper_us=T+Z, staged_latest_us=455*Z)
for line in (up/'PORTAL.jsonl').read_text().splitlines():
    print(json.dumps(replay(json.loads(line)),sort_keys=True))
