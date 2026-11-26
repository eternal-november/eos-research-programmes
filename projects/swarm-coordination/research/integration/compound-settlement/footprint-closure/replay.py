"""Physical occupancy and actual old service are separate read warrants."""
from itertools import product
from pathlib import Path
import hashlib, importlib.util,json,sys
from core import FootprintCut,may_admit

up=Path(sys.argv[1])
here=Path(__file__).resolve().parent
for ln in (here/'SOURCE.tsv').read_text().splitlines():
    name,repo,rev,path,expected=ln.split('\t')
    b=(up/name).read_bytes()
    assert hashlib.sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==expected

# Reuse exactly the parent scenario assembly rather than transcribing its
# selected native warehouse logic; its core import is not our selector.
# Temporarily install the replay's read-only original interface names.
up=up.resolve()
parent_core=up/'compound_core.py'
saved=sys.modules.pop('core')
spec=importlib.util.spec_from_file_location('core',parent_core)
pc=importlib.util.module_from_spec(spec)
sys.modules['core']=pc
spec.loader.exec_module(pc)
try:
    spec=importlib.util.spec_from_file_location('compound',up/'compound_original.py')
    wmodule=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(wmodule)
finally:
    sys.modules['core']=saved


def one(mode,rule):
    p=wmodule.Warehouse()
    n=p.n
    p.pre(True)
    assert p.pos(2)==(1,1)
    return_paid=False
    sealed=(mode not in ('late','return_rebind'))
    pending=(mode=='pending')
    disjoint=False
    if mode!='occupied':
        assert p.apply(0,0,n.Action.LEFT.value,0)==[0]*4
        assert p.apply(0,0,n.Action.FORWARD.value,0)==[0]*4
        assert p.pos(2)==(1,2)
        disjoint=(mode in ('with_return','return_rebind'))
        if not disjoint:
            assert p.apply(0,0,n.Action.TOGGLE_LOAD.value,0)==[0,0,.5,0]
            return_paid=True
            assert p.w.agents[2].carrying_shelf is None
            assert not p.w.agents[2].has_delivered
        if pending or not sealed:
            for _ in range(2):assert p.apply(0,0,n.Action.RIGHT.value,0)==[0]*4
            assert p.w.agents[2].dir==n.Direction.UP
            if pending:
                a=p.w.agents[2]
                a.req_action=n.Action.FORWARD
                assert a.req_location(p.w.grid_size)==(1,1)
    cut=FootprintCut(sealed,int(pending),return_paid,p.w.grid[0,1,1]==0)
    lawful_vacancy=bool(cut.empty_now and sealed and not pending)
    strong=(lawful_vacancy and (return_paid or disjoint))
    if rule=='strict':
        admitted=may_admit(cut)
    elif rule=='plan_only':
        admitted=cut.empty_now and (return_paid or disjoint)
    elif rule=='scope':
        # Authorize the older return only at its physically disjoint drop
        # position, with no authority to substitute a move into L.
        admitted=strong
    else:
        # Diagnostic control: mistake old delivery for valid retirement.
        assert rule=='credit_only'
        admitted=bool(p.first)
    if pending or not sealed:
        assert p.apply(0,0,n.Action.FORWARD.value,0)==[0]*4
        assert p.pos(2)==(1,1)
    old_on_site_before_wave = p.pos(2)==(1,1)
    old_request=n.Action.TOGGLE_LOAD.value if disjoint and sealed else 0
    rewards=p.apply(int(admitted),0,old_request,1)
    if disjoint and sealed:
        assert p.pos(2)==(1,2) and rewards[2]==.5
    if admitted:
        assert (rewards[0]==.5)==lawful_vacancy
    assert rewards[3]==.5
    return dict(cut={k:(bool(v) if k=='empty_now' else v) for k,v in cut.__dict__.items()},
        advertised_disjoint_return=disjoint,actual_drop_scope_frozen=bool(disjoint and sealed),admit=bool(admitted),rescue=bool(rewards[0]==.5),
        independent=True,old_on_site_before_wave=old_on_site_before_wave,old_return_already_paid=return_paid,
        old_return_paid_during_wave=bool(rewards[2]==.5),oracle_early_allow=bool(strong))

out={}
for case,rule in product(('occupied','with_return','clear','pending','late','return_rebind'),
                         ('strict','scope','credit_only','plan_only')):
    out[case+':'+rule]=one(case,rule)
for mode in ('occupied','pending','late'):
    assert out[mode+':credit_only']['admit'] and not out[mode+':credit_only']['rescue']
    assert not out[mode+':scope']['admit']
assert out['clear:strict']['rescue']
assert out['with_return:scope']['rescue'] and out['with_return:scope']['old_return_paid_during_wave']
assert not out['with_return:strict']['admit']
assert out['return_rebind:plan_only']['admit'] and not out['return_rebind:plan_only']['rescue']
assert not out['return_rebind:plan_only']['old_return_paid_during_wave']
assert not out['return_rebind:scope']['admit']

# A scoped reachability product of the two actual plan-only traces.
# The old re-entry transition is already represented as dormant. Reopening
# the capability adds a path to it; it does not invent a new effect edge.
# This product is authored, not an extractor of all possible RWARE histories.
sys.path.insert(0,str(up))
from reuse import Graph,Edits,Fact,full,update,witnesses,validate_path
protected=out['with_return:plan_only']
unprotected=out['return_rebind:plan_only']
assert protected['cut']['empty_now']==unprotected['cut']['empty_now']==True
assert (protected['advertised_disjoint_return']==unprotected['advertised_disjoint_return']==True
        and protected['admit']==unprotected['admit']==True)
assert protected['rescue'] and protected['old_return_paid_during_wave']
assert unprotected['old_on_site_before_wave'] and not unprotected['rescue']
assert not unprotected['old_return_paid_during_wave']
relations={
    'emitted grant':{'finish together'},
    'finish together':set(),
    'late reassignment enabled':{'old re-enters protected site'},
    'old re-enters protected site':{'missed final service'},
    'missed final service':set(),
}
bad={
    # This is violation of the promised protected footprint, not a claim
    # of a collision; native simulator correctly refuses the second move.
    'old re-enters protected site':frozenset({'safety'}),
    'missed final service':frozenset({'deadline'}),
}
graph=Graph(frozenset({'emitted grant'}),{u:frozenset(v) for u,v in relations.items()},
            {u:Fact(bad.get(u,frozenset())) for u in relations})
old,_=full(graph)
assert all(v is None for v in witnesses(old,('safety','deadline')).values())
deployed,now,work=update(graph,old,Edits(out={
    'emitted grant':frozenset({'finish together','late reassignment enabled'})}))
w=witnesses(now,('safety','deadline'))
direct,_=full(deployed)
assert w==witnesses(direct,('safety','deadline'))
assert all(validate_path(deployed,w[k]) for k in ('safety','deadline'))
assert w['realizability'] is None
out['incremental_authority_extension']=dict(witnesses=w,work=work,
              evaluator='explicit scoped product of native replay branches')
print(json.dumps(out,sort_keys=True,indent=2))
