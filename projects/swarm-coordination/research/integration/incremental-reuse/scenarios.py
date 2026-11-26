"""Authored after the implementation freeze; not blindly or independently selected."""
from reuse import Fact,Observation,Graph,Edits

def g(out, roots=('start',), facts=None):
    facts=facts or {}
    vertices=set(out)|{x for r in out.values() for x in r}|set(roots)|set(facts)
    return Graph(frozenset(roots),{x:frozenset(out.get(x,())) for x in vertices},
                 {x:facts.get(x,Fact()) for x in vertices})

same_read=lambda action:Observation('coordinator','takeover-cut','old inbox shows accepted',action)
a=g({
    'start':{'reserved'},'reserved':{'done'},
    'budget-drained':{'old-issued-enters-C'},
    'old-issued-enters-C':{'done'},'new-disjoint-diagnostic':{'done'},
    'still-safe-at-deadline':{'done'},'needs-right-quiet-route':{'done'}
}, facts={
    'old-issued-enters-C':Fact(frozenset({'safety'})),
    'still-safe-at-deadline':Fact(frozenset({'deadline'})),
    'needs-right-quiet-route':Fact(obs=same_read('R')),
    'reserved':Fact(obs=same_read('L'))
})

new_behavior=Edits(out={'reserved':frozenset({'done','new-disjoint-diagnostic'})})
expose_old=Edits(out={'reserved':frozenset({'done','budget-drained'})})
deadline_only=Edits(out={'reserved':frozenset({'done','still-safe-at-deadline'})})
information_only=Edits(out={'reserved':frozenset({'done','needs-right-quiet-route'})})
mark_change_only=Edits(facts={'done':Fact(frozenset({'deadline'}))})
edit_no_effect=Edits(out={'reserved':frozenset({'done'})})
instances=[
 ('harmless_new_path',a,new_behavior,set()),
 ('new_safe_step_enables_old_ingress',a,expose_old,{'safety'}),
 ('no_occupancy_but_late',a,deadline_only,{'deadline'}),
 ('audit_actions_need_hidden_state',a,information_only,{'realizability'}),
 ('mark_change_without_edge_change',a,mark_change_only,{'deadline'}),
 ('explicit_noop',a,edit_no_effect,set()),
]

b=g({'start':{'islandA','done'},'islandA':{'islandB'},'islandB':{'islandA'}},
    facts={'islandB':Fact(frozenset({'safety'}))})
delete_ingress=Edits(out={'start':frozenset({'done'})})
instances.append(('detach_live_SCC_not_self_supporting',b,delete_ingress,set()))
c=g({'start':{'done'},'old-root':{'post'},'post':{'post'}},roots=('start','old-root'),
    facts={'post':Fact(frozenset({'deadline'}))})
instances.append(('remove_live_root_and_keep_other',c,Edits(roots=frozenset({'start'})),set()))

uncertain_alias={'independent':new_behavior,'shared':expose_old}
# Union would splice together two installed laws: law 0 enables reaching
# port but not old unsafe continuation, law 1 enables continuation only.
d=g({'start':{'done'},'port':{'done'},'unsafe':{'done'}},
    facts={'unsafe':Fact(frozenset({'safety'}))})
splicing={'law0':Edits(out={'start':frozenset({'port'})}),
          'law1':Edits(out={'port':frozenset({'unsafe'})})}
invalid_union=Edits(out={'start':frozenset({'port','done'}),
                         'port':frozenset({'unsafe','done'})})

def chain(n):
    return {f'c{i}':{f'c{i+1}'} if i<n-1 else set() for i in range(n)}
large=g({'start':{'c0','other'},'pad':{'other'},'other':{'other'}, **chain(2000)})
cost_cases={
  'disjoint_short_branch':Edits(out={'start':frozenset({'c0','other','pad'})}),
  'new_edge_to_already_reached_branch':Edits(out={'other':frozenset({'other','c0'})}),
  'remove_nonwitness_from_already_reached_cycle':Edits(out={'other':frozenset()}),
  'unplug_entire_chain':Edits(out={'start':frozenset({'other'})}),
}
