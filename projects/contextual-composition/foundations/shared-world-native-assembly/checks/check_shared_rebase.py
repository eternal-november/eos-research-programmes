"""Independent finite diagnostics for the feedback/rebase note, not a proof."""
from fractions import Fraction as F
import json
# Single scope at world 0: active root and active existing child use the
# prescope cache; passive grandchild is rebased. Both active nodes add ports.
# Passive rebase changes world but preserves cache, so initialization is NOT natural.
world=0
old={():{'cache':0,'ports':('a',)}, ('a',):{'cache':0,'ports':('g',)},
     ('a','g'):{'cache':0,'ports':()}}
active={(),('a',)}
new_world=1
new={}
for path,state in old.items():
    new[path]={'cache':state['cache'],'ports':state['ports'],'world':new_world}
for path in active:
    new[path]['ports']=old[path]['ports']+('fresh',)
    # New seed captures actual post-world; old caches remain old.
    new[path+('fresh',)]={'cache':new_world,'ports':(),'world':new_world}
assert len(new)==5
for path,state in new.items():
    assert state['world']==1
    for port in state['ports']:
        assert path+(port,) in new
assert new[('a','g')]['cache']==0
assert new[('fresh',)]['cache']==1
assert new[('a','fresh')]['cache']==1
# a_* i(0) has cache 0, whereas i(1) has cache1. Finite closure needed neither equality.
assert new[('a','g')]['cache'] != new[('fresh',)]['cache']
# Joint coefficient projection nonfaithfulness: A0 != A1 but p A0=p A1=p.
p=(F(1),F(0))
A0=((F(1),F(0)),(F(0),F(0)))
A1=((F(1),F(0)),(F(0),F(1)))
def rowmul(v,A):return tuple(sum(v[i]*A[i][j] for i in range(2)) for j in range(2))
assert A0!=A1 and rowmul(p,A0)==rowmul(p,A1)==p
# Joint law comparison forced to identity by both bit projections.
diag={(0,0):F(1,2),(0,1):F(0),(1,0):F(0),(1,1):F(1,2)}
anti={pair:F(1,2)-value for pair,value in diag.items()}
assert all(sum(v for pair,v in diag.items() if pair[i]==b)==F(1,2)
           for i in (0,1) for b in (0,1))
assert all(sum(v for pair,v in anti.items() if pair[i]==b)==F(1,2)
           for i in (0,1) for b in (0,1))
assert diag!=anti
print(json.dumps({'status':'passed','old_nodes':len(old),'new_nodes':len(new),
 'active_ancestor_and_descendant':True,'old_child_rebase_not_reinitialization':True,
 'coefficient_maps_different_with_equal_primitive_projections':True,
 'same_marginals_different_supplied_joint':True,
 'scope':'finite witness checks only; no generic feedback initiality or coherence certification'},indent=2))
