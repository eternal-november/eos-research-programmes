import json
root=lambda r,p,t:('Root',r,tuple(p),t)
birth=lambda n,o,p,t:('Birth',n,o,tuple(p),t)
actor=lambda a,l:('Actor',a,l)
material=lambda a,l:('Material',a,l)
a=root('run',('root',),'X'); owner=actor(a,'self')
requests=[(0,owner,('p',),'M'),(0,owner,('q',),'M'),
          (0,owner,('p','child'),'M'),(1,owner,('p',),'M')]
ns=[birth(*r) for r in requests]
assert len(set(ns))==4
names=[constructor(n,'self') for n in ns for constructor in (actor,material)]
assert len(set(names))==8
# Grouping uses the same primitive list, never introduces wrapper names.
flat=list(requests)
grouped=[requests[:1],requests[1:3],requests[3:]]
assert [birth(*r) for g in grouped for r in g]==[birth(*r) for r in flat]
# All raw branch profiles allocate absent slots only conditionally. Zero mass
# does not delete a present request; no random name dimension is introduced.
profiles={0:['p'],1:['p','q']}; probabilities={0:1,1:0}
rows={z:[birth(2,owner,(p,),'M') for p in ps] for z,ps in profiles.items()}
assert len(rows[1])==2 and probabilities[1]==0
for k,m,n in [(0,1,2),(3,4,5),(10,0,7)]:
    assert (k+m)+n==k+(m+n)
print(json.dumps({'distinct_invocations':4,'typed_actor_material_names':8,
'grouping_invariance':'PASS','zero_branch_allocation':'PASS',
'event_offset_associativity':'PASS','extra_name_random_coordinates':0,
'scope':'finite naming diagnostics; native-copy and coherence proofs remain textual'},indent=2))
# Recursive suffix substitution: the second suffix refers to a first-suffix
# actor; shifting only the outer birth would leave that sponsor wrongly dated.
def subst(t, offset, env, qualify=False):
    if t[0]=='Param': return env[t[1]]
    if t[0]=='Root': return t
    if t[0]=='Actor': return ('Actor',subst(t[1],offset,env,qualify),t[2])
    if t[0]=='Birth':
        n=t[1]+offset
        event=('run-A',n) if qualify else n
        return ('Birth',event,subst(t[2],offset,env,qualify),t[3],t[4])
    raise ValueError(t)
root_name=('Root',('run-A','root'),(), 'X')
first=('Actor',('Birth',0,('Param','root'),('p',),'M'),'self')
second=('Birth',0,('Param','owner'),('q',),'L')
combined=subst(second,1,{'owner':first})
left=subst(combined,7,{'root':root_name},True)
owner_after_prefix=subst(first,7,{'root':root_name},True)
right=subst(second,8,{'owner':owner_after_prefix},True)
assert left==right
assert left[1]==('run-A',8) and left[2][1][1]==('run-A',7)
assert ('Birth',('run-A',0),'external',('p',),'M') != ('Birth',('run-B',0),'external',('p',),'M')
print('Recursive suffix sponsor substitution and independent-run separation: PASS')
