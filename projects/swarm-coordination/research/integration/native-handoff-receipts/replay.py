import ast,enum,hashlib,itertools,json,sys,typing
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from types import SimpleNamespace as NS
import numpy as np
from receiver import Cut,confirm

PINS={
    'warehouse.py':'9797bf36970d5eb14fef7a150fab7562c450dff6',
    'rail.py':'ac9a1c35940119b59d54f1fed0b3a4c1238e0ef1',
    'agent_chains.py':'e8cadbf0a5eafda77360836f6aca704f7a2494ab',
    'resource.py':'b9d7a49948db753592d538974d391ff5c80e1d32',
    'agents.py':'dcf1becb179380bb775dd372bacb6445a3c12b67',
    'actions.py':'2029a97e6fa01f3c04bd4067d08eaef1911f4063'}
def tree(f):
    b=f.read_bytes()
    assert hashlib.sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==PINS[f.name],f
    return ast.parse(b)
def top(f,k):
    return next(x for x in tree(f).body if getattr(x,'name',None)==k)
def method(f,k):
    return next(y for x in tree(f).body if isinstance(x,ast.ClassDef)
                for y in x.body if isinstance(y,ast.FunctionDef) and y.name==k)
class GenericStub:
    def __class_getitem__(cls,parameter): return cls
def native_rail(src):
    files={k:src/k for k in PINS if k!='warehouse.py'}
    mod=[top(files['actions.py'],'RailEnvActions'),top(files['agents.py'],'_sanitize_entry_point'),
         top(files['agent_chains.py'],'MotionCheck'),top(files['resource.py'],'GridResourceMap')]
    # These are actual methods and the supplied methods do not use full
    # RailEnv initialization. Strip decorators on the single static helper.
    f=method(files['rail.py'],'_candidate_entry_points'); f.decorator_list=[]; mod.append(f)
    mod.extend(method(files['rail.py'],k) for k in ('distribute','handle_done_state'))
    g=dict(vars(typing),np=np,fastenum=NS(Enum=enum.Enum),lru_cache=lru_cache,AgentHandle=int,Resource=tuple,
           ResourceMap=GenericStub,Vector2D=tuple,EntryPointT=tuple,EnvAgent=NS,
           env_utils=NS(AgentTransitionData=NS),ZERO_FRACTION=Fraction(0))
    exec(compile(ast.Module(body=mod,type_ignores=[]),'flatland-selected.py','exec'),g)
    return NS(**{x.name:g[x.name] for x in mod})

class Speed:
    def set(self,s,d,e,crossed=False):
        self.speed=s; self.distance=d;self.crossed=crossed

def rail_case(n,mode,remove,overpass,tick):
    # Coordinates below are ordinary station/track cells. The native grid
    # resource map optionally splits the crossing by direction parity.
    port=(1,1); far=(8,8)
    old_here=(port,0); old_next=((0,1),0); old_cont=((0,0),3)
    new_here=(((1,0) if overpass else (2,1)),(1 if overpass else 0))
    new_next=(port,(1 if overpass else 0))
    new_cont=(((1,2) if overpass else (0,1)),(1 if overpass else 0))
    ind_here=((3,3),1); ind_next=((3,4),1); ind_cont=((3,5),1)
    route=((old_here,old_next,old_cont),(new_here,new_next,new_cont),(ind_here,ind_next,ind_cont))
    res=n.GridResourceMap({port} if overpass else set())
    prot=res.get_resource(old_here,old_next)
    W=NS(resource_check=n.MotionCheck(),remove_agents_at_target=remove,rail=NS(edge_length=lambda a,b:Fraction(1)),
         _elapsed_steps=tick, distance_map=None, rewards_dict={i:0 for i in range(4)},dones={})
    W.rewards=NS(cumulate=lambda a,b:a+b,step_reward=lambda **kw:0)  # never source of task event
    W.handle_done_state=lambda a:n.handle_done_state(W,a)
    agents=[]; trans=[]
    for i,(c,d,z) in enumerate(route):
        target=[new_next] if i==1 else [(far,0)]
        a=NS(handle=i,old_entry_point=c,current_entry_point=c,next_entry_point=d,
             target_entry_point=None,arrival_time=None,targets=target,speed_counter=Speed())
        halt=i==0 and mode=='malfunction'
        mid=i==0 and mode=='mid_cell'
        c1,d1=n._candidate_entry_points(n.RailEnvActions.MOVE_FORWARD,c,d,False,halt,tick,z,1,c,
                False,not mid,False,False,False,False)
        # Use supplied distance/speed state. The exact selected candidate
        # transition above and MotionCheck/commit below are not reimplemented.
        td=NS(candidate_entry_point=c1,candidate_next_entry_point=d1,is_cell_exit=not mid,
              done=False,candidate_distance=None if remove and c1 in target else Fraction(0),
              candidate_speed=Fraction(1),distance=Fraction(0),edge_length=Fraction(1))
        W.resource_check.add_agent(i,res.get_resource(c,d),res.get_resource(c1,d1))
        agents.append(a); trans.append(td)
    W.resource_check.find_conflicts()
    before=tuple((i,res.get_resource(c,d)) for i,(c,d,z) in enumerate(route))
    for a,t in zip(agents,trans):n.distribute(W,a,t)
    post=tuple((i,res.get_resource(a.current_entry_point,a.next_entry_point)) for i,a in enumerate(agents))
    # Newly reached target is recorded by native handle_done_state before
    # optional removal. A command or optimistic permission cannot mint it.
    service=tuple((i,res.get_resource(a.target_entry_point,None)) for i,a in enumerate(agents)
                  if a.arrival_time==tick)
    restore=dict(post)
    restore.update(service)
    applied=tuple(sorted(restore.items()))
    pend=frozenset((i,'trip_target') for i,a in enumerate(agents) if a.arrival_time is None)
    accepted=confirm(Cut(before,applied,service,pend),prot,0,1,'trip_target')
    assert accepted==(mode=='move' and not overpass)
    assert dict(post)[2]!=dict(before)[2]
    assert trans[0].resource_check     # holds and moves can all report true
    if mode!='move': assert dict(post)[0]==dict(before)[0]
    if remove and service: assert dict(post)[1] is None
    if overpass: assert service and service[0][1]!=prot
    endpoint_only=confirm(Cut(before,post,service,pend),prot,0,1,'trip_target')
    coordinates={x[0] if isinstance(x,tuple) and isinstance(x[0],tuple) else x
                 for _,x in service}
    coordinate_only=port in coordinates
    assert endpoint_only==(accepted and not remove)
    assert coordinate_only==(mode=='move' or overpass)
    assert not confirm(Cut(before,applied,(),pend),prot,0,1,'trip_target')
    if service:
        before_receipt=n.handle_done_state
        W._elapsed_steps=tick+1
        a=agents[1]
        previous_target=a.target_entry_point
        before_receipt(W,a)
        assert a.arrival_time==tick and a.target_entry_point==previous_target
    return dict(mode=mode,remove=remove,overpass=overpass,verdict=accepted,old_grant=trans[0].resource_check,
                new_grant=trans[1].resource_check,endpoint_only=endpoint_only,coordinate_only=coordinate_only,
                before=before,applied=applied,after=post,service=service,
                source_retired=agents[0].arrival_time is not None)

def warehouse_cases(src):
    n=load_warehouse(src)
    R=rot
    P=((1,1),(2,1),(2,2),(1,2),(3,3)); D=n.Direction
    ds=(D.RIGHT,D.DOWN,D.LEFT,D.UP,D.RIGHT)
    out=[]
    for erased,stand in itertools.product((False,True),repeat=2):
        w=R.plant(n,P,ds,((0,P[0]),(3,P[3]),(None if stand else 1,P[1])),P[0],[1])
        w.np_random=NS(choice=lambda choices:next(x for x in choices if x.id==1))
        w.agents[0].has_delivered=True
        _,reward,*_=n.step(w,[1,1,0 if erased else 1,1,1])
        after=tuple((i,(a.x,a.y)) for i,a in enumerate(w.agents))
        applied=after
        svc=tuple((i,p) for i,p in applied if reward[i]==.5 and p==P[0] and w.agents[i].has_delivered)
        pend=frozenset((i,'shelf_return') for i,a in enumerate(w.agents) if a.has_delivered and a.carrying_shelf)
        accepted=confirm(Cut(tuple(enumerate(P)),applied,svc,pend),P[0],0,3,'shelf_return')
        assert accepted==(not erased and not stand)
        assert (0,'shelf_return') in pend
        out.append(dict(erased=erased,standing=stand,verdict=accepted,rewards=reward,after=after))
    return out

def load_warehouse(src):
    p=src/'warehouse.py'; tree(p)
    # Native previous harness's hash loader expects its original basename.
    # The alias lives only in the hash table, not in any source rewrite.
    rot.iso.PINS[p.name]=PINS[p.name]
    return rot.engine(p)

if __name__=='__main__':
    if (Path(__file__).with_name('rware_rotation.py')).is_file(): import rware_rotation as rot
    else:
        sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'rware-simultaneous-port'))
        import check as rot
    s=Path(sys.argv[1]); rail=native_rail(s)
    rows=[rail_case(rail,m,r,g,1) for m,r,g in itertools.product(
          ('move','mid_cell','malfunction'),(False,True),(False,True))]
    print(json.dumps(dict(rail_rows=rows,warehouse_rows=warehouse_cases(s)),sort_keys=True,separators=(',',':')))
