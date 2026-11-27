import ast, dataclasses, enum, itertools, json, math, pathlib, re, sys
from types import SimpleNamespace as N
from typing import Any, List, Union

P=pathlib.Path(sys.argv[1])
def selected(name, names=(), methods=()):
    p=P/name; t=ast.parse(p.read_text(),filename=str(p))
    chosen=[v for v in t.body if getattr(v,'name',None) in names]
    for cls,m in methods:
        C=next(v for v in t.body if isinstance(v,ast.ClassDef) and v.name==cls)
        chosen.extend(g for g in C.body if isinstance(g,ast.FunctionDef) and g.name==m)
    assert len(chosen)==len(names)+len(methods)
    exec(compile(ast.Module(body=chosen,type_ignores=[]),str(p),'exec'),globals())

@dataclasses.dataclass
class PlanTuple:
    x:float
    y:float
    time:float
@dataclasses.dataclass
class Location:
    x:float
    y:float
Point=Location
@dataclasses.dataclass
class Pose:
    position:Any
    orientation:Any
def Point(x,y,z=0):return N(x=x,y=y,z=z)
def Quaternion(x,y,z,w):return N(x=x,y=y,z=z,w=w)
def calculate_distance(a,b):return math.hypot(a.x-b.x,a.y-b.y)
NOMINAL_SPEED_M_PER_S=2
Enum=enum.Enum
selected('status.py',('Status',))
selected('vertex.py',('Vertex','loc','time','calculate_plan_tuple_distance'))
vertex=N(Vertex=Vertex)
selected('dep.py',('Dependency',))
selected('comms.py',('parse_pose',),(('Comms','callback'),))
selected('controller.py',methods=(('Controller','controller_task'),))
assert 'orientation=Quaternion(x=0.0, y=0.0, z=0.0, w=1.0)' in (P/'agent.py').read_text()

class Log:
    def debug(self,*x):pass
    def warn(self,*x):pass
    def info(self,*x):pass
class CommsFixture:
    def __init__(self,v):
        self.current_vertex=v;self.sub_link='local pose';self.logger=Log();self.sent=[]
    def get_curr_vertex(self):return self.current_vertex
    def get_agent_id(self):return self.current_vertex.agent_id
    def publish_pose_goal(self,goal):self.sent.append(goal.position.x)
    callback=callback
def setup():
    A=Vertex('agent0',[PlanTuple(2,0,0),PlanTuple(4,0,3)],0,Status.IN_PROGRESS)
    B=Vertex('agent1',[PlanTuple(1,0,0),PlanTuple(3,0,4)],0,Status.STAGED)
    S=Vertex('agent2',[PlanTuple(7,1,0),PlanTuple(8,1,3)],0,Status.STAGED)
    B.add_dependency(Dependency(A,B,True))
    base,side=CommsFixture(B),CommsFixture(S)
    controller=N(comms=[base,side],logger=Log(),
                 sadg=N(optimize=lambda **kw:None),visualize_sadg=False)
    return A,CommsFixture(A),base,side,controller
def pose_at(x,theta):
    return Pose(Point(x,0),Quaternion(0,0,math.sin(theta/2),math.cos(theta/2)))
for x,theta,reached in ((3.9,0,False),(4,0,True),(4,math.pi/2,True)):
    a,aio,base,side,c=setup()
    aio.callback(pose_at(x,theta))
    controller_task(c)
    assert (a.status is Status.COMPLETED)==reached and len(base.sent)==int(reached)
    assert side.sent==[8]

# Body and timed evolution are separately declared; this is not stock
# ROS plant kinematics. Local sample is from known current frame, named
# body profile and immutable through-crossing motion/authority law.
def peak(lo,hi,L,W):
    h=lambda q: L*abs(math.cos(q))+W*abs(math.sin(q))
    crit=math.atan2(W,L)
    if any(lo<=k*math.pi+s*crit<=hi for k in range(math.floor(lo/math.pi)-2,
          math.ceil(hi/math.pi)+3) for s in (-1,1)):
        return math.hypot(L,W)
    return max(h(lo),h(hi))

def maximum_by_quadrants(lo,hi,L,W):
    cuts=[lo]+[k*math.pi/2 for k in range(math.floor(lo/(math.pi/2)),
            math.ceil(hi/(math.pi/2))) if lo<k*math.pi/2<hi]+[hi]
    values=[]
    for a,b in zip(cuts,cuts[1:]):
        quadrant=math.floor((a+b)/math.pi)
        offset=math.atan2(W,L) if quadrant%2==0 else math.atan2(L,W)
        at=min(max(quadrant*math.pi/2+offset,a),b)
        values.append(L*abs(math.cos(at))+W*abs(math.sin(at)))
    return max(values)

checks=0
for theta,w,age,cross,L,W in itertools.product(
        (0,.5,1.2,math.pi/2,2.1,3.0),(.0,.1,.4),(0,1,2),(1,2,4),(.9,1.5,2),(.4,.5)):
    change=w*(age+cross)
    u,v=theta-change,theta+change
    a=peak(u,v,L,W);b=maximum_by_quadrants(u,v,L,W)
    assert abs(a-b)<1e-9,(u,v,a,b)
    checks+=1
records={}
for label,theta,turn,age,span in [('face_short',math.pi/2,0,0,1),
                                 ('face_long',0,0,0,1),
                                 ('short_heading_ages',math.pi/2,.15,1,1),
                                 ('same_heading_older',math.pi/2,.15,2,1)]:
    a,aio,base,side,c=setup()
    aio.callback(pose_at(4,theta))
    # Native admission on a fresh, independent fixture.
    controller_task(c);assert base.sent and side.sent
    threshold=peak(theta-turn*(age+span),theta+turn*(age+span),1.5,.5)
    # Use the same downstream dependency and execution method after
    # substituting a physically qualified release predicate.
    n,_,nbase,nside,nc=setup()
    if 4-threshold>3:n.set_status(Status.COMPLETED)
    controller_task(nc)
    records[label]=dict(native_send=base.sent,guarded_send=nbase.sent,side=nside.sent,
                        worst_tail_x=round(4-threshold,6))
assert records['face_short']['guarded_send']==[3]
assert not records['face_long']['guarded_send']
assert records['short_heading_ages']['guarded_send']==[3]
assert not records['same_heading_older']['guarded_send']
print(json.dumps(dict(coordinate_identity_cases=3,swept_comparisons=checks,cases=records),
                 indent=2,sort_keys=True))
