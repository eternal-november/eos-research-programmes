"""Execute the pinned switcher against finite offline ROS stubs."""
import json, sys, types
from extract import checked

def module(name, **bindings):
    m=types.ModuleType(name)
    vars(m).update(bindings)
    sys.modules[name]=m
    if "." in name:
        package,attr=name.rsplit(".",1)
        setattr(sys.modules[package],attr,m)
    return m

class Request:
    BEST_EFFORT=1
    def __init__(self):
        self.activate_controllers=[]
        self.deactivate_controllers=[]

class Reply:
    def __init__(self, ok): self.ok=ok
    def result(self): return self

class Run:
    def __init__(self, health, failed_indices=(), partial_indices=()):
        self.health=iter(health)
        self.active=set()
        self.requests=[]
        self.states=[]
        self.failed=set(failed_indices)
        self.partial=set(partial_indices)
        self.errors=0
        self.keep=True

    def step(self, node):
        try: c,f=next(self.health)
        except StopIteration:
            self.keep=False
            raise KeyboardInterrupt
        self.states.append(sorted(self.active))
        node.robot_health_cb(types.SimpleNamespace(ceiling_robot=c, floor_robot=f))

    def call(self, rq):
        start=list(rq.activate_controllers)
        stop=list(rq.deactivate_controllers)
        n=len(self.requests)
        self.requests.append([start,stop])
        if n in self.failed: return Reply(False)
        self.active.difference_update(stop)
        self.active.update(start[:1] if n in self.partial else start)
        return Reply(True)

    def execute(self, source):
        run=self
        class Node:
            def __init__(self,*args): pass
            def create_client(self,*args):
                return types.SimpleNamespace(call_async=run.call)
            def create_subscription(self,*args): return None
            def get_logger(self): return types.SimpleNamespace(error=run.error)
        module("rclpy",ok=lambda:run.keep,spin_once=run.step,
               spin_until_future_complete=lambda *args:None)
        module("rclpy.node",Node=Node)
        module("rclpy.executors",SingleThreadedExecutor=object)
        module("ariac_msgs"); module("ariac_msgs.msg",Robots=object)
        module("controller_manager_msgs")
        module("controller_manager_msgs.srv",SwitchController=types.SimpleNamespace(Request=Request))
        space={"__name__":"archived"}
        exec(compile(source,"pinned_switcher","exec"),space)
        node=space["RobotControllerSwitcher"]()
        node.run()
        return {"requests":len(self.requests),"errors":self.errors,
                "last_request":self.requests[-1],
                "floor_active":{"floor_robot_controller","linear_rail_controller"}<=self.active,
                "floor_assumed_active":node.floor_robot_state,
                "active":sorted(self.active)}
    def error(self,*args): self.errors+=1

def read_rows(path):
    with open(path) as f: rows=[list(map(int,l.split())) for l in f]
    assert len(rows)==12
    # Assert all intermediate inputs including the same-cut start order.
    for (case,t,ceiling,floor,camera,logical,stop_r,stop_s,live_r,live_s) in rows:
        assert ceiling==camera==(t not in [0,1])
        assert stop_r==stop_s==(t==2)
        assert live_r==live_s==(case!=0 and t>=case)
        assert floor==logical==(t==2 or not(case!=0 and t>=case))
    return rows

if __name__=="__main__":
    source=checked(sys.argv[1],"7e4378046bb514148af49b35f10bda68d561757a")
    rows=read_rows(sys.argv[2])
    result={}
    for c in range(3):
        health=[(bool(ceiling),bool(floor)) for case,_,ceiling,floor,*_ in rows if c==case]
        actual=Run(health).execute(source)
        assert actual["floor_active"]
        correct=[(bool(ceiling),not bool(live_r))
                 for case,_,ceiling,_,*_,live_r,live_s in rows if c==case]
        fixed=Run(correct).execute(source)
        assert fixed["floor_active"]==(c==0)
        assert {"ceiling_robot_controller","gantry_controller"}<=set(fixed["active"])
        result[f"second_starts_{c if c else 'never'}"]={
            "floor_report":health[-1][1],
            "floor_enabled_after_modeled_successful_switch":actual["floor_active"],
            "floor_enabled_with_union_oracle":fixed["floor_active"]}
    # The mock failure makes no controller changes. The code accepts
    # another identical health report but issues no replacement call.
    f=Run([(False,True)]*4,failed_indices=(0,)).execute(source)
    assert f["floor_assumed_active"] and not f["floor_active"]
    assert f["errors"]==f["requests"]==1
    result["failed_switch_with_three_equal_followup_reports"]=f
    # A hypothetical incomplete controller effect is a comparison case,
    # not a claimed ROS service outcome.
    p=Run([(False,True)]*4,partial_indices=(0,)).execute(source)
    assert p["floor_assumed_active"] and not p["floor_active"]
    assert p["errors"]==0 and p["requests"]==1
    result["modeled_partial_switch_with_ok"]=p
    print(json.dumps(result,sort_keys=True,indent=2))
