"""Drive an exact pinned switcher through controlled callback orders."""
import json, sys
from itertools import product
from pathlib import Path

# The pinned parent harness supplies deterministic message/service stubs.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from switch_replay import Run, checked

class Interleaving(Run):
    def __init__(self, later, during, *, failed_indices=()):
        super().__init__([(True,True)],failed_indices=failed_indices)
        self.updates=iter(later)
        self.during=list(during)
        self.call_times=[]
        self.callback_times=[]
        self.t=0
    def receive(self,node,report):
        self.callback_times.append(self.t)
        from types import SimpleNamespace
        c,f=report
        node.robot_health_cb(SimpleNamespace(ceiling_robot=c,floor_robot=f))
    def step(self,node):
        if self.t==0:
            self.receive(node,(True,True))
            self.t=1
            return
        try: t,report=next(self.updates)
        except StopIteration:
            self.keep=False
            raise KeyboardInterrupt
        self.t=t
        if report is not None: self.receive(node,report)
    def call(self,rq):
        self.call_times.append(self.t)
        return super().call(rq)
    def wait(self,node,reply):
        if len(self.call_times)!=1: return
        for t,report in self.during:
            self.t=t
            self.receive(node,report)
        self.t=4
    def run_pinned(self,s):
        # Override only the ROS stub binding, not the pinned switcher text.
        import switch_replay as adapter
        orig=adapter.module
        def inject(name, **bindings):
            if name=="rclpy": bindings["spin_until_future_complete"]=self.wait
            return orig(name,**bindings)
        try:
            adapter.module=inject
            r=self.execute(s)
        finally:
            adapter.module=orig
        return {"call_times":self.call_times, "callbacks":self.callback_times,
                "floor_active":r["floor_active"],
                "ceiling_active":{"ceiling_robot_controller","gantry_controller"}<=set(r["active"]),
                "last_request":r["last_request"]}

def mailbox_reference(inflight, after, settled=4):
    """Exact actuation in this reference only; latest report is authoritative."""
    applied=(True,True)
    exits=[]
    latest=[(settled,inflight[-1][1])] if inflight else []
    for t,value in latest+after:
        if value is not None and value!=applied:
            exits.append((t,value))
            applied=value
    return exits

if __name__=="__main__":
    source=checked(sys.argv[1],"7e4378046bb514148af49b35f10bda68d561757a")
    disable=(True,False)
    enabled=(True,True)
    before="                rclpy.spin_once(self)"
    end="                self.recieved_msg = False"
    assert source.count(before)==source.count(end)==1
    patched=source.replace(before,"                if not self.recieved_msg:\n    "+before).replace(end,"")
    before_apply="            if self.recieved_msg:\n"
    assert patched.count(before_apply)==1
    patched=patched.replace(before_apply,before_apply+end+"\n")
    scenarios={
      "persists_without_repeat": ([(2,disable)],[(5,None)]),
      "persists_with_repeat": ([(2,disable)],[(5,None),(9,disable)]),
      "clears_during_old_switch": ([(2,disable),(3,enabled)],[(5,None)]),
      "same_stop_after_old_switch": ([],[(5,disable)]),
    }
    out={}
    for name,(during,later) in scenarios.items():
        p=Interleaving(later,during).run_pinned(source)
        ref=mailbox_reference(during,later)
        repaired=Interleaving(later,during).run_pinned(patched)
        assert repaired["call_times"]==[1]+[t for t,_ in ref]
        out[name]={"pinned":p,"mailbox_adjustment":repaired,
                   "latest_version_reference":ref}
    assert out["persists_without_repeat"]["pinned"]["call_times"]==[1]
    assert out["persists_without_repeat"]["latest_version_reference"]==[(4,disable)]
    assert out["persists_with_repeat"]["pinned"]["call_times"]==[1,9]
    assert out["persists_with_repeat"]["latest_version_reference"]==[(4,disable)]
    assert out["clears_during_old_switch"]["pinned"]["call_times"]==[1]
    assert not out["clears_during_old_switch"]["latest_version_reference"]
    assert not out["same_stop_after_old_switch"]["pinned"]["floor_active"]
    assert out["same_stop_after_old_switch"]["pinned"]["call_times"]==[1,5]
    # Evaluate every persistent/cleared word of up to four reports
    # during the old switch. No post-completion health callback is supplied.
    checked_cases=0
    for size in range(5):
        for vals in product(list(product((False,True),repeat=2)),repeat=size):
            during=[(2+j/5,v) for j,v in enumerate(vals)]
            following=[(5,None)]
            old=Interleaving(following,during).run_pinned(source)
            new=Interleaving(following,during).run_pinned(patched)
            want=vals[-1] if vals else (True,True)
            assert old["call_times"]==[1]
            assert new["call_times"]==([1] if want==(True,True) else [1,4])
            assert (new["ceiling_active"],new["floor_active"])==want
            checked_cases+=1
    f=Interleaving([(5,(True,True)),(6,(True,True))],[],
                   failed_indices=(0,)).run_pinned(patched)
    assert f["call_times"]==[1] and not f["floor_active"]
    out["checks"]={"bounded_wait_callback_words":checked_cases,
                   "failed_activation_still_lacks_retry":True}
    print(json.dumps(out,indent=2,sort_keys=True))
