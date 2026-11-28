#!/usr/bin/env python3
"""Matched passage capability frontiers from public native phase histories."""
from pathlib import Path
from itertools import product
import argparse,importlib.util,json,subprocess as sp,tempfile
HERE=Path(__file__).resolve().parent
PIN="6b2881248f3f09b6bfe2a45161500d486773728c"
def main():
    p=argparse.ArgumentParser()
    p.add_argument("--source",type=Path,default=HERE)
    p.add_argument("--template",type=Path,default=HERE/"door_effect.cc.in")
    p.add_argument("--policy",type=Path,default=HERE/"native_policy.js")
    p.add_argument("--model",type=Path,default=HERE/"development.js")
    p.add_argument("--extractor",type=Path,default=HERE/"door_effect.py")
    a=p.parse_args()
    import hashlib
    raw=a.extractor.read_bytes()
    assert hashlib.sha1(f"blob {len(raw)}\0".encode()+raw).hexdigest()=="0f440057c3e7a334fe1f18195502a8aad00b179d"
    spec=importlib.util.spec_from_file_location("door_effect",a.extractor)
    extract=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(extract)
    extract.exact(a.policy,"0dfee82b1e547687a3ba2a4f2932a8b5c946cee3")
    src=a.source
    u=extract.exact(src/"utils.hpp","a84cf6fcbb95b2fda96e580c6e248cab33aa46c1")
    d=extract.exact(src/"door.cpp","3972e4308f44ad3cd90a0e139484f9d2d6813b68")
    f=extract.exact(src/"DoorOpen.cpp","c57241738d140d45a958457a69ae2c563e6e4988")
    h=extract.exact(src/"SupervisorHasSession.cpp","691945ac652bfc1a8ad8ebea403a7de11ee8d2c8")
    code=extract.exact(a.template,"0e7e90cdf8d418965e5ba93af0a50ada2132ee11")
    code=code.split("int main(){",1)[0]+"\n#include <array>\n"+(HERE/"frontier_main.inc").read_text()
    for marker,symbol in zip(("JOINT","WITHIN","MODE","TARGET","COMMAND","PUBLISH"),(
        "Entity get_joint_entity","bool is_joint_at_position","DoorModeCmp get_current_mode",
        "double calculate_target_velocity","void command_door","void publish_state")):
        code=code.replace(marker+"_SRC",extract.body(d,r"^  "+symbol+r"\("))
    code=code.replace("UPDATE_SRC",extract.body(f,r"^void DoorOpen::ActivePhase::_update_status\("))
    code=code.replace("SESSION_SRC",extract.body(h,r"^bool supervisor_has_session\("))
    with tempfile.TemporaryDirectory() as tmp:
        wd=Path(tmp)
        (wd/"door.cc").write_text(code);(wd/"utils.hpp").write_text(u)
        sp.run(["c++","-std=c++20","-O2","door.cc","-o","door"],cwd=wd,check=True)
        runs=0
        with sp.Popen([wd/"door"],text=True,stdin=sp.PIPE,stdout=sp.PIPE,bufsize=1) as t:
            def emit(*xs):
                t.stdin.write(" ".join(map(str,xs))+"\n");t.stdin.flush()
            def transition(pos,vel,closed):
                x=(-512-pos) if closed else -pos
                if abs(x)<4:x=0
                sign=-1 if x<0 else 1
                x*=sign;vel*=sign
                v=min(x,16,1+vel)
                if vel>0 and x>0 and vel*vel>=2*x:v=vel-1
                return pos+sign*v,sign*v
            def reference(w,expiry,deadline):
                sw,close=w
                out=[]
                for g in (0,1):
                    pairs=[(0,-5 if g==sw else -2)]
                    for k in range(deadline):pairs.append(transition(*pairs[-1],k>=1 and k>=expiry and g==close))
                    out.extend(p for p,_ in pairs)
                return out
            arms=[
              ("writer-fast",2,4,0,1,5,True),
              ("public-no-hold-short",0,2,3,3,10,False),
              ("history-delayed",0,2,3,7,11,True),
              ("same-history-stronger-hold",2,2,3,7,11,False),
              ("first-loss-delayed",0,3,3,7,11,True),
              ("history-omits-third",0,2,2,7,11,False),
              ("history-misses-start",0,2,3,8,11,False),
              ("phase-third-delayed",0,1,3,7,11,False),
              ("phase-sixth-delayed",0,1,6,7,11,False),
              ("phase-seventh-live",0,1,7,7,11,True),
              ("phase-seventh-delayed",0,1,7,8,12,True),
              ("phase-with-hold",4,1,3,3,7,True),
              ("phase-with-hold-lag1",5,1,3,4,8,True),
              ("phase-lag1-old-expiry",4,1,3,4,8,False),
              ("fixed-gate-with-hold",8,0,0,0,11,True),
              ("fixed-gate-no-hold",0,0,0,0,11,False),
            ]
            outcomes={}
            for name,expiry,kind,sample,arrive,deadline,expected in arms:
                worlds=list(product((0,1),(-1,0,1)))
                menu=list(product((0,1),range(arrive,max(deadline-3,arrive+1))))
                encode=lambda act: json.dumps(act,separators=(",",":"))
                def replay(w,select):
                    nonlocal runs
                    runs+=1
                    emit(*w,expiry,kind,sample,arrive,deadline)
                    line=t.stdout.readline().split();assert line[0]=="L"
                    view=list(map(int,line[1:]))
                    choice=select(view)
                    emit(*(choice if choice is not None else (-1,0)))
                    line=t.stdout.readline().split();assert line[0]=="O"
                    transit,independent,*trace=map(int,line[1:])
                    assert independent==deadline and trace==reference(w,expiry,deadline)
                    return view,bool(transit),trace
                rows, physical = [], []
                for w in worlds:
                    rr=[replay(w,lambda _,act=act:act) for act in menu]
                    assert len({tuple(v) for v,_,_ in rr})==1
                    rows.append([dict(view=rr[0][0],winners=[encode(a) for a,(_,win,_) in zip(menu,rr) if win])])
                    positions=rr[0][2]
                    for tick in range(deadline-3):
                        for g in (0,1):
                            offset=g*(deadline+1)+tick
                            if all(v>-8 for v in positions[offset:offset+5]):
                                physical.append((w,g,tick))
                data=json.dumps(dict(worlds=rows,plans=[name],actions=[encode(x) for x in menu]))
                selected=json.loads(sp.check_output(["node",str(a.policy),str(a.model),PIN],input=data,text=True))
                assert bool(selected)==expected,name
                earliest=None
                if selected:
                    _,policy=selected[0]
                    def choose(v):return json.loads(next(a for vv,a in policy if vv==v))
                    for w in worlds:assert replay(w,choose)[1]
                    earliest=max(choose(row[0]["view"])[1]+4 for row in rows)
                else:
                    for w in worlds:assert not replay(w,lambda _:None)[1]
                if name=="public-no-hold-short":
                    assert not any(w==(0,1) for w,_,_ in physical)
                if name=="history-delayed":
                    assert [t for w,g,t in physical if w==(0,1) and g==0]==[7]
                if name=="same-history-stronger-hold":
                    assert rows[1][0]["view"]==rows[2][0]["view"]
                    assert set(rows[1][0]["winners"]).isdisjoint(rows[2][0]["winners"])
                if name=="history-omits-third":
                    assert rows[2][0]["view"]==rows[4][0]["view"]
                    assert set(rows[2][0]["winners"]).isdisjoint(rows[4][0]["winners"])
                outcomes[name]={"viable":expected,"worst_exit":earliest,"cells":len({tuple(row[0]["view"]) for row in rows}),"policy":selected[0][1] if selected else [],"configuration":[expiry,kind,sample,arrive,deadline]}
            t.stdin.close();assert t.wait()==0
    print(json.dumps(dict(runs=runs,outcomes=outcomes),sort_keys=True))
if __name__=="__main__":main()
