#!/usr/bin/env python3
"""Transfer the fixed two-cut chooser to local door-actuation evidence."""
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
    code=code.split("int main(){",1)[0]+"\n#include <array>\n"+(HERE/"gate_main.inc").read_text()
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
            def replay(w,plan,expiry,deadline,k):
                nonlocal runs
                runs+=1
                swapped,close,link=w
                emit(swapped,close,expiry,plan,link,deadline)
                first=t.stdout.readline().split();assert first[0]=="L"
                view=[int(n) for n in first[1:]]
                choice=k(view)
                emit(*(choice if choice is not None else (-1,0)))
                ans=t.stdout.readline().split();assert ans[0]=="O"
                good,independent,_=map(int,ans[1:])
                assert independent==deadline
                return view,bool(good)
            results={}
            actions=list(product((0,1),range(4)))
            encode=lambda a: json.dumps(a,separators=(",",":"))
            probes=["public","pre-change-read","fresh-read"]
            for expiry,deadline,report in product(range(6),(4,5,6),(0,1)):
                histories=list(product((0,1),(-1,0,1),(report,)))
                converted=[]
                for w in histories:
                    options=[]
                    for plan in range(3):
                        all_out=[replay(w,plan,expiry,deadline,lambda _,a=a:a) for a in actions]
                        assert len({tuple(v) for v,_ in all_out})==1
                        options.append(dict(view=all_out[0][0],winners=[encode(a) for a,(_,yes) in zip(actions,all_out) if yes]))
                    converted.append(options)
                inp=json.dumps(dict(worlds=converted,plans=probes,actions=list(map(encode,actions))))
                certified=json.loads(sp.check_output(["node",str(a.policy),str(a.model),PIN],input=inp,text=True))
                for no,policy in certified:
                    def decode(v):
                        return json.loads(next(k for vv,k in policy if vv==v))
                    assert all(replay(w,no,expiry,deadline,decode)[1] for w in histories)
                if not certified:
                    assert all(not replay(w,0,expiry,deadline,lambda _:None)[1] for w in histories)
                by_name={probes[i]:v for i,v in certified}
                exactly={"fresh-read"} if expiry>=2 and deadline>=5 and report else set()
                assert set(by_name)==exactly
                if exactly:
                    assert sorted(by_name["fresh-read"])==[[[0,1],"[0,0]"],[[1,1],"[1,0]"]]
                results[f"{expiry}/{deadline}/{report}"]={probes[i]:p for i,p in certified}
            t.stdin.close();assert t.wait()==0
    print(json.dumps(dict(runs=runs,results=results),sort_keys=True))
if __name__=="__main__":main()
