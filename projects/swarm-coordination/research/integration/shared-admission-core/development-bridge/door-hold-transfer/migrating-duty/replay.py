#!/usr/bin/env python3
"""Exercise scoped authorization at the native door writer cut."""
from pathlib import Path
from itertools import product
import argparse,importlib.util,json,subprocess as sp,tempfile,sqlite3
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
        # A durable authored source adapter. Both logs have identical presented
        # candidates; only named OLD authority rows differ after reopening.
        def decode(db,cut):
            rows=db.execute("select site from appointment where name=? and cut=?",("OLD",cut)).fetchall()
            assert len(rows)<=1
            return rows[0][0] if rows else -1
        def build(w):
            path=wd/f"journal_{w[0]}_{w[1]}"
            with sqlite3.connect(path) as db:
                db.executescript("""
                    create table latch(site integer primary key, target text);
                    insert into latch values (0,'CLOSE'),(1,'CLOSE');
                    create table appointment(name text,cut integer,site integer,
                        primary key(name,cut))""")
                db.executemany("insert into appointment values ('OLD',?,?)",
                               [(cut,site) for cut,site in zip((3,4),w) if site>=0])
            # Explicit close/reopen, not a supplied current OPEN row.
            db.close()
            with sqlite3.connect(path) as db:
                assert db.execute("select target from latch order by site").fetchall()==[("CLOSE",)]*2
                pair=(decode(db,3),decode(db,4))
            db.close()
            assert pair==w
            return pair
        static=[(-1,-1),(0,0),(1,1)]
        migrating=static+[(0,1),(1,0)]
        verified={w:build(w) for w in migrating}

        cases=0
        output={}
        with sp.Popen([wd/"door"],stdin=sp.PIPE,stdout=sp.PIPE,text=True,bufsize=1) as proc:
            def request(*fields):
                proc.stdin.write(" ".join(map(str,fields))+"\n")
                proc.stdin.flush()
            def one(w,report,mask,writer,choose):
                nonlocal cases
                cases+=1
                request(*verified[w],report,mask,writer)
                obs=proc.stdout.readline().split()
                assert obs[0]=="C" and obs[1:3]==["1","1"]
                view=list(map(int,obs[1:]))
                a=choose(view)
                request(a if a is not None else -1)
                named=proc.stdout.readline().split()
                assert named[0]=="O"
                cross,old,authority,independent,dip,first,minother=map(int,named[1:])
                assert independent and minother<0
                if writer in (0,2):
                    want_cross=(a is not None and (mask&(1<<a)) and
                                (writer==2 or a!=w[1] or a==2))
                    want_old=writer==0 or a not in (site for site in w if site>=0)
                    assert (bool(cross),bool(old),bool(authority))==(bool(want_cross),want_old,True)
                return view, bool(cross and old and authority and independent), [cross,old,authority,independent,dip,first]
            plans=list(range(1,8))
            actions=[0,1,2]
            def factored(worlds,report,writer,mask):
                groups={}
                for first,second in worlds:
                    label=first if report else -2
                    legal=set()
                    for a in actions:
                        if not mask&(1<<a):
                            continue
                        good=(a!=second if writer==0 else
                              False if writer==1 else
                              a not in (first,second) if writer==2 else
                              first==second and a!=second if writer==3 else
                              second<0 and (a!=first or first<0))
                        if good:
                            legal.add(a)
                    groups[label]=groups.get(label,set(actions)) & legal
                return groups if all(groups.values()) else {}

            for env,report,writer in product(range(2),range(2),range(5)):
                worlds=static if env==0 else migrating
                matrix=[]
                for w in worlds:
                    opts=[]
                    for mask in plans:
                        arms=[one(w,report,mask,writer,lambda _,a=a:a) for a in actions]
                        assert all(view==arms[0][0] for view,_,_ in arms)
                        opts.append(dict(view=arms[0][0],winners=[a for a,(_,ok,_) in zip(actions,arms) if ok]))
                    matrix.append(opts)
                req=json.dumps(dict(worlds=matrix,plans=plans,actions=actions))
                checked=json.loads(sp.check_output(["node",str(HERE/"native_policy.js"),str(HERE/"development.js"),PIN],input=req,text=True))
                masks=[plans[i] for i,_ in checked]
                expected=([3,4,5,6,7] if env==0 and report else [4,5,6,7]) if writer in (0,2) or (writer==3 and env==0) else []
                # Targeted motor hold does not repair an overlapping live
                # appointment, so here it has the same lawful service region.
                assert masks==[m for m in plans if factored(worlds,report,writer,m)]
                for i,table in checked:
                    model=factored(worlds,report,writer,plans[i])
                    assert all(a in model[v[-1]] for v,a in table)
                assert masks==expected,(env,report,writer,masks,expected)
                for i,tab in checked:
                    assert all(one(w,report,plans[i],writer,lambda v:next(a for u,a in tab if u==v))[1] for w in worlds)
                output[f"{env}/{report}/{writer}"]=masks
            witness={}
            for name,w,report,a,writer in [
                ("no appointment",(-1,-1),0,0,0),
                ("old live",(0,0),0,0,0),
                ("stable",(1,1),1,0,0),
                ("moves onto crossing",(1,0),1,0,0),
                ("holds gate but misses OLD",(1,0),1,0,2),
                ("leave first gate after one tick",(0,1),1,0,0),
                ("isolated alternate",(1,0),1,2,0)
            ]:
                witness[name]=one(w,report,7,writer,lambda _:a)
            assert witness["no appointment"][0]==witness["old live"][0]
            assert witness["stable"][0]==witness["moves onto crossing"][0]
            assert witness["stable"][1] and not witness["moves onto crossing"][1]
            assert witness["moves onto crossing"][2][:4]==[0,1,1,1]
            assert witness["holds gate but misses OLD"][2][:4]==[1,0,1,1]
            assert witness["leave first gate after one tick"][2]==[1,1,1,1,1,1]
            assert witness["isolated alternate"][1]
            proc.stdin.close()
            assert proc.wait()==0
        print(json.dumps(dict(runs=cases,results=output,witness=witness),sort_keys=True))
if __name__=="__main__":main()
