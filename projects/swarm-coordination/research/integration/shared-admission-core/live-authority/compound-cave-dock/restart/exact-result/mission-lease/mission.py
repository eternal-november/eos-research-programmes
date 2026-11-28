#!/usr/bin/env python3
import argparse
from collections import Counter
from decimal import Decimal as D
import hashlib
import importlib.util
import json
from pathlib import Path
from subprocess import Popen,PIPE,run
import sys
import tempfile

HERE=Path(__file__).resolve().parent
PARENT=HERE if (HERE/"result_transfer.py").is_file() else HERE.parent

def module(name,path):
    s=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(s)
    sys.modules[name]=m
    s.loader.exec_module(m)
    return m

code=PARENT/"result_transfer.py"
pin="3be5d2cc1f31a112a28af1a0d73d725d71718661"
data=code.read_bytes()
assert hashlib.sha1(f"blob {len(data)}\0".encode()+data).hexdigest()==pin
v=module("parent_result",code)
g=module("mission_geom",HERE/"mission_geom.py")

def probe(geom,paths,closed):
    e,_,_,_,_=g.load(geom,paths)
    box=e.GATE_A if closed=="A" else e.GATE_B
    start=g.PROBE
    # Ideal 5 m ray. Rock clearance and other entities were checked
    # for this whole beam by mission_geom, independent of the gate.
    near,far=box
    hit=min(D(5),max(D(0),near[1]-D(start[1]))) if (
        near[0]<=start[0]<=far[0] and near[2]<=start[2]<=far[2] and
        far[1]>=start[1]) else D(5)
    assert hit in (D("2.45"),D(5))
    return (256 if hit<3 else 128),hit

def patch(work):
    v.patch(work)
    cpp=work/"compound.cpp"
    y=cpp.read_text()
    k=v.r.replace
    y=k(y,"stateCode,late,replyCap,replyBytes;","stateCode,late,replyCap,replyBytes;\n double retryTime,replyTime;")
    y=k(y,">>replyCap>>replyBytes){",">>replyCap>>replyBytes>>retryTime>>replyTime){")
    y=k(y,'for(const auto& name:{"R","S","D"})','for(const auto& name:{"R","S","D","M"})')
    y=k(y,'for(const auto& name:{"P","Q","Base","R","S","D"})',
            'for(const auto& name:{"P","Q","Base","R","S","D","M"})')
    y=k(y,'who=="R"?rpose(now):who=="S"?fixed[4]:who=="D"?fixed[5]:fixed[1]',
          'who=="R"?rpose(now):who=="S"?fixed[4]:who=="D"?fixed[5]:who=="M"?Point{100,60,8}:fixed[1]')
    y=k(y,"replyAtQ=-1, denied=0;","replyAtQ=-1, denied=0, observedAtR=-1;")
    y=k(y,"else if(now==.9375){","else if(now==replyTime){")
    y=k(y,"    if(who==\"R\" && dst==\"S\"){",'''    if(who=="M" && dst=="R" && now==-90){
       assert(v.size()==1 && readWire(v)<=1 && observedAtR<0);
       observedAtR=readWire(v)==1?256:128;
       return;
    }
    if(who=="R" && dst=="S"){''')
    y=k(y,"const int val=now==-70?stateCode:256;",
          "const int val=now==-70?observedAtR:256;")
    y=k(y,'''  send("P","R","c",-100);assert(primaryContact==1);''','''  send("P","R","c",-100);assert(primaryContact==1);
  // M is the only supplier of the geometry-derived observation.
  assert(stateCode==256||stateCode==128);
  send("M","R",std::string(1,char(stateCode==256)),-90);
  assert(observedAtR==stateCode);''')
    y=k(y,'''if(!to.empty())send("Q",to,archived,.875);''','''if(!to.empty())send("Q",to,archived,retryTime);''')
    y=k(y,'''two(response),.9375);''','''two(response),replyTime);''')
    y=k(y,'''<<" "<<replyAtQ<<" "<<denied<<std::endl;''','''
        <<" "<<replyAtQ<<" "<<denied<<" "<<observedAtR<<std::endl;''')
    cpp.write_text(y)
    run(["g++","-std=c++17","-O2","-Wno-return-type","compound.cpp","-o","mission"],
        cwd=work,check=True)

def check(work,geom,input_paths):
    lib,terrain=g.solve(geom,input_paths)
    instructions=[]
    for measured in ("A","B"):
        code,hit=probe(geom,input_paths,measured)
        for strategy,mode,reply_width,retry,reply in [
            ("compact",1,1,D(".875"),D(".9375")),
            ("full_wait",0,2,D("1.875"),D("1.9375")),
            ("full_eager",0,2,D(".875"),D(".9375"))]:
            # A defined positive family: historical commit exists; late
            # physical recipient switch with typed handoff as in the parent.
            case=(2,1,0,mode,3,1,4,1,code,0,4,reply_width,retry,reply)
            instructions.append((measured,code,hit,strategy,case))
    result={}
    e,_,_,_,_=g.load(geom,input_paths)
    with (work/"diag").open("w+") as err, Popen([work/"mission"],cwd=work,
           stdin=PIPE,stdout=PIPE,stderr=err,text=True,bufsize=1) as p:
        for measured,value,hit,mode,case in instructions:
            p.stdin.write(" ".join(str(x) for x in case)+"\n");p.stdin.flush()
            while True:
                z=p.stdout.readline().split()
                if not z:
                    err.seek(0)
                    raise ValueError((case,err.read()[-700:]))
                if z[0]=="J":
                    p.stdin.write(v.journal(work,z[1:])+"\n");p.stdin.flush()
                elif z[0]=="V":
                    assert z[-3:]==["eR","gR","eR"]
                else:break
            assert tuple(map(int,z[:8]))==case[:8]
            first,side,bad=map(int,z[8:11]);prior,replay,local,observed,denied,probe_r=map(int,z[18:24])
            assert probe_r==value and first==0 and side==1 and not bad and prior==1 and not denied
            if mode=="full_eager":
                assert observed==local==-1 and replay==0
            else:
                assert observed==local==value and replay==1
            if observed not in lib:
                # Authored runtime hold at the certified initial anchor.
                result[f"{measured}/{mode}"]=dict(hold=True,scan_m=str(hit))
                continue
            # Actual callback selects route; evaluator checks the world.
            # It never passes the latent measured box to the policy.
            route=lib[observed]
            box=e.GATE_A if measured=="A" else e.GATE_B
            other=e.GATE_B if measured=="A" else e.GATE_A
            assert not any(g.exact_cross(a,b,box) for a,b in g.pairwise(route["path"]))
            assert any(g.exact_cross(a,b,other) for a,b in g.pairwise(route["path"]))
            done=case[-1]+route["travel"]
            assert done<D(200)
            result[f"{measured}/{mode}"]=dict(egress=str(done),scan_m=str(hit),
                 returned=observed,returned_at=str(case[-1]),legs=len(route["path"])-1,margin=route["margin"],
                 invalid_after_unannounced_gate_swap=True)
        p.stdin.close();assert p.wait()==0
        err.seek(0);assert not err.read()
    for measured in ("A","B"):
        assert D(result[measured+"/full_wait"]["egress"])-D(result[measured+"/compact"]["egress"])==1
    print(json.dumps(dict(mesh_triangles=terrain["mesh_triangles"],cases=result),sort_keys=True))

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--geom",type=Path,default=HERE/"geometry")
    p.add_argument("--source",type=Path,default=HERE/"source")
    p.add_argument("--paths",type=Path,default=HERE/"paths")
    a=p.parse_args()
    with tempfile.TemporaryDirectory() as d:
        w=Path(d)
        v.f.compile_native(a.geom,a.source,w)
        patch(w)
        check(w,a.geom,a.paths)
