#!/usr/bin/env python3
"""Exercise scoped authorization at the native door writer cut."""
from pathlib import Path
from itertools import product
import argparse,importlib.util,json,subprocess as sp,tempfile
HERE=Path(__file__).resolve().parent
PIN="6b2881248f3f09b6bfe2a45161500d486773728c"
def main():
    p=argparse.ArgumentParser()
    p.add_argument("--source",type=Path,default=HERE)
    p.add_argument("--template",type=Path,default=HERE/"door_effect.cc.in")
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
        cases=[]
        for prior,r,d,tag,h,mode in product((2,5),(1,2,3),range(1,5),range(2),range(5),(0,1,2,3,5)):
            if tag==1 and d<r:
                continue
            cases.append((prior,r,d,tag,h,mode))
        packet="".join(" ".join(map(str,c))+"\n" for c in cases)
        lines=sp.check_output([wd/"door"],input=packet,text=True).splitlines()
        assert len(lines)==len(cases)
        passes={m:0 for m in (0,1,2,3,5)}
        summaries={}
        for (prior,r,d,tag,h,m),line in zip(cases,lines):
            got=[tuple(map(int,x.split())) for x in line.split(";") if x]
            assert len(got)==9
            baseline=[(t>=max(d,h) and tag==int(t>=r), t>=1) for t in range(9)]
            differences=[t for t,((close,other,*_),pair) in enumerate(zip(got,baseline)) if (close,other)!=pair]
            if not differences:
                passes[m]+=1
            if m==3:
                assert not differences
            if (prior,r,d,tag,h) in ((2,2,2,0,3),(2,2,2,1,3),(2,2,1,0,1),(5,3,1,0,0)):
                summaries[str((prior,r,d,tag,h,m))]=got
        assert passes == {0:90,1:180,2:120,3:210,5:84}
        stale=summaries[str((2,2,2,0,3,3))]
        fresh=summaries[str((2,2,2,1,3,3))]
        assert stale[:3]==fresh[:3]
        assert stale[3][0]==0 and fresh[3][0]==1
        assert max(x[-1] for x in stale[2:7])==1
        assert max(x[-1] for x in fresh[2:7])==11
        cut=summaries[str((5,3,1,0,0,3))]
        assert cut[3][0]==0 and cut[3][2]==-5
        print(json.dumps(dict(cases=len(cases),passes=passes,witnesses=summaries),sort_keys=True))
if __name__=="__main__":main()
