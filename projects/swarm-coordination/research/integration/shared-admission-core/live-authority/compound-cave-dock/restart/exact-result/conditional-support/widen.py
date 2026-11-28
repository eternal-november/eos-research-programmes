#!/usr/bin/env python3
"""Native pressure test of the late result codebook under admitted edit support."""
from pathlib import Path
import argparse
from collections import Counter
import hashlib
import importlib.util
import json
from subprocess import Popen, PIPE, run
import sys
import tempfile

HERE=Path(__file__).resolve().parent
PARENT=HERE if (HERE/"result_transfer.py").is_file() else HERE.parent
def load_checked_module():
    path=PARENT/"result_transfer.py"
    src=path.read_bytes()
    assert hashlib.sha1(f"blob {len(src)}\0".encode()+src).hexdigest()==VALUE_PIN
    s=importlib.util.spec_from_file_location("exact_dock_return",path)
    o=importlib.util.module_from_spec(s)
    sys.modules["exact_dock_return"]=o
    s.loader.exec_module(o)
    return o
VALUE_PIN="3be5d2cc1f31a112a28af1a0d73d725d71718661"

def patch(v,work):
    v.patch(work)
    cpp=work/"compound.cpp"
    z=cpp.read_text()
    k=v.r.replace
    z=k(z,'''      if((policy==1||policy==3) && v.size()==1 && code>0){''','''
      if((policy==4||policy==5) && v.size()==1){
        assert(earlySeen>=0);
        const int excluded=earlySeen==0?255:1;
        if(code>=excluded)++code;
      }
      if((policy==1||policy==3) && v.size()==1 && code>0){''')
    z=k(z,'''  if(policy==1||policy==3){
    earlySource=bucket''','''  if(policy==1||policy==3||policy==4||policy==5){
    earlySource=bucket''')
    z=k(z,'''      const int val=now==-70?stateCode:256;''',
        '''      const int val=now==-70?stateCode:late;''')
    z=k(z,'''assert(priorCredit==prior+late);''','''assert(priorCredit==prior+(late>0));''')
    z=k(z,'''bytes_sent_this_epoch==size_t(oldBytes)*(1+late)''',
        '''bytes_sent_this_epoch==size_t(oldBytes)*(1+(late>0))''')
    z=k(z,'''        if(policy==1||policy==3){
          int code=credit==0?0:1+(credit-1)%128;''','''
        if(policy==4||policy==5){
          const int excluded=earlySource==0?255:1;
          if(credit==excluded && policy==4){++denied;return;}
          const int code=credit>excluded?credit-1:credit;
          send("R","S",std::string(1,char(code)),t);
        }else if(policy==1||policy==3){
          int code=credit==0?0:1+(credit-1)%128;''')
    cpp.write_text(z)
    run(["g++","-std=c++17","-O2","-Wno-return-type","compound.cpp","-o","widen"],cwd=work,
        check=True)

def check(v,work):
    scenarios=[(2,1,0,mode,3,1,4,bool(code),code,late,4,1)
               for mode in (1,4,5)
               for code,late in [(k,0) for k in range(257)]+[(0,v) for v in range(1,257)]]
    stats=Counter()
    late_witness={}
    tapes=set()
    with (work/"errs.txt").open("w+") as err, Popen([work/"widen"],cwd=work,
            stdin=PIPE,stdout=PIPE,stderr=err,text=True,bufsize=1) as p:
        for case in scenarios:
            p.stdin.write(" ".join(str(int(k)) for k in case)+"\n");p.stdin.flush()
            while True:
                row=p.stdout.readline().split()
                if not row:
                    err.seek(0)
                    raise AssertionError((case,err.read()[-500:]))
                if row[0]=="J":
                    p.stdin.write(v.journal(work,row[1:])+"\n");p.stdin.flush()
                elif row[0]=="V":
                    tapes.add(tuple(row[1:]))
                else:break
            assert tuple(map(int,row[:8]))==tuple(map(int,case[:8]))
            mode,code,late=case[3],case[8],case[9]
            new,side,wrong=map(int,row[8:11])
            old,_,local,client,denied=map(int,row[18:23])
            assert not wrong and side and old+new==1
            expected=(late or code or 42)
            gate=(mode==1 and late>=129) or (mode==4 and late==255)
            assert denied==gate
            want=(-1 if gate else 256 if mode==5 and late==255 else expected)
            assert client==local==want
            stats[f"mode{mode}_exact"]+=(client==expected)
            stats[f"mode{mode}_wrong"]+=(client!=-1 and client!=expected)
            if late in (255,256):
                late_witness[f"mode{mode}_late{expected}"]=client
        p.stdin.close();assert p.wait()==0
        err.seek(0)
        assert len(err.read().splitlines())==129
    assert len(tapes)==1
    print(json.dumps(dict(native_cases=len(scenarios),**stats,witness=late_witness),sort_keys=True))

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--geom",type=Path,default=HERE/"geometry")
    p.add_argument("--source",type=Path,default=HERE/"source")
    a=p.parse_args()
    v=load_checked_module()
    with tempfile.TemporaryDirectory() as d:
        work=Path(d)
        v.f.compile_native(a.geom,a.source,work)
        patch(v,work)
        check(v,work)
