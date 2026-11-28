#!/usr/bin/env python3
from pathlib import Path
from contextlib import closing
import argparse
from collections import Counter,defaultdict
import hashlib
import importlib.util
import itertools
import json
import sqlite3
from subprocess import Popen,PIPE,run
import sys
import tempfile

HERE=Path(__file__).resolve().parent
PARENT=HERE if (HERE/"restart.py").is_file() else HERE.parent
old=PARENT/"restart.py"
b=old.read_bytes()
assert hashlib.sha1(f"blob {len(b)}\0".encode()+b).hexdigest()=="2f1cf373df50d8b47b5b88d441c35d77a34a431a"
s=importlib.util.spec_from_file_location("old_restart",old)
r=importlib.util.module_from_spec(s)
sys.modules["old_restart"]=r
s.loader.exec_module(r)
f=r.f

def patch(work):
    r.add_adapter(work)
    file=work/"compound.cpp"
    z=file.read_text()
    rep=r.replace
    z=rep(z,"oldBytes,sideBytes,cap,prior;","oldBytes,sideBytes,cap,prior,stateCode,late,replyCap,replyBytes;")
    z=rep(z,">>sideBytes>>cap>>prior){",">>sideBytes>>cap>>prior>>stateCode>>late>>replyCap>>replyBytes){")
    z=rep(z,'''  std::string installed="R";''','''  std::string installed="R";
  int earlySource=-1, earlySeen=-1, response=-1, replyAtQ=-1, denied=0;
  auto two=[](int code){
    return std::string(1,char(code/256))+std::string(1,char(code%256));
  };
  auto readWire=[](const std::string &bytes){
    assert(bytes.size()==1||bytes.size()==2);
    return bytes.size()==1?int((unsigned char)bytes[0]):
        256*int((unsigned char)bytes[0])+int((unsigned char)bytes[1]);
  };
  auto bucket=[](int code){return code==0?0:(code-1)/128;};''')
    z=rep(z,'''  w.b.team->at("Q")->radio.capacity=8*cap;''','''  w.b.team->at("Q")->radio.capacity=8*cap;
  w.b.team->at("S")->radio.capacity=8*replyCap;''')
    z=rep(z,'''   else{assert(v.size()==1&&(v[0]=='e'||v[0]=='g')&&(who=="R"||who=="S"));''','''   else if(now==.9375){
      assert(who=="S" && v.size()==size_t(replyBytes));
      replyAtQ=readWire(v)+(replyBytes==1);
   }
   else{assert(v.size()==1&&(v[0]=='e'||v[0]=='g')&&(who=="R"||who=="S"));''')
    z=rep(z,'''    if(v=="hu" || v=="hp" || v=="u" || v=="p"){
      assert(who=="R"&&dst=="S"&&!localR(now));
      ++providerTransfer;
      if(policy!=2)assert(journal(std::string("IMPORT S ")+v.back())=="OK");''','''
    if(who=="R" && dst=="S"){
      if(now<0){assert(earlySeen==-1 && v.size()==1);
        earlySeen=readWire(v); assert(earlySeen<=1); return;}
      assert(!localR(now));++providerTransfer;
      int code=readWire(v);
      if((policy==1||policy==3) && v.size()==1 && code>0){
        if(earlySeen<0)return;
        code+=128*earlySeen;
      }
      assert(journal("IMPORT S "+std::to_string(code))=="OK");''')
    z=rep(z,'if(v=="c"){assert(who=="P"&&dst=="R"&&now<0);',
            'if(v=="c" && who=="P" && dst=="R" && now<0){')
    z=rep(z,'if(v=="?"){assert(who=="Q");++polls;return;}',
             'if(v=="?" && who=="Q"){++polls;return;}')
    z=rep(z,'''      priorCredit+=(journal("WRITE R")=="FIRST");return;''','''      const int val=now==-70?stateCode:256;
      assert(val>=1&&val<=256);
      priorCredit+=journal("WRITE R "+std::to_string(val))[0]=='F';return;''')
    z=rep(z,'''      auto r=journal("WRITE "+physical);
      assert(r=="FIRST"||r=="REPLAY");
      paid+=r=="FIRST"; replaySeen+=r=="REPLAY";''','''      auto out=journal("WRITE "+physical+" 42");
      paid+=out[0]=='F';replaySeen+=out[0]=='R';
      response=std::stoi(out.substr(1));''')
    z=rep(z,'''  send("P","R",old,-2);assert(priorCredit==prior);
  send("P","R",old,0);''','''  send("P","R",old,-70);assert(priorCredit==prior);
  if(policy==1||policy==3){
    earlySource=bucket(std::stoi(journal("READ R")));
    send("R","S",std::string(1,char(earlySource)),-1.25);
    assert(earlySeen==earlySource);
  }
  if(late)send("P","R",old,-.5);
  assert(priorCredit==prior+late);
  send("P","R",old,0);''')
    z=rep(z,'''        const auto credit=journal("READ R");
        // One report key and one ownership handoff are prebound by
        // this model. p/u can jointly encode grant and settlement fact.
        send("R","S", policy==3?credit:"h"+credit,t);''','''        const int credit=std::stoi(journal("READ R"));
        if(policy==1 && credit!=0 && bucket(credit)!=earlySource){
          ++denied;return;
        }
        if(policy==1||policy==3){
          int code=credit==0?0:1+(credit-1)%128;
          send("R","S",std::string(1,char(code)),t);
        }else if(policy==2){
          send("R","S",std::string(1,char(credit!=0)),t);
        }else send("R","S",two(credit),t);''')
    z=rep(z,'''    assert(to.empty());to=(policy==1?r.second:"Dock");''','''    assert(to.empty());to="Dock";''')
    z=rep(z,'''  if(!to.empty())send("Q",to,archived,.875);''','''  if(!to.empty())send("Q",to,archived,.875);
  if(response>=0){
    assert(installed=="S");
    send("S","Q",replyBytes==1?std::string(1,char(response-1)):two(response),.9375);
  }''')
    z=rep(z,'''      <<w.state("Q").bytes_sent_this_epoch''','''      <<w.state("Q").bytes_sent_this_epoch''')
    z=rep(z,'''<<" "<<priorCredit<<" "<<replaySeen<<std::endl;''','''
      <<" "<<priorCredit<<" "<<replaySeen<<" "<<response<<" "<<replyAtQ<<" "<<denied<<std::endl;''')
    z=rep(z,"(t==-2&&!prior)","(t==-70&&!prior)")
    z=rep(z,'w.state("P").bytes_sent_this_epoch==size_t(oldBytes)',
            'w.state("P").bytes_sent_this_epoch==size_t(oldBytes)*(1+late)')
    file.write_text(z)
    run(["g++","-std=c++17","-O2","-Wno-return-type","compound.cpp","-o","results"],
        cwd=work,check=True)

def journal(work,command):
    if command==["RESET"]:
        for n in ("R","S"):
            with closing(sqlite3.connect(work/f"{n}.sqlite")) as db, db:
                db.execute("CREATE TABLE IF NOT EXISTS done(k TEXT PRIMARY KEY, v INT)")
                db.execute("DELETE FROM done")
        return "OK"
    op,receiver,*detail=command
    assert receiver in ("R","S")
    with closing(sqlite3.connect(work/f"{receiver}.sqlite")) as db, db:
        saved=db.execute("SELECT v FROM done WHERE k=?",(r.KEY,)).fetchone()
        if op=="READ":
            assert receiver=="R" and not detail
            return str(0 if saved is None else saved[0])
        val=int(detail[0])
        if op=="IMPORT":
            assert receiver=="S" and saved is None
            if val: db.execute("INSERT INTO done VALUES (?,?)",(r.KEY,val))
            return "OK"
        assert op=="WRITE" and val>0
        if saved is not None:return "R"+str(saved[0])
        db.execute("INSERT INTO done VALUES (?,?)",(r.KEY,val))
        return "F"+str(val)

def check(work):
    # Use only the late movement from the parent. R stays on the
    # nearer old site before t=0; the pre-window R->S cut is distinct.
    cases=[(2,dup,0,mode,3,1,cap,bool(code),code,late,rc,replybytes)
        for dup,mode,cap,rc,replybytes in itertools.product((0,1),range(4),(4,5),(4,5),(1,2))
        for code,late in ([(k,0) for k in range(257)]+[(0,1)])]
    counts=Counter()
    tape_sets=defaultdict(set)
    with (work/"diagnostics.txt").open("w+") as errors, Popen([work/"results"],
          cwd=work,stdin=PIPE,stdout=PIPE,stderr=errors,text=True,bufsize=1) as p:
        for case in cases:
            p.stdin.write(" ".join(str(int(n)) for n in case)+"\n");p.stdin.flush()
            while True:
                z=p.stdout.readline().split()
                if not z:
                    errors.seek(0)
                    raise AssertionError((case,errors.read()[-2400:]))
                if z[0]=="J":
                    p.stdin.write(journal(work,z[1:])+"\n");p.stdin.flush()
                elif z[0]=="V":tape=tuple(z[1:])
                else:break
            _,dup,_,mode,a,b,cap,prior,code,late,return_cap,replybytes=case
            assert tuple(map(int,z[:8]))==tuple(map(int,case[:8]))
            n,side,wrong=map(int,z[8:11])
            tx=int(z[12]);scope=int(z[14])
            old,replayed,local,acked,denied=map(int,z[18:23])
            assert side==1 and wrong==0 and old==prior+late
            assert denied==int(mode==1 and late)
            assert scope==1-denied
            assert tx==b+(a if scope else 0)
            attempt_ok=bool(scope and (mode!=0 or cap>=a+2))
            assert n+replayed==attempt_ok and n==int(attempt_ok and old==0)
            expected=code or (256 if late else 42)
            used=(1 if old and mode==2 else (128 if late and mode==3 else expected))
            assert local==(used if attempt_ok else -1)
            returned=attempt_ok and return_cap>=2+dup+replybytes
            assert acked==(used if returned else -1)
            counts[f"mode{mode}_exact_local"]+=int(local==expected)
            counts[f"mode{mode}_exact_return"]+=int(acked==expected)
            counts[f"mode{mode}_wrong_return"]+=int(acked!=-1 and acked!=expected)
            if not late and cap==4 and return_cap==5 and replybytes==2:
                counts[f"mode{mode}_tight_exact_return"]+=int(acked==expected)
            if mode==1 and attempt_ok and dup and return_cap==4:
                if replybytes==2:
                    assert acked==-1;counts["two_byte_return_blocked"]+=1
                else:
                    assert acked==expected;counts["one_byte_return_restored"]+=1
            if mode==1 and late:assert denied and acked==-1
            tape_sets[(dup,mode,cap,return_cap,replybytes)].add(tape)
        p.stdin.close()
        assert p.wait()==0
        errors.seek(0)
        assert all(e.strip()=="[Broker::DispatchMessages()]: Could not find endpoint Dock:7" for e in errors)
    assert all(len(t)==1 for t in tape_sets.values())
    print(json.dumps(dict(native_cases=len(cases),identical_tape_groups=len(tape_sets),**counts),sort_keys=True))

if __name__=="__main__":
    a=argparse.ArgumentParser()
    a.add_argument("--geom",type=Path,default=HERE/"geometry")
    a.add_argument("--source",type=Path,default=HERE/"source")
    x=a.parse_args()
    f.checked(x.geom/"egress.py",f.EGRESS)
    with tempfile.TemporaryDirectory() as d:
        w=Path(d)
        f.compile_native(x.geom,x.source,w)
        patch(w)
        check(w)
