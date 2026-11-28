#!/usr/bin/env python3
"""Cold receiver journal and native late binding, on the same cave fixture."""
import argparse
from contextlib import closing
from collections import Counter
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path
import sqlite3
from subprocess import Popen, PIPE, run
import sys
import tempfile

HERE=Path(__file__).resolve().parent
PARENT=HERE if (HERE/"compound.cpp").is_file() else HERE.parent
PARENT_PINS={
    "compound.cpp":"b7ee8ea3aed3dcaa9c78e26253924c6f75e5edd0",
    "replay.py":"2cbeaf8222e0e39a66cc107d3b0cc40d2ea55b25",
}
for name, pin in PARENT_PINS.items():
    x=(PARENT/name).read_bytes()
    assert hashlib.sha1(f"blob {len(x)}\0".encode()+x).hexdigest()==pin
spec=importlib.util.spec_from_file_location("held_in_family",PARENT/"replay.py")
f=importlib.util.module_from_spec(spec)
sys.modules["held_in_family"]=f
spec.loader.exec_module(f)

def replace(x,a,b):
    assert x.count(a)==1,a
    return x.replace(a,b)

def add_adapter(work):
    # Transport and report handlers are fixture code, not native broker.
    h=work/"staged_replay.inc"
    z=h.read_text()
    z=replace(z," bool Request(const std::string&,subt::msgs::Datagram msg){",
      """ std::string actualClient;
 bool Request(const std::string& client,subt::msgs::Datagram msg){
  actualClient=client;""")
    h.write_text(z)
    c=work/"compound.cpp"
    z=c.read_text()
    z=replace(z,"oldBytes,sideBytes,cap;\n while","oldBytes,sideBytes,cap,prior;\n while")
    z=replace(z,">>sideBytes>>cap){",">>sideBytes>>cap>>prior){")
    z=replace(z,"  World w(32);","""  auto journal=[](const std::string &op){
    std::cout<<"J "<<op<<std::endl;
    std::string out;assert(bool(std::cin>>out));return out;
  };
  assert(journal("RESET")=="OK");
  World w(32);
  w.b.endpoints["Dock:7"].push_back({"R"});
  std::string installed="R";""")
    z=replace(z,"    if(t<0)return fixed[1];",
     "    if(t<0)return (t==-2&&!prior)?fixed[3]:fixed[1];")
    z=replace(z,"  int paid=0,sidePaid=0,invalid=0,copySeen=0,polls=0,providerTransfer=0,primaryContact=0;",
    "  int paid=0,sidePaid=0,invalid=0,copySeen=0,polls=0,providerTransfer=0,primaryContact=0,priorCredit=0,replaySeen=0;")
    z=replace(z,
     '''    if(v=="h"){assert(who=="R"&&dst=="S"&&!localR(now));++providerTransfer;return;}
    assert(v==old);
    // Endpoints can deliver a packet even when their application is not
    // authorized to settle the outstanding named duty at consumption.
    const bool allowed=dst=="R"?localR(now):(providerTransfer==1 && now>=.375);
    if(who=="Q" && allowed) ++paid;
    else ++invalid;''',
     '''    if(v=="hu" || v=="hp" || v=="u" || v=="p"){
      assert(who=="R"&&dst=="S"&&!localR(now));
      ++providerTransfer;
      if(policy!=2)assert(journal(std::string("IMPORT S ")+v.back())=="OK");
      // Explicit local capability: this fixture co-locates the directory
      // with the transfer callback and installs the singleton before dispatch.
      w.b.endpoints["Dock:7"]={{"S"}};installed="S";
      return;
    }
    assert(v==old);
    const auto& physical=w.b.node.actualClient;
    if(now<0){assert(who=="P"&&physical=="R");
      priorCredit+=(journal("WRITE R")=="FIRST");return;}
    const bool allowed=physical=="R"?localR(now):(physical=="S" && providerTransfer==1);
    if(who=="Q" && allowed){
      auto r=journal("WRITE "+physical);
      assert(r=="FIRST"||r=="REPLAY");
      paid+=r=="FIRST"; replaySeen+=r=="REPLAY";
    }else ++invalid;''')
    z=replace(z,'''  w.app.callbacks["S:7"]=finish;''','''  w.app.callbacks["S:7"]=finish;
  w.app.callbacks["Dock:7"]=finish;''')
    z=replace(z,'''  send("P","R","c",-100);assert(primaryContact==1);
  send("P","R",old,0);assert(paid==0&&invalid==0);''',
     '''  send("P","R","c",-100);assert(primaryContact==1);
  send("P","R",old,-2);assert(priorCredit==prior);
  send("P","R",old,0);assert(paid==0&&invalid==0);''')
    z=replace(z,'''  if(!localR(.375)&&omit!=2)send("R","S","h",.375);
  assert(providerTransfer==(shift==1 && omit!=2));
  if(policy==2){send("Q","R","?",.5);assert(polls==(size_t(sideBytes)+1<=size_t(cap)));}''',
    '''  auto moveAuthority=[&](double t){
    if(!localR(t)&&installed=="R"){
      w.b.endpoints.erase("Dock:7");installed="-";
      // Scope is closed before exporting the local journal fact; a
      // later R data packet cannot add a new credit with this pose.
      if(omit!=2){
        const auto credit=journal("READ R");
        // One report key and one ownership handoff are prebound by
        // this model. p/u can jointly encode grant and settlement fact.
        send("R","S", policy==3?credit:"h"+credit,t);
      }
    }
  };
  moveAuthority(.375);
  assert(providerTransfer==(shift==1 && omit!=2));''')
    z=replace(z,'''  if(duplicate)send("R","Q","e",.75);
  std::string to;
  if(policy==1){if(!receipts.empty())to=receipts.back().second;}
  else for(const auto& r:receipts)if(r.first=='g'){
    assert(to.empty());to=r.second;
  }
  if(!to.empty())send("Q",to,archived,.875);''',
    '''  if(duplicate)send("R","Q","e",.75);
  moveAuthority(.8125);
  std::string to;
  for(const auto& r:receipts)if(r.first=='g'){
    assert(to.empty());to=(policy==1?r.second:"Dock");
  }
  std::cout<<"V "<<w.state("Q").bytes_sent_this_epoch;
  for(const auto& r:receipts)std::cout<<" "<<r.first<<r.second;
  std::cout<<std::endl;
  if(!to.empty())send("Q",to,archived,.875);''')
    z=replace(z,'''      <<" "<<cap<<" "<<paid''','''      <<" "<<cap<<" "<<prior<<" "<<paid''')
    z=replace(z,'''<<(to.empty()?'-':to[0])<<"\\n";''',
     '''<<(to.empty()?'-':to[0])<<" "<<installed<<" "<<priorCredit<<" "<<replaySeen<<std::endl;''')
    c.write_text(z)
    run(["g++","-std=c++17","-O2","-Wno-return-type","compound.cpp","-o","restart"],
        cwd=work,check=True)

KEY="old-inspection:42"
def station(work,command):
    # Each operation reopens its named durable file; receiver restart
    # is a cold reconstruction, not a power-loss test. R and S do not
    # have shared reads or access to each other's journal.
    if command==["RESET"]:
        for n in ("R","S"):
            with closing(sqlite3.connect(work/f"{n}.sqlite")) as db, db:
                db.execute("CREATE TABLE IF NOT EXISTS credit(k TEXT PRIMARY KEY)")
                db.execute("DELETE FROM credit")
        return "OK"
    op,receiver,*detail=command
    assert receiver in ("R","S")
    with closing(sqlite3.connect(work/f"{receiver}.sqlite")) as db, db:
        if op=="READ":
            assert receiver=="R" and not detail
            return "p" if db.execute("SELECT k FROM credit WHERE k=?",(KEY,)).fetchone() else "u"
        if op=="IMPORT":
            assert receiver=="S" and detail in (["p"],["u"])
            if detail==["p"]:
                db.execute("INSERT OR IGNORE INTO credit VALUES (?)",(KEY,))
            return "OK"
        assert op=="WRITE" and not detail
        n=db.execute("INSERT OR IGNORE INTO credit VALUES (?)",(KEY,)).rowcount
        return "FIRST" if n==1 else "REPLAY"

def check(work):
    family=[x for x in product(range(3),range(2),range(3),range(4),range(1,5),
             range(1,5),range(1,10),range(2)) if x[6]>=x[5]]
    stat=Counter()
    twins={}
    with (work/"diagnostics.txt").open("w+") as diagnostics, Popen([work/"restart"],
          cwd=work,stdin=PIPE,stdout=PIPE,stderr=diagnostics,text=True,bufsize=1) as p:
        for x in family:
            p.stdin.write(" ".join(map(str,x))+"\n");p.stdin.flush()
            while True:
                z=p.stdout.readline().split()
                assert z, x
                if z[0]=="J":
                    p.stdin.write(station(work,z[1:])+"\n");p.stdin.flush()
                elif z[0]=="V":
                    tape=tuple(z[1:])
                else:
                    break
            assert tuple(map(int,z[:8]))==x
            shift,dup,omit,policy,a,b,c,prior=x
            new,side,wrong=map(int,z[8:11])
            sent=int(z[12])
            transfer=int(z[14])
            grant,issued,installed=z[15:18]
            old,replays=map(int,z[18:20])
            assert old==prior and side==1 and transfer==int(shift!=0 and omit!=2)
            assert installed==("S" if transfer else "-" if shift else "R")
            assert grant==("-" if omit==1 or shift==1 and omit==2 else
                           "S" if shift==1 else "R")
            assert issued==("-" if grant=="-" else grant if policy==1 else "D")
            expected_attempt=(issued!="-" and installed!="-" and a+b<=c)
            if policy==1 and grant=="R" and shift==2:
                # Unicast to the retired physical R can still spend airtime.
                expected_attempt=(a+b<=c)
                assert wrong==expected_attempt
            else:
                assert wrong==0
            assert sent==b+a*expected_attempt
            if policy!=1 and installed=="S":
                receiverFits=c>=a+(1 if policy==3 else 2)
            elif policy==1 and grant=="S":
                receiverFits=c>=a+2
            else:
                receiverFits=True
            got=bool(expected_attempt and not wrong and receiverFits)
            if expected_attempt and not wrong and not receiverFits:
                stat[f"p{policy}_receiver_budget_reject"]+=1
            if got:
                assert new==int(not old or (policy==2 and installed=="S")), (x,z,tape)
                assert replays==1-new
            else:
                assert new==replays==0
            stat[f"p{policy}_exactly_once"]+=(old+new==1)
            stat[f"p{policy}_duplicate_effect"]+=(old+new>1)
            stat[f"p{policy}_misaddress"]+=wrong
            positive=omit==0 and a+b<=c
            if positive:
                stat[f"p{policy}_positive_success"]+=(old+new==1)
                stat[f"p{policy}_positive_with_reconciliation"]+=bool(got and old+new==1)
            k=x[:-1]
            if k in twins:
                assert twins.pop(k)==tape
            else:
                twins[k]=tape
        p.stdin.close()
        assert p.wait()==0
        diagnostics.seek(0)
        errors=diagnostics.read().splitlines()
        assert all(x=="[Broker::DispatchMessages()]: Could not find endpoint Dock:7" for x in errors)
        stat["expected_no_binding_diagnostics"]=len(errors)
    assert not twins and stat["p0_duplicate_effect"]==stat["p3_duplicate_effect"]==0
    assert stat["p0_receiver_budget_reject"]>0 and stat["p3_receiver_budget_reject"]==0
    assert stat["p3_positive_success"]==stat["p3_positive_with_reconciliation"]==960
    print(json.dumps(dict(runs=len(family),matched_frozen_tapes=len(family)//2,**stat),sort_keys=True))

def main():
    a=argparse.ArgumentParser()
    a.add_argument("--geom",type=Path,default=HERE/"geometry")
    a.add_argument("--source",type=Path,default=HERE/"source")
    x=a.parse_args()
    f.checked(x.geom/"egress.py",f.EGRESS)
    with tempfile.TemporaryDirectory() as d:
        w=Path(d)
        f.compile_native(x.geom,x.source,w)
        add_adapter(w)
        check(w)
if __name__=="__main__": main()
