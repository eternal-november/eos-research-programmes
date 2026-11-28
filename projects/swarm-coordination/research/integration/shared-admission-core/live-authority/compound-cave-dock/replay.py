#!/usr/bin/env python3
"""Recreate the joined held-in compound dock replay from pinned inputs."""
import argparse
from collections import Counter
from decimal import Decimal
import heapq
from hashlib import sha1
import importlib.util
from itertools import product
import json
from pathlib import Path
import re
import shutil
from subprocess import check_output, run
import sys
import tempfile

HERE=Path(__file__).resolve().parent
EGRESS="d0268cca19bda41b4efa7c3bee019b1b9c0e54c5"
INPUTS="fff6f8e20b482187cfd12d45e7b09487f0ffbb79"
CORE="687bf1250c6725992b6de696d0781d7948b4a89e"
LUT="5d53ca3aefec299168a1b49f6d2900bf51b42774"

def checked(path,expected):
    data=path.read_bytes()
    assert sha1(f"blob {len(data)}\0".encode()+data).hexdigest()==expected,path.name
    return data

def mod(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec)
    sys.modules[name]=m
    spec.loader.exec_module(m)
    return m

def local_geometry(model):
    e=mod("frozen_geometry",model/"egress.py")
    e.verify()
    e.MODELS[18]="straight3"
    mesh,fences,_=e.load_scene()
    r=e.Map(mesh,fences)
    pts=[(100,-25,6),(50,25,6),(100,100,6),(100,50,8),(100,75,8),(75,100,6)]
    eps=[(p,p) for p in pts]
    eps[3]=(pts[3],(100,Decimal("50.015625"),8))
    precopy=(101,-25,6)
    eps.append((precopy,precopy))
    assert eps[0][0][0]+Decimal(".601") < precopy[0]
    margins=[r.certificate(a,b) for a,b in eps]
    assert min(margins)>0.2
    assert all(sum((a-b)**2 for a,b in zip(u,v))>4 for u,v in
               product(pts,repeat=2) if u!=v)
    return round(min(margins),8),len(mesh)

def compile_native(model,src,work):
    checked(model/"SOURCE_INPUTS.tsv",INPUTS)
    for line in (model/"SOURCE_INPUTS.tsv").read_text().splitlines():
        name,repo,ref,source,sha=line.split("\t")
        (work/name).write_bytes(checked(src/name,sha))
    (work/"cave.dat").write_bytes(checked(src/"cave.dat",LUT))
    for x in ("extract_radio.py","extract_visible.py"):
        run([sys.executable,"-B",x],cwd=work,check=True)
    c=(work/"table.cc").read_text()
    k=c.index("bool VisibilityTable::LoadLUT()")
    (work/"load.inc").write_text(c[k:c.index("\n}",k)+2])
    shim=work/"visibility_shim.hpp"
    shim.write_text(shim.read_text().replace("struct VisibilityTable{",
             "struct VisibilityTable{\n std::string lutPath;\n bool LoadLUT();",1))
    adj={}
    for a,b,c in re.findall(r"(\d+)\s*--\s*(\d+)\s*\[label=(\d+)\]",(work/"world.dot").read_text()):
        a,b,c=map(int,(a,b,c))
        adj.setdefault(a,[]).append((b,c))
        adj.setdefault(b,[]).append((a,c))
    ids=(18,39,16,13,42,6)
    def ds(primal):
        q=[(0,primal)]
        d={primal:0}
        while q:
            t,h=heapq.heappop(q)
            if d[h]!=t:continue
            for j,c in adj[h]:
                if d.get(j,float("inf"))>t+c:
                    d[j]=t+c
                    heapq.heappush(q,(t+c,j))
        return " ".join(str(d[k]) for k in ids)
    (work/"dist6.tsv").write_text("\n".join(map(ds,ids))+"\n")
    shutil.copyfile(HERE/"compound.cpp",work/"compound.cpp")
    run(["g++","-std=c++17","-O2","-Wno-return-type","compound.cpp","-o","compound"],
        cwd=work,check=True)

def run_family(core,work):
    cases=[(shift,dup,omit,pol,a,b,cap)
           for shift,dup,omit,pol,a,b,cap in product(
               range(2),range(2),range(3),range(3),range(1,9),range(1,9),range(1,19))
           if cap>=b]
    out=check_output([work/"compound"],cwd=work,text=True,input=
        "".join(" ".join(map(str,x))+"\n" for x in cases)).splitlines()
    assert len(out)==len(cases)
    stats=Counter()
    proto={}
    for c,s in zip(cases,out):
        z=s.split()
        assert tuple(map(int,z[:7]))==c
        shift,dup,omit,pol,a,b,cap=c
        paid,side,invalid=map(int,z[7:10])
        latest=z[10]
        spent,count,transfer=map(int,z[11:14])
        grant,issued=z[14:]
        r="S" if shift else "R"
        exists=omit!=1 and (not shift or omit!=2)
        assert transfer==(shift and omit!=2)
        assert grant==(r if exists else "-")
        assert count==1+dup+exists
        assert latest==("e" if dup or not exists else "g")
        target= (("R" if latest=="e" else r) if pol==1 else grant)
        assert issued==target
        fitted=(pol!=2 or cap>b) and b+a+(pol==2)<=cap
        tx=(issued!="-" and fitted)
        # Checked on the native rows. Destination transfer length is [0,1].
        assert side==1
        assert paid==(tx and target==r)
        assert invalid==(tx and target!=r)
        assert spent==b+(1 if pol==2 and cap>b else 0)+a*int(tx)
        stats[f"policy_{pol}_raw_settled"]+=paid
        stats[f"policy_{pol}_misaddressed"]+=invalid
        if issued!="-" and issued!=grant:
            stats[f"policy_{pol}_unqualified_selection"]+=1
        # Evaluate service independently of whichever policies succeeded.
        if exists and a+b<=cap:
            stats["declared_positive_cases"]+=(pol==0)
            stats[f"policy_{pol}_qualified_positive"]+=bool(paid and issued==grant)
        if pol==0:
            auth=("accept",r)
            facts=frozenset([auth]) if not shift or transfer else frozenset()
            active=core.Use(("TX","Q"),b,cap,8)
            scope=(core.Event(2,0,uses=(active,),paid=("inspection",)),)
            options={}
            for dest in ("R","S"):
                # The required positive grant is checked from Q's callback,
                # not synthesized from the evaluator's actual recipient.
                if grant==dest:
                    options[dest]=(core.Event(7,0,need=frozenset([("accept",dest)]),
                        uses=(core.Use(("TX","Q"),a,cap,8),),paid=("older",)),)
            seen=((1,"Q",("historical","R")),)
            if exists:seen+=((5,"Q",("fresh",grant)),)
            if dup:seen+=((6,"Q",("historical","R")),)
            row=core.Row(seen,facts,scope,options)
            proto.setdefault((dup,omit,a,b,cap),[]).append((row,paid))
    checked_rows=0
    for rows in proto.values():
        cells=core.admitted([r for r,_ in rows],"Q",7,{"older":7,"inspection":7},("R","S"))
        for r,p in rows:
            actual=cells[core.view(r,"Q",7)]
            assert len(actual)==p
            checked_rows+=1
    assert stats["policy_0_misaddressed"]==0
    # Separate out-of-envelope late failure. Up to dispatch, the scoped
    # report tape is the same as the no-move case, and the old owner guard
    # rejects the report rather than credit it to the wrong recipient.
    late=check_output([work/"compound"],cwd=work,text=True,
          input="0 1 0 0 3 2 5\n2 1 0 0 3 2 5\n").splitlines()
    stable,over=map(str.split,late)
    assert stable[10:]==over[10:] # same observations and budget
    assert stable[7:10]==["1","1","0"] and over[7:10]==["0","1","1"]
    print(json.dumps(dict(native_cases=len(cases),unchanged_core_rows=checked_rows,
                          post_grant_fault_control="same tape; side pays, older unresolved",
                          **stats),sort_keys=True))

if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("--geom",type=Path,default=HERE/"geometry")
    ap.add_argument("--source",type=Path,default=HERE/"source")
    ap.add_argument("--core",type=Path,default=(HERE/"core.py" if (HERE/"core.py").is_file()
                    else HERE.parents[1]/"core.py"))
    args=ap.parse_args()
    checked(args.geom/"egress.py",EGRESS)
    checked(args.core,CORE)
    core=mod("unchanged_core",args.core)
    margin,n=local_geometry(args.geom)
    print("selected cave mesh triangles",n,"minimum certified geometric bound",margin)
    with tempfile.TemporaryDirectory() as d:
        w=Path(d)
        compile_native(args.geom,args.source,w)
        run_family(core,w)
