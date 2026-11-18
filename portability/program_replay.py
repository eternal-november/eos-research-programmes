"""Reproduce portability evidence on immutable Git snapshots, without moving a working branch."""
import argparse
import ast
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from hashlib import sha256
import json
import os
import re
from urllib.parse import unquote
from pathlib import Path
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory, gettempdir
from threading import Lock

HERE=Path(__file__).resolve().parent
SOURCE="theories-and-designs/byzantine-control"
PORT=SOURCE+"/portability"
HISTORICAL="fb85a7606f45e52d0cd48e023ab9776dd526640c"
PROPOSAL="a0007e8904355ec32c27e6dc21905bdfbc101d22"
EXCEPTIONS={"framing_probe":"framing","pulse_model":"pulse","threshold_incidence_model":"threshold_incidence",
            "threshold_program_model":"threshold_program","threshold_publication_model":"threshold_publication",
            "vector_refresh_model":"vector_refresh","fixed_island_model":"fixed_island"}
TOOLS={"program_replay.py","freeze_portability.py"}
CURRENT={"a80_prefix_mission.py","a80_g3.py","a80_handoff_trip.py","a80_candidate_custody.py",
         "b_handoff.py","b_host_flow.py","b_reference_return.py","regional_assembly.py",
         "frame_pacing.py","normal_response_transport.py","quiet_window.py","premise_audit.py",
         "world_channel.py","spatial_coverage.py","receiver_lease.py","sender_eligibility.py",
         "current_publication_comparison.py","baseline_adapter.py","projected_work_flow.py",
         "b_cut_induction.py","b_lead_installation.py","phase_ten_history.py"}
PRINT_LOCK=Lock()


def require(ok,reason):
    if not ok:raise ValueError(reason)


def git(repo,*args):
    return subprocess.check_output(["git","-C",str(repo),*args],stderr=subprocess.PIPE)


def rev(repo,name):
    require(not name.startswith("-"),"A revision cannot be a Git option")
    commit=git(repo,"rev-parse","--verify",name+"^{commit}").decode().strip()
    require(len(commit)==40 and all(ch in "0123456789abcdef" for ch in commit),"Unresolved commit")
    return commit


def files(repo,revision):
    data=git(repo,"ls-tree","-z",revision+":"+PORT)
    entries={}
    for x in data.split(b"\0"):
        if x:
            meta,path=x.split(b"\t",1)
            kind=meta.split()[1]
            if kind==b"blob":entries[path.decode()]=meta.split()[2].decode()
    return entries


def texts(repo,entries):
    # One cat-file process avoids a Git process per blob and preserves exact bytes.
    selected={n:o for n,o in entries.items() if n.endswith((".py",".lean"))}
    run=subprocess.run(["git","-C",str(repo),"cat-file","--batch"],
            input="".join(o+"\n" for o in selected.values()).encode(),capture_output=True,check=True)
    data=run.stdout;at=0
    out={}
    for name,oid in selected.items():
        end=data.index(b"\n",at)
        lo=end+1
        got,kind,count=data[at:end].split()
        require(got.decode()==oid and kind==b"blob","Git returned a different source")
        hi=lo+int(count)
        out[name]=data[lo:hi].decode("utf-8-sig")
        require(data[hi:hi+1]==b"\n","Malformed cat-file result")
        at=hi+1
    require(at==len(data),"Unexpected Git output")
    return out


@dataclass(frozen=True)
class Probe:
    name:str
    revision:str
    role:str
    script:str
    args:tuple
    receipt:str|None


def is_main(tree):
    for n in tree.body:
        if isinstance(n,ast.If) and isinstance(n.test,ast.Compare) and isinstance(n.test.left,ast.Name):
            if n.test.left.id=="__name__" and any(isinstance(c,ast.Constant) and c.value=="__main__"
                                                   for c in n.test.comparators):
                return True
    return False


def plan(repo,point):
    entries=files(repo,point)
    src=texts(repo,entries)
    probes=[]
    accounted=set()
    for file,code in sorted(src.items()):
        if not file.endswith(".py") or file in TOOLS:continue
        tree=ast.parse(code,filename=file)
        if not is_main(tree):continue
        strings={n.value for n in ast.walk(tree) if isinstance(n,ast.Constant) and isinstance(n.value,str)}
        stem=file[:-3]
        record=EXCEPTIONS.get(stem,stem)+"_results.json"
        if record not in entries:record=None
        if record:accounted.add(record)
        # Historical verification uses the exact repackaged evidence revision.
        # For result-free probes use their last changed represented script.
        historical=git(repo,"rev-list","-1",point,"--",PORT+"/"+(record or file)).decode().strip()
        require(len(historical)==40,"Missing history for "+file)
        def options(tokens):
            flags=("--check",) if "--check" in tokens else ()
            return flags+(("--research-repo","{research}") if "--research-repo" in tokens else ())
        old=git(repo,"show",historical+":"+PORT+"/"+file).decode("utf-8-sig")
        old_tokens={n.value for n in ast.walk(ast.parse(old)) if isinstance(n,ast.Constant) and isinstance(n.value,str)}
        probes.append(Probe("bound/"+stem,historical,"bound source",file,options(old_tokens),record))
        if file in CURRENT and historical!=point:
            probes.append(Probe("current/"+stem,point,"present application",file,options(strings),record))
    # An unclassified result must never quietly disappear from reproduction.
    records={name for name in entries if name.endswith("_results.json")}
    require(records==accounted,"Unclassified or multiply named receipts: "+str(sorted(records^accounted)))
    probes.append(Probe("current/lean",point,"current checked declarations","",(),None))
    probes.append(Probe("baseline/aggregate",HISTORICAL,"archived baseline","../local-control/verify.py",
                        ("--check","--lean","{lean}"),"../local-control/verification.json"))
    require(len({x.name for x in probes})==len(probes),"Repeated scientific check name")
    return probes


def lean_build(repo,point,exe,env):
    current=files(repo,point)
    src={k:v for k,v in texts(repo,current).items() if k.endswith(".lean")}
    remaining=set(src);built=set();messages=[]
    with TemporaryDirectory(prefix="rp-lean-") as dst:
        require(Path(dst).resolve().parent==Path(gettempdir()).resolve() and Path(dst).name.startswith("rp-lean-"),
                "Unexpected temporary Lean directory")
        e=dict(env,LEAN_PATH=dst)
        while remaining:
            for name in sorted(remaining):
                imported={s.split()[1]+".lean" for s in src[name].splitlines()
                          if s.startswith("import ") and len(s.split())>=2}
                if imported&set(src)<=built:break
            else:raise ValueError("Local Lean import cycle")
            cmd=[str(exe),"-o",str(Path(dst)/(Path(name).stem+".olean")),name]
            out=subprocess.run(cmd,cwd=repo/PORT,env=e,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            require(out.returncode==0 and b"sorryAx" not in out.stdout and b"declaration uses 'sorry'" not in out.stdout,
                    "Lean certification failed in "+name+"\n"+out.stdout[-4000:].decode(errors="replace"))
            messages.append(name.encode()+b"\n"+out.stdout.replace(b"\r\n",b"\n"))
            built.add(name);remaining.remove(name)
    return b"\n".join(messages)


def tree_binding(repo,point):
    return dict(commit=point,root_tree=git(repo,"rev-parse",point+"^{tree}").decode().strip(),
                programme_tree=git(repo,"rev-parse",point+":"+PORT).decode().strip(),
                contract_blob=git(repo,"rev-parse",point+":"+PORT+"/CONTRACT.md").decode().strip())


def worker(source,sandbox,cases,lean,research):
    checkout=sandbox/"eos-garden"
    subprocess.run(["git","-c","core.autocrlf=false","clone","--shared","--no-checkout","--quiet",
                    str(source),str(checkout)],check=True)
    env=dict(os.environ)
    env.pop("PYTHONOPTIMIZE",None)
    env["PYTHONDONTWRITEBYTECODE"]="1"
    env["PYTHONIOENCODING"]="utf-8"
    current=None
    records=[]
    for c in cases:
        if current!=c.revision:
            git(checkout,"-c","core.autocrlf=false","switch","--detach","--quiet",c.revision)
            current=c.revision
        status=git(checkout,"status","--porcelain","--untracked-files=all")
        require(not status.strip(),"Earlier check changed the isolated source: "+status.decode(errors="replace")[:300])
        with PRINT_LOCK:print("Checking",c.name,c.revision[:12],flush=True)
        record=dict(name=c.name,revision=c.revision,role=c.role)
        try:
            if c.name=="current/lean":
                out=lean_build(checkout,current,lean,env)
            else:
                assert c.script
                cmd=[sys.executable,"-B",str(checkout/PORT/c.script)]
                cmd.extend((str(research) if a=="{research}" else str(lean) if a=="{lean}" else a) for a in c.args)
                proc=subprocess.run(cmd,cwd=checkout/PORT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
                out=proc.stdout.replace(b"\r\n",b"\n")
                require(proc.returncode==0,f"Exit {proc.returncode}\n"+out[-5000:].decode("utf-8","replace"))
            after=git(checkout,"status","--porcelain","--untracked-files=all")
            require(not after.strip(),"Checker mutated the source: "+after.decode(errors="replace")[:350])
            record["status"]="passed"
            record["stdout_sha256"]=sha256(out).hexdigest()
            if c.receipt:
                raw=(checkout/PORT/c.receipt).read_bytes().replace(b"\r\n",b"\n")
                record["receipt"]=c.receipt
                record["receipt_sha256_lf"]=sha256(raw).hexdigest()
        except (ValueError,OSError,subprocess.SubprocessError) as exc:
            record.update(status="failed",error=str(exc))
            with PRINT_LOCK:print("FAILED",c.name,str(exc)[-700:],flush=True)
        records.append(record)
    return records



def research_sources(repo,point,research):
    """Bind the actual external files cited by the frozen programme, including trees."""
    entries=files(repo,point)
    pattern=re.compile(r"https://github\.com/eternal-november/eos-research-programmes/(?:blob|tree)/([a-f0-9]{7,40})/([^\s)#]+)")
    references={}
    for name in sorted(entries):
        if name.endswith(".md"):
            note=git(repo,"show",point+":"+PORT+"/"+name).decode("utf-8-sig")
            for tag,path in pattern.findall(note):
                path=unquote(path)
                references.setdefault((tag,path),[]).append(name)
    resolved={}
    for tag,path in sorted(references):
        commit=rev(research,tag)
        key=commit+":"+path
        oid=git(research,"rev-parse","--verify",key).decode().strip()
        require(git(research,"cat-file","-t",oid).strip() in (b"blob",b"tree"),"Unknown external source kind")
        row=resolved.setdefault(key,dict(git_object=oid,consumers=[]))
        row["consumers"]=sorted(set(row["consumers"]+references[(tag,path)]))
    return resolved


def main():
    require(sys.version_info[:2]==(3,12) and not sys.flags.optimize,"Run unoptimized Python 3.12")
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--at",required=True,help="Immutable scientific source revision or local Git reference")
    ap.add_argument("--list",action="store_true")
    ap.add_argument("--only",action="append",help="Exact check name; repeat for a bounded partial run")
    ap.add_argument("--jobs",type=int,default=2)
    ap.add_argument("--lean",type=Path)
    ap.add_argument("--research-repo",type=Path)
    ap.add_argument("--output",type=Path,help="Write a new run record, including failures, to this path")
    args=ap.parse_args()
    source=Path(git(HERE,"rev-parse","--show-toplevel").decode().strip())
    point=rev(source,args.at)
    require(subprocess.run(["git","-C",str(source),"merge-base","--is-ancestor",PROPOSAL,point]).returncode==0,
            "Requested programme revision does not descend from its contract")
    cases=plan(source,point)
    if args.only:
        ids=set(args.only)
        require(ids<={x.name for x in cases},"Unknown requested check(s): "+str(ids-{x.name for x in cases}))
        cases=[x for x in cases if x.name in ids]
    if args.list:
        for c in cases:print(c.name,c.revision,c.role,c.receipt or "-")
        return
    require(1<=args.jobs<=8,"Choose 1 to 8 isolated checkers")
    path=shutil.which("lean") if not args.lean else args.lean
    require(path is not None,"Supply --lean")
    lean=Path(path).resolve()
    version=subprocess.check_output([str(lean),"--version"],text=True).strip()
    require("version 4.33.0," in version,"Lean 4.33.0 required")
    research=args.research_repo.resolve() if args.research_repo else None
    if any("{research}" in c.args for c in cases):
        require(research is not None and (research/".git").exists(),"Supply the contextual-composition Git repository")
    rows=[]
    with TemporaryDirectory(prefix="byzantine-replay-") as tmp:
        require(Path(tmp).resolve().parent==Path(gettempdir()).resolve() and Path(tmp).name.startswith("byzantine-replay-"),
                "Unexpected temporary replay directory")
        # Only the temporary clones change HEAD. Production/user worktrees
        # and their indices never participate in a historical checkout.
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            tasks=[]
            for i in range(min(args.jobs,len(cases))):
                loc=Path(tmp)/str(i)
                loc.mkdir()
                tasks.append(pool.submit(worker,source,loc,cases[i::args.jobs],lean,research))
            for t in tasks:rows.extend(t.result())
    rows.sort(key=lambda x:x["name"])
    full=not args.only
    evidence=dict(binding=tree_binding(source,point),proposal=PROPOSAL,historical_baseline=HISTORICAL,
                  python=".".join(map(str,sys.version_info[:3])),lean=version,all_listed_checks_selected=full,
                  runner_sha256_lf=sha256(Path(__file__).read_bytes().replace(b"\r\n",b"\n")).hexdigest(),
                  referenced_research=research_sources(source,point,research) if research else {},
                  requested_checks=len(rows),passed=sum(r["status"]=="passed" for r in rows),checks=rows,
                  scientific_scope="Historical checks apply at their named revision. Programme completion requires a separate verified positive-family and held-out audit.")
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        with args.output.open("x",encoding="utf8",newline="\n") as f:
            json.dump(evidence,f,sort_keys=True,indent=2);f.write("\n")
    print(f"{evidence['passed']}/{len(rows)} checks passed for {point}; full selection={full}.")
    if evidence["passed"]!=len(rows):raise SystemExit(1)


if __name__=="__main__":
    main()
