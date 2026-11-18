"""Fingerprint or verify a proposed immutable transfer reference; no target selection."""
import argparse
import ast
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess

import program_replay as replay

HERE=Path(__file__).resolve().parent
PORT=replay.PORT
MANIFEST=PORT+"/RP6-FREEZE.json"
CORE_NOTES={
    "CONTRACT.md","PROGRAM.md","CHALLENGE.md","CORE.md","PREFIX-MISSION.md","RECURRENT-SUPPORT.md",
    "SOURCE-CLASS.md","CLASS-ADMISSION.md","EXPORT-DEPENDENCIES.md","CONSTRUCTORS.md","DONOR-WINDOW.md",
    "FLOW-COMPOSITION.md","PROJECTED-WORK-FLOW.md","QUIET-WINDOW.md","WATCHDOG-PROGRESS.md",
    "HISTORICAL-REPAIR-LIFT.md","PACED-HISTORY-TRANSFER.md","LOCAL-PREDICATE.md",
    "OPEN-PROTOCOL-FORMULATION.md","SERVICE-FIBRES.md","TRACKER-ENVELOPE.md","INTERZONE-WORK.md",
    "FRAMINGS.md","OPERATING-FLOW-JOIN.md","TRANSFER-INTERFACE.md","REPEATED-PROOF-BURDEN.md",
}
RC=re.compile(rb"(?<![A-Za-z0-9_])[0-9a-f]{7,40}(?![A-Za-z0-9_])")


def check(test,message):
    if not test:raise ValueError(message)


def historical(repo,at,probes):
    # A Git tree binds every byte in its snapshot, including non-code
    # data. Historical checker inputs can be on separate worker branches.
    # Find the local commit names in source text and close over their
    # actual checker implementations, by blob identity rather than filename.
    found={at,replay.HISTORICAL,replay.PROPOSAL,*(case.revision for case in probes)}
    pending=list(found)
    blob_seen=set()
    token_cache={}
    while pending:
        sha=pending.pop()
        listing=replay.git(repo,"ls-tree","-rz",sha,"--",replay.SOURCE)
        blobs=[]
        for row in listing.split(b"\0"):
            if not row:continue
            meta,name=row.split(b"\t",1)
            if meta.split()[1]!=b"blob":continue
            # Exact historical commits cited in current scientific prose
            # are also part of the reference; code closure is transitive.
            if not(name.endswith((b".py",b".json")) or sha==at and name.endswith((b".md",b".lean"))):
                continue
            oid=meta.split()[2]
            if oid not in blob_seen:
                blobs.append(oid)
                blob_seen.add(oid)
        if not blobs:continue
        proc=subprocess.run(["git","-C",str(repo),"cat-file","--batch"],
                input=b"\n".join(blobs)+b"\n",capture_output=True,check=True)
        offset=0;data=proc.stdout;tokens=set()
        for expected in blobs:
            header=data.index(b"\n",offset)
            oid,kind,size=data[offset:header].split()
            check(oid==expected and kind==b"blob","Bad Git response")
            end=header+1+int(size)
            tokens.update(x.decode() for x in RC.findall(data[header+1:end]) if any(ch in b"abcdef" for ch in x))
            offset=end+1
        unknown=sorted(t for t in tokens if t not in token_cache)
        if unknown:
            proc=subprocess.run(["git","-C",str(repo),"cat-file","--batch-check=%(objectname) %(objecttype)"],
                  input="".join(t+"^{commit}\n" for t in unknown).encode(),capture_output=True,check=True)
            rows=proc.stdout.decode().splitlines()
            check(len(rows)==len(unknown),"Unexpected reference lookup")
            for t,row in zip(unknown,rows):
                fields=row.split()
                token_cache[t]=fields[0] if len(fields)==2 and fields[1]=="commit" else None
        for t in tokens:
            commit=token_cache[t]
            if commit is not None and commit not in found:
                found.add(commit);pending.append(commit)
    return {k:replay.git(repo,"rev-parse",k+"^{tree}").decode().strip() for k in sorted(found)}


def immutable_files(repo,point):
    rows=replay.git(repo,"ls-tree","-rz",point,"--",replay.SOURCE).split(b"\0")
    fixed={}
    for row in rows:
        if not row:continue
        meta,name=row.split(b"\t",1)
        file=name.decode()
        mode,kind,oid=meta.decode().split()
        if file not in (PORT+"/TODO.md",MANIFEST):
            fixed[file]={"mode":mode,"kind":kind,"object":oid}
    return fixed


def executable_manuscripts(repo,revision,script):
    """Read the import table at the code revision whose checker consumes it."""
    if script=="local_predicate.py":
        names={"IMPORT_PREFIX","IMPORTS"}
    elif script=="service_fibres.py":
        names={"CC","CC_PREFIX","THEOREMS"}
    else:
        raise ValueError("External research reader needs a reviewed dependency inventory: "+script)
    code=replay.git(repo,"show",revision+":"+PORT+"/"+script).decode("utf-8-sig")
    fields={}
    for node in ast.parse(code).body:
        if isinstance(node,ast.Assign) and len(node.targets)==1 and isinstance(node.targets[0],ast.Name):
            key=node.targets[0].id
            if key in names:
                check(key not in fields,"Duplicate import declaration in "+script+": "+key)
                fields[key]=ast.literal_eval(node.value)
    check(set(fields)==names,"Incomplete external import inventory in "+script)
    if script=="local_predicate.py":
        return [(commit,fields["IMPORT_PREFIX"]+path,digest)
                for path,(commit,digest) in fields["IMPORTS"].items()]
    return [(fields["CC"],fields["CC_PREFIX"]+path,digest)
            for path,digest in fields["THEOREMS"].items()]


def bound_research(repo,point,research,probes):
    objects=replay.research_sources(repo,point,research)
    readers={(case.revision,case.script) for case in probes
             if "{research}" in case.args and case.script not in replay.TOOLS}
    # A current exported implementation can also be consumed by a new adapter
    # even when its historical receipt alone is on the replay roster.
    readers.update((point,script) for _,script in list(readers))
    for revision,script in sorted(readers):
        consumer=revision+":"+PORT+"/"+script
        for tag,path,digest in executable_manuscripts(repo,revision,script):
            key=replay.rev(research,tag)+":"+path
            oid=replay.git(research,"rev-parse","--verify",key).decode().strip()
            raw=replay.git(research,"cat-file","blob",oid)
            codec="utf-8-sig" if script=="service_fibres.py" else "utf-8"
            actual=sha256(raw.decode(codec).replace("\r\n","\n").encode()).hexdigest()
            check(actual==digest,"Executable manuscript digest differs at "+consumer+" -> "+key)
            row=objects.setdefault(key,dict(git_object=oid,consumers=[]))
            check(row["git_object"]==oid,"Manuscript object disagrees at "+key)
            row["consumers"]=sorted(set(row["consumers"])|{consumer})
            row.setdefault("checked_text_sha256",{})[consumer]=digest
    return objects


def make(repo,point,research):
    c=replay.rev(repo,point)
    entries=replay.files(repo,c)
    check(CORE_NOTES<=set(entries),"Missing frozen interface sources: "+str(CORE_NOTES-set(entries)))
    # Future adapters can add or substitute *source data* using new files
    # and explicit maps. No edit to a pre-existing implementation is used
    # to claim it ran unchanged on the selected target.
    immutable=immutable_files(repo,c)
    probes=replay.plan(repo,c)
    manuscripts=bound_research(repo,c,research,probes)
    return dict(format=2,reference=replay.tree_binding(repo,c),proposal=replay.PROPOSAL,
                frozen_baseline=replay.HISTORICAL,code_and_interface=dict(sorted(immutable.items())),
                historical_source_trees=historical(repo,c,probes),research_objects=manuscripts,
                replay_source_revisions={case.name:case.revision for case in probes},
                original_source_commits_and_tree_ids_are_part_of_the_reference=True)


def canonical(data):
    return json.dumps(data,sort_keys=True,ensure_ascii=False,separators=(",",":")).encode()


def manifest_blob(repo,commit):
    row=replay.git(repo,"ls-tree",commit,"--",MANIFEST)
    if not row:
        return None
    header,path=row.rstrip(b"\n").split(b"\t")
    mode,kind,oid=header.split()
    check(path.decode()==MANIFEST and mode==b"100644" and kind==b"blob",
          "Expected a regular tracked freeze manifest at "+commit)
    return oid.decode()


def full_commit(repo,commit):
    check(re.fullmatch(r"[a-f0-9]{40}",commit) is not None and replay.rev(repo,commit)==commit,
          "Supply the full immutable commit ID: "+commit)
    return commit


def require_ancestor(repo,earlier,later,strict=False):
    check((not strict or earlier!=later) and
          subprocess.run(["git","-C",str(repo),"merge-base","--is-ancestor",earlier,later]).returncode==0,
          "Invalid evidence chronology: "+earlier+" -> "+later)


def verify_seal(repo,payload,record_bytes,seal,candidate,selection=None):
    seal=full_commit(repo,seal)
    require_ancestor(repo,payload["reference"]["commit"],seal,strict=True)
    oid=manifest_blob(repo,seal)
    check(oid is not None,"Original freeze commit contains no manifest")
    check(replay.git(repo,"cat-file","blob",oid)==record_bytes,
          "Supplied manifest bytes differ from the original freeze commit")
    parents=replay.git(repo,"rev-list","--parents","-n","1",seal).decode().split()[1:]
    check(all(manifest_blob(repo,parent)!=oid for parent in parents),
          "Supplied freeze commit did not introduce this manifest")
    point=replay.rev(repo,candidate)
    require_ancestor(repo,seal,point)
    comparisons={seal,point}
    if selection:
        selection=full_commit(repo,selection)
        require_ancestor(repo,seal,selection,strict=True)
        require_ancestor(repo,selection,point)
        comparisons.add(selection)
    for compared in sorted(comparisons):
        check(manifest_blob(repo,compared)==oid,"Original freeze manifest was replaced at "+compared)
        current=immutable_files(repo,compared)
        changed=[path for path,data in payload["code_and_interface"].items() if current.get(path)!=data]
        check(not changed,"Frozen sources changed at "+compared+": "+", ".join(changed))
    return oid


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--at",required=True)
    ap.add_argument("--research-repo",type=Path,required=True)
    group=ap.add_mutually_exclusive_group()
    group.add_argument("--output",type=Path,help="Create a new reference record; never replaces an existing freeze")
    group.add_argument("--verify",type=Path,help="Check every bound object and immutable input")
    ap.add_argument("--candidate",help="Optional candidate commit for an unchanged-procedure comparison")
    ap.add_argument("--freeze-commit",help="Full ID of the independently recorded commit introducing the manifest")
    ap.add_argument("--selection-commit",help="Full ID of the independently committed primitive selection")
    args=ap.parse_args()
    if args.candidate:
        check(args.verify is not None and args.freeze_commit is not None,
              "A candidate comparison requires --verify and the original --freeze-commit")
    if args.freeze_commit:
        check(args.verify is not None,"A sealed comparison requires --verify")
    if args.selection_commit:
        check(args.candidate is not None,"Checking the selection chronology requires --candidate")
    repo=Path(replay.git(HERE,"rev-parse","--show-toplevel").decode().strip())
    p=make(repo,args.at,args.research_repo.resolve())
    fingerprint=sha256(canonical(p)).hexdigest()
    record={"sha256":fingerprint,"payload":p}
    if args.verify:
        record_bytes=args.verify.read_bytes()
        check(json.loads(record_bytes)==record,"Freeze, source or manuscript changed")
        if args.freeze_commit:
            oid=verify_seal(repo,p,record_bytes,args.freeze_commit,args.candidate or args.freeze_commit,
                            args.selection_commit)
            print("Original manifest",oid,"sealed at",args.freeze_commit)
    if args.output:
        with args.output.open("x",encoding="utf-8",newline="\n") as out:
            json.dump(record,out,sort_keys=True,indent=2,ensure_ascii=False);out.write("\n")
    print(fingerprint,"at",p["reference"]["commit"],"bound",len(p["code_and_interface"]),"source objects,",
          len(p["historical_source_trees"]),"local source revisions and",len(p["research_objects"]),"external objects")


if __name__=="__main__":
    main()
