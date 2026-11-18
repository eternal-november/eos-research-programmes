"""Fingerprint or verify a proposed immutable transfer reference; no target selection."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess

import program_replay as replay

HERE=Path(__file__).resolve().parent
PORT=replay.PORT
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


def historical(repo,at):
    # A Git tree binds every byte in its snapshot, including non-code
    # data. Historical checker inputs can be on separate worker branches.
    # Find the local commit names in source text and close over their
    # actual checker implementations, by blob identity rather than filename.
    found={at,replay.HISTORICAL,replay.PROPOSAL}
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
        if meta.split()[1]==b"blob" and file!=PORT+"/TODO.md" and file!=PORT+"/RP6-FREEZE.json":
            fixed[file]=meta.split()[2].decode()
    return fixed


def make(repo,point,research):
    c=replay.rev(repo,point)
    entries=replay.files(repo,c)
    check(CORE_NOTES<=set(entries),"Missing frozen interface sources: "+str(CORE_NOTES-set(entries)))
    # Future adapters can add or substitute *source data* using new files
    # and explicit maps. No edit to a pre-existing implementation is used
    # to claim it ran unchanged on the selected target.
    immutable=immutable_files(repo,c)
    manuscripts=replay.research_sources(repo,c,research)
    return dict(format=1,reference=replay.tree_binding(repo,c),proposal=replay.PROPOSAL,
                frozen_baseline=replay.HISTORICAL,code_and_interface=dict(sorted(immutable.items())),
                historical_source_trees=historical(repo,c),research_objects=manuscripts,
                original_source_commits_and_tree_ids_are_part_of_the_reference=True)


def canonical(data):
    return json.dumps(data,sort_keys=True,ensure_ascii=False,separators=(",",":")).encode()


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--at",required=True)
    ap.add_argument("--research-repo",type=Path,required=True)
    group=ap.add_mutually_exclusive_group()
    group.add_argument("--output",type=Path,help="Create a new reference record; never replaces an existing freeze")
    group.add_argument("--verify",type=Path,help="Check every bound object and immutable input")
    ap.add_argument("--candidate",help="Optional candidate commit for an unchanged-procedure comparison")
    args=ap.parse_args()
    repo=Path(replay.git(HERE,"rev-parse","--show-toplevel").decode().strip())
    p=make(repo,args.at,args.research_repo.resolve())
    fingerprint=sha256(canonical(p)).hexdigest()
    record={"sha256":fingerprint,"payload":p}
    if args.verify:
        check(json.loads(args.verify.read_text(encoding="utf-8"))==record,"Freeze, source or manuscript changed")
    if args.candidate:
        check(args.verify is not None,"A transfer comparison requires an existing reference record")
        q=replay.rev(repo,args.candidate)
        current=immutable_files(repo,q)
        changed=[f for f,oid in p["code_and_interface"].items() if current.get(f)!=oid]
        check(not changed,"Frozen files changed: "+", ".join(changed))
    if args.output:
        with args.output.open("x",encoding="utf-8",newline="\n") as out:
            json.dump(record,out,sort_keys=True,indent=2,ensure_ascii=False);out.write("\n")
    print(fingerprint,"at",p["reference"]["commit"],"bound",len(p["code_and_interface"]),"source objects,",
          len(p["historical_source_trees"]),"local source revisions and",len(p["research_objects"]),"external objects")


if __name__=="__main__":
    main()
