from pathlib import Path
import adapt_lifecycle

p=Path("mission.cpp")
s=p.read_text()
a='''    if(!aux1.empty())continue;
    // The caller only consumes CURRENT pose source replies.'''
b='''    if(aux1.empty()){
    // The caller only consumes CURRENT pose source replies.'''
assert s.count(a)==1
s=s.replace(a,b)
a='''    r.w.b.pose_update_f=normal_pose;
 }
 assert(bool(w&~coverActual)==!aux1.empty());'''
b='''    r.w.b.pose_update_f=normal_pose;
    }
    std::cout<<"audit-cut "<<auditCut[i]<<" "<<(aux1.empty()?"-":aux1)<<std::endl;
 }
 assert(bool(w&~coverActual)==!aux1.empty());'''
# coverActual includes physical past/carry, not a new read of the final calendar.
assert s.count(a)==1
p.write_text(s.replace(a,b))
p=Path("bridge.py")
s='import residual_source as rs\n'+p.read_text()
s=s.replace('phasebit,calib,policy,kind,death):','phasebit,calib,policy,case,death):')
a=s.index("            cs.initialize(")
b=s.index("            x,primary,cut=",a)
s=s[:a]+'''            rs.initialize(caldb,(t0,t1),w,case)
            proposal=cs.pending_read(caldb)
            assert proposal==((1,0) if case=="blocked" else (0,0))
            write(" ".join(map(str,proposal)))
            assert read("revise",1)==["3"]
            write("ok")
            assert int(read("calibration",1)[0])==t0
            write(" ".join(map(str,cs.tick(caldb,t0))))
            first,receipt=read("audit-cut",2);assert int(first)==t0
            assert (receipt=="-")==(case=="blocked")
            # Model an unavailable handoff record even though the isolated
            # native evaluator can establish that the first output arrived.
            rs.record_cut(caldb,t0,receipt if case=="confirmed" else "-")
            args=[sys.executable,str(Path(__file__).with_name("residual_source.py")),str(caldb),"late-B",policy]
            cutresult=run([*args,death],capture_output=True,text=True)
            assert cutresult.returncode=={"before":71,"after":72}[death] and not cutresult.stdout and not cutresult.stderr
            if death=="before":assert cs.pending_read(caldb)==proposal
            again=run([*args,"reply"],capture_output=True,text=True,check=True)
            replay=run([*args,"reply"],capture_output=True,text=True,check=True)
            assert not again.stderr and not replay.stderr and again.stdout==replay.stdout
            install=again.stdout.strip()=="installed"
            assert install==(case=="confirmed" or policy=="forget-past")
            assert int(read("calibration",1)[0])==t1
            available=cs.tick(caldb,t1)
            assert available==(0,int(install))
            write(" ".join(map(str,available)))
            last,receipt=read("audit-cut",2);assert int(last)==t1
            with cs.open_calendar(caldb) as cd:
                assert cd.execute("select count(*) from Edit").fetchone()==(1,)
                assert cd.execute("select count(*) from Applied").fetchone()==(int(install),)
                starts=cd.execute("select actor,cut from Operation order by actor").fetchall()
                assert starts==([(0,t0)] if case=="blocked" else [])+([(1,t1)] if install else [])
            w2,active2,used,base=map(int,read("window",4))
            assert w2==w and active2==3
            assert used==(0 if case=="blocked" and install else 2 if case=="blocked" else 1)
''' + s[b:]
a=s.index('    summary={}',s.index('def main'))
b=s.index('if __name__=="__main__":',a)
s=s[:a]+'''    summary={}
    for policy in ("causal","direct","forget-past"):
        results=[]
        for case,w,gc,death in product(("blocked","confirmed","unconfirmed"),range(2),
                                         ("before","after"),("before","after")):
            dockcut="before" if gc=="after" else "after"
            r=trace(binary,sites,w,2,3,6,dockcut,"checked","clearance",gc,0,"resource-scoped",
                    policy,case,death)
            assert r["effects"]==1 and r["ack"] and r["egress"]<454000000 and r["timely_effect"]
            assert r["audit"]==([2] if policy=="forget-past" and case=="blocked" else [1,2])
            results.append(r)
        summary[policy]=dict(n=len(results),old=sum(bool(r["used"]) for r in results),
             installs=sum(r["install"] for r in results),egress=max(r["egress"] for r in results))
    assert summary["causal"]==summary["direct"]
    assert summary["causal"]["installs"]==8 and summary["forget-past"]["old"]==16
    print(json.dumps(summary,sort_keys=True))
''' + s[b:]
p.write_text(s)
