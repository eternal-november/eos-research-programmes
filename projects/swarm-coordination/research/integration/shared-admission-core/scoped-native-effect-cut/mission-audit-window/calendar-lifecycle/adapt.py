from pathlib import Path
import adapt_window

p=Path("mission.cpp")
s=p.read_text()
a=s.index(" assert(argc==10);")
b=s.index(" const int world",a)
s=s[:a]+''' assert(argc==5);Scene s(argv[1]);
'''+s[b:]
a=s.index(" const Cover envelope")
b=s.index(" assert(active!=0);",a)
s=s[:a]+''' // The source returns a projection of its committed appointments,
 // never a future readiness mask supplied by the experiment driver.
 std::cout<<"calendar "<<w<<" "<<auditCut[0]<<" "<<auditCut[1]<<std::endl;
 unsigned aSupport,bSupport;
 assert((std::cin>>aSupport>>bSupport)&&(aSupport|bSupport)<=3);
 const Cover envelope{w,{aSupport,bSupport,0},{1,1,0}};
 const unsigned active=activate(envelope,true,3);
'''+s[b:]
a=''' unsigned used=0;
 for(unsigned i=0;i<2;++i){
    if(!aux1.empty())break;
    const bool deadA=(active&1)&&(aMiss&(1u<<i));
    const bool deadB=(active&2)&&(bMiss&(1u<<i));'''
b=''' unsigned used=0,coverActual=0;
 std::cout<<"revise "<<active<<std::endl;
 std::string readyToRead;assert((std::cin>>readyToRead)&&readyToRead=="ok");
 for(unsigned i=0;i<2;++i){
    std::cout<<"calibration "<<auditCut[i]<<std::endl;
    unsigned unavailableA,unavailableB;
    assert((std::cin>>unavailableA>>unavailableB)&&unavailableA<=1&&unavailableB<=1);
    const bool deadA=(active&1)&&unavailableA;
    const bool deadB=(active&2)&&unavailableB;
    if(deadA||deadB)coverActual|=1u<<i;
    if(!aux1.empty())continue;'''
assert s.count(a)==1
s=s.replace(a,b)
a=''' const unsigned coverActual=(active&1?aMiss:0u)|(active&2?bMiss:0u);
'''
assert s.count(a)==1
s=s.replace(a,'')
p.write_text(s)
p=Path("bridge.py")
s=p.read_text()
s='import calendar_source as cs\n'+s
s=s.replace('phasebit,calib,win):','phasebit,calib,policy,kind,death):')
s=s.replace('str(cap),*map(str,win)],','str(cap)],')
a=s.index('            w,active,used,base=')
b=s.index('            x,primary,cut=',a)
s=s[:a]+'''            w,t0,t1=map(int,read("calendar",3))
            assert w==3 and t1-t0==31250
            caldb=Path(scratch)/"owned.sqlite"
            cs.initialize(caldb,(t0,t1),w)
            proposal=cs.pending_read(caldb)
            assert proposal==(1,1)
            write(" ".join(map(str,proposal)))
            active=int(read("revise",1)[0])
            assert active==3
            args=[sys.executable,str(Path(__file__).with_name("calendar_source.py")),str(caldb),"amend",
                  kind,policy]
            cutresult=run([*args,death],capture_output=True,text=True)
            assert cutresult.returncode=={"before":71,"after":72}[death] and not cutresult.stdout and not cutresult.stderr
            if death=="before":assert cs.pending_read(caldb)==proposal
            again=run([*args,"reply"],capture_output=True,text=True,check=True)
            assert not again.stderr
            replay=run([*args,"reply"],capture_output=True,text=True,check=True)
            assert replay.stdout==again.stdout and not replay.stderr
            install=again.stdout.strip()=="installed"
            assert again.stdout.strip() in ("installed","refused")
            expected_install=(kind in ("none","out")
                  or kind=="paired" and policy!="frozen"
                  or kind in ("east","west") and policy=="separate")
            assert install==expected_install
            write("ok")
            for t in (t0,t1):
                seen=int(read("calibration",1)[0]);assert t==seen
                write(" ".join(map(str,cs.tick(caldb,t))))
            with cs.open_calendar(caldb) as cd:
                assert cd.execute("select count(*) from Edit").fetchone()==(1,)
                assert cd.execute("select count(*) from Applied").fetchone()==(int(install),)
                work=cd.execute("select actor,cut from Operation order by actor").fetchall()
                expected_moves={"none":(),"east":(0,),"west":(1,),"paired":(0,1),"out":(2,)}[kind] if install else ()
                assert work==[(i,t1 if i in expected_moves else t0) for i in range(3)]
            w2,active2,used,base=map(int,read("window",4))
            assert w2==w and active2==active
            expected_used=(0 if install and kind in ("east","west") else 1 if install and kind=="paired" else 2)
            assert used==expected_used
'''+s[b:]
s=s.replace('early=active.bit_count(),used=used)','early=active.bit_count(),used=used,install=install)')
a=s.index('    summary={}',s.index('def main'))
b=s.index('if __name__=="__main__":',a)
s=s[:a]+'''    summary={}
    for policy in ("shared","direct","separate","frozen"):
        results=[]
        for kind,w,gc in product(("east","west","paired","out"),range(2),("before","after")):
           # Both independent routes; both phase orders of the actual
           # gate and dock controllers, versus the durable calendar cut.
           for time in ("before","after"):
              dockcut="before" if gc=="after" else "after"
              r=trace(binary,sites,w,2,3,6,dockcut,'checked',"clearance",gc,0,"resource-scoped",
                      policy,kind,time)
              assert r["effects"]==1 and r["ack"] and r["egress"]<454000000 and r["timely_effect"]
              bad=policy=="separate" and kind in ("east","west")
              assert r["audit"]==([2] if bad else [1,2])
              results.append(r)
        summary[policy]=dict(n=len(results),old=sum(bool(r["used"]) for r in results),
                 installs=sum(r["install"] for r in results),egress=max(r["egress"] for r in results))
    assert summary["shared"]==summary["direct"]
    assert summary["shared"]["installs"]==16 and summary["frozen"]["installs"]==8
    assert summary["separate"]["old"]==16
    print(json.dumps(summary,sort_keys=True))
''' + s[b:]
p.write_text(s)
