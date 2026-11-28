from pathlib import Path
import adapt_residual

p=Path("mission.cpp")
s=p.read_text()
a=''' assert(argc==5);Scene s(argv[1]);'''
b=''' assert(argc==6);Scene s(argv[1]);
 const bool competingReceipt=std::stoi(argv[5])==1;'''
assert s.count(a)==1
s=s.replace(a,b)
a=''' const auto auxBase=t;
 // Preserve'''
b=''' const auto auxBase=t;
 std::string competing;
 if(competingReceipt){
    // Separately owed six-byte result using the opposite direction of
    // the same native path. Its physical copy is at the Audit cite.
    r.add("ArchiveCopy",r.where.at("Audit"));
    competing=r.route("ArchiveCopy","R","L35032",secs(auxBase));
    assert(competing=="L35032");
    assert(r.w.state("R").bytes_received_this_epoch==6);
    assert(r.w.b.Unregister("ArchiveCopy"));
 }
 // Preserve'''
assert s.count(a)==1
s=s.replace(a,b)
a='''    std::cout<<"audit-cut "<<auditCut[i]<<" "<<(aux1.empty()?"-":aux1)<<std::endl;'''
b='''    std::string confirmed;
    if(i==0&&!aux1.empty()){
       // The dock remains separate from this policy authority. A native
       // response issued by the actual audit recipient carries the exact
       // named sample back to the requester before the revision cut.
       r.w.b.pose_update_f=normal_pose;
       confirmed=r.route("Audit","R",aux1,secs(auditCut[i])+1./128.);
       assert(confirmed.empty()==competingReceipt);
       assert(r.w.state("Audit").bytes_sent_this_epoch==1);
       if(!confirmed.empty())assert(confirmed==aux1);
    }
    std::cout<<"audit-cut "<<auditCut[i]<<" "<<(aux1.empty()?"-":aux1)<<" "
       <<(confirmed.empty()?"-":confirmed)<<" "<<(competing.empty()?"-":competing)<<std::endl;'''
assert s.count(a)==1
p.write_text(s.replace(a,b).replace("Audit cite","Audit site"))
p=Path("bridge.py")
s=p.read_text()
a='''str(cap)],
                   stdin'''
b='''str(cap),str(int(case=="unconfirmed"))],
                   stdin'''
assert s.count(a)==1
s=s.replace(a,b)
a='''            first,receipt=read("audit-cut",2);assert int(first)==t0
            assert (receipt=="-")==(case=="blocked")
            # Model an unavailable handoff record even though the isolated
            # native evaluator can establish that the first output arrived.
            rs.record_cut(caldb,t0,receipt if case=="confirmed" else "-")'''
b='''            first,receipt,confirmed,side=read("audit-cut",4);assert int(first)==t0
            assert (receipt=="-")==(case=="blocked")
            assert (confirmed!="-")==(case=="confirmed")
            assert confirmed=="-" or confirmed==receipt
            assert side==("L35032" if case=="unconfirmed" else "-")
            # Only the value actually returned over RF can enter the
            # owned appointment source. The evaluator separately tracks
            # delivered first audit and retained independently owed copy.
            rs.record_cut(caldb,t0,confirmed)'''
assert s.count(a)==1
s=s.replace(a,b)
a='''            last,receipt=read("audit-cut",2);assert int(last)==t1'''
b='''            last,receipt,r2,side2=read("audit-cut",4);assert int(last)==t1
            assert r2=="-" and side2==side'''
assert s.count(a)==1
p.write_text(s.replace(a,b))
p=Path("residual_source.py")
s=Path("residual_source.baseline").read_text()
assert "edit_time=last+2000" in s
p.write_text(s.replace("edit_time=last+2000","edit_time=last+15625"))
