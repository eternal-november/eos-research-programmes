from pathlib import Path
import adapt_receipt

p=Path("mission.cpp")
s=p.read_text().replace("assert(argc==6);Scene","assert(argc==7);Scene")
a=''' const bool competingReceipt=std::stoi(argv[5])==1;'''
b=''' const bool competingReceipt=std::stoi(argv[5])==1;
 const bool delayedReceipt=std::stoi(argv[6])==1;
 assert(!delayedReceipt||!competingReceipt);'''
assert s.count(a)==1
s=s.replace(a,b).replace('if(i==0&&!aux1.empty()){','if(i==0&&!aux1.empty()&&!delayedReceipt){')
a='''       <<(confirmed.empty()?"-":confirmed)<<" "<<(competing.empty()?"-":competing)<<std::endl;
 }'''
b='''       <<(confirmed.empty()?"-":confirmed)<<" "<<(competing.empty()?"-":competing)<<std::endl;
    if(i==0){
       std::string reply;assert((std::cin>>reply)&&reply=="revision-complete");
       std::string after;
       if(delayedReceipt){
          assert(!aux1.empty());
          after=r.route("Audit","R",aux1,secs(auditCut[0])+3./128.);
          assert(after==aux1);
       }
       std::cout<<"late-evidence "<<(after.empty()?"-":after)<<std::endl;
    }
 }'''
assert s.count(a)==1
p.write_text(s.replace(a,b))
p=Path("bridge.py")
s=p.read_text()
a='''str(cap),str(int(case=="unconfirmed"))],'''
b='''str(cap),str(int(case=="unconfirmed")),str(int(case=="delayed"))],'''
assert s.count(a)==1
s=s.replace(a,b)
a='''            rs.record_cut(caldb,t0,confirmed)'''
b='''            rs.record_cut(caldb,t0,confirmed,2*t0+15625 if confirmed!="-" else None)'''
assert s.count(a)==1
s=s.replace(a,b)
a='''            assert install==(case=="confirmed" or policy=="forget-past")
            assert int(read("calibration",1)[0])==t1'''
b='''            assert install==(case=="confirmed" or policy=="forget-past")
            write("revision-complete")
            latevalue,=read("late-evidence",1)
            if case=="delayed":
                assert latevalue==receipt and latevalue!="-"
                rs.late_ack(caldb,t0,latevalue,2*t0+46875)
                stable=run([*args,"reply"],capture_output=True,text=True,check=True)
                assert stable.stdout==again.stdout and not stable.stderr
                # Re-reading a past refusal is not a new amendment.
                # Starting a genuinely new request after the deadline
                # is separately rejected even though the audit is known.
                expired=run([*args[:3],"after-deadline",policy,"reply"],
                    capture_output=True,text=True,check=True)
                assert expired.stdout.strip()=="refused" and not expired.stderr
            else:assert latevalue=="-"
            assert int(read("calibration",1)[0])==t1'''
assert s.count(a)==1
s=s.replace(a,b).replace('assert cd.execute("select count(*) from Edit").fetchone()==(1,)','assert cd.execute("select count(*) from Edit").fetchone()==(1+int(case=="delayed"),)')
s=s.replace('(("blocked","confirmed","unconfirmed"),range(2),','(("blocked","confirmed","unconfirmed","delayed"),range(2),')
s=s.replace('summary["forget-past"]["old"]==16','summary["forget-past"]["old"]==24')
s=s.replace('early=active.bit_count()', 'early=active2.bit_count()')
p.write_text(s)
p=Path("residual_source.py")
s=p.read_text()
a='''d.execute("CREATE TABLE Progress(t INTEGER PRIMARY KEY, actual_receipt TEXT)")'''
b='''d.execute("CREATE TABLE Progress(t INTEGER PRIMARY KEY, actual_receipt TEXT, accepted_twice INTEGER)")
        d.execute("CREATE TABLE TimeCut(now_twice INTEGER NOT NULL, close_twice INTEGER NOT NULL)")
        d.execute("insert into TimeCut values (?,?)",(2*cuts[0],2*cuts[0]+31250))'''
assert s.count(a)==1
s=s.replace(a,b)
a='''def record_cut(path,t,receipt):'''
b='''def record_cut(path,t,receipt,accepted):'''
assert s.count(a)==1
s=s.replace(a,b)
a='''        d.execute("insert into Progress values (?,?)",(t,None if receipt=="-" else receipt))
        d.commit()

def edit'''
b='''        close,=d.execute("select close_twice from TimeCut").fetchone()
        assert (receipt=="-")== (accepted is None)
        if accepted is not None:assert 2*t<accepted<=close
        d.execute("insert into Progress values (?,?,?)",(t,None if receipt=="-" else receipt,accepted))
        d.execute("update TimeCut set now_twice=?",(close,))
        d.commit()

def late_ack(path,t,receipt,accepted):
    with cs.open_calendar(path) as d:
        d.execute("begin immediate")
        old,close=d.execute("select * from TimeCut").fetchone()
        assert old==close and accepted>close
        assert d.execute("select actual_receipt,accepted_twice from Progress where t=?",(t,)).fetchone()==(None,None)
        d.execute("update Progress set actual_receipt=?,accepted_twice=? where t=?",(receipt,accepted,t))
        d.execute("update TimeCut set now_twice=?",(accepted,))
        d.commit()

def edit'''
assert s.count(a)==1
s=s.replace(a,b)
a='''        last,receipt=progress[0]
        edit_time=last+15625
        assert last<edit_time<cuts[1]
        prop=dict(rows);prop[1]=(cuts[1],cuts[1]+1000)
        residual=sum(1<<j for j,t in enumerate(cuts) if t>edit_time)&w'''
b='''        last,receipt,accepted=progress[0]
        now,close=d.execute("select * from TimeCut").fetchone()
        assert (receipt is None)==(accepted is None)
        assert accepted is None or accepted<=now
        assert 2*last<now<2*cuts[1]
        prop=dict(rows);prop[1]=(cuts[1],cuts[1]+1000)
        residual=sum(1<<j for j,t in enumerate(cuts) if 2*t>now)&w'''
assert s.count(a)==1
s=s.replace(a,b).replace('if policy=="causal":','if now>close:\n            admit=False\n        elif policy=="causal":').replace('q>edit_time','2*q>now').replace('iv[1]>edit_time','2*iv[1]>now')
p.write_text(s)
