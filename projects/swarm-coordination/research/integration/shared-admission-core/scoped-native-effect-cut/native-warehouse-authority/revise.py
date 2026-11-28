from pathlib import Path
m=Path("motion_journal.py")
s=Path("source/motion_journal.py").read_text()
a='''    CREATE TABLE IF NOT EXISTS receipt('''
b='''    CREATE TABLE IF NOT EXISTS power(
      singleton INTEGER PRIMARY KEY CHECK(singleton=1), mask INTEGER NOT NULL CHECK(mask BETWEEN 0 AND 3));
    INSERT OR IGNORE INTO power VALUES (1,3);
    CREATE TABLE IF NOT EXISTS revision(epoch INTEGER PRIMARY KEY, oldmask NOT NULL, newmask NOT NULL);
    CREATE TABLE IF NOT EXISTS receipt('''
assert s.count(a)==1
s=s.replace(a,b)
a='''def apply(db,plant,key,actor,termination=False):'''
b='''def current(db):
    power,=db.execute("select mask from power where singleton=1").fetchone()
    return power

def handoff(db, mask):
    # This caller is the simulation's expressly authorized revision owner.
    # The actual linearization cut is the committed SQLite transaction.
    db.execute("begin immediate")
    original=current(db)
    assert original==3 and mask in range(4)
    db.execute("update power set mask=? where singleton=1",(mask,))
    db.execute("insert into revision values (1,?,?)",(original,mask))
    db.commit()

def apply(db,plant,key,actor,termination=False):'''
assert s.count(a)==1
s=s.replace(a,b)
a='''        if w.grid[0,actor+1,2]:'''
b='''        if not (current(db)&(1<<actor)) or w.grid[0,actor+1,2]:'''
assert s.count(a)==1
s=s.replace(a,b)
m.write_text(s)
m=Path("journal_effect.py")
s=Path("source/journal_effect.py").read_text()
a='''    p.add_argument("--warehouse",'''
assert s.count(a)==1
s=s.replace(a,'''    p.add_argument("--cut",type=Path,required=True)
'''+a)
a='''            for prior,blocked,after,arm,edge in product(range(2),range(2),range(4),range(4),range(2)):
                case=(prior,blocked,after,arm,edge)'''
b='''            for prior,blocked,after,arm,edge,owner in product(range(2),range(2),range(4),range(4),range(2),range(4)):
                case=(prior,blocked,after,arm,edge,owner)'''
assert s.count(a)==1
s=s.replace(a,b)
a='''                result=None
                emit(0,after,arm,edge)'''
b='''                issued=j.current(db)
                assert issued==3
                result=None
                emit(0,after,arm,edge)'''
assert s.count(a)==1
s=s.replace(a,b)
a='''                    if line[0]=="P":emit(1)'''
b='''                    if line[0]=="P":
                        # The authority change occurs after ordinary
                        # radio work and the earlier journal-owned move,
                        # but before the actual first charged attempt.
                        j.handoff(db,owner)
                        db.close()
                        db=j.connect(path)
                        assert j.current(db)==owner
                        assert list(db.execute("select oldmask,newmask from revision"))==[(issued,owner)]
                        assert j.resolved(db,j.OLD)==existing
                        assert j.Plant(iso,n).snapshot(j.Plant(iso,n).native(db))==plant.snapshot(pre)
                        emit(1)'''
assert s.count(a)==1
s=s.replace(a,b)
a='''                        allow=(existing is not None or not pre.grid[0,k+1,2])
                        if arm==2:allow=not pre.grid[0,k+1,2] # suppress keyed evidence before dispatch
                        emit(int(allow))'''
b='''                        room=not pre.grid[0,k+1,2]
                        if arm==0:
                            # An old durable result is read under its own
                            # standing A/B read permission. A fresh attempt
                            # must instead use the currently authorized actor.
                            inspect=existing is not None
                            scope=k in (0,1) if inspect else bool(j.current(db)&(1<<k))
                            flags=[scope,True,room,True]
                            response=int(sp.check_output([args.cut,"inspect" if inspect else "effect",
                                      *(str(int(b)) for b in flags)],text=True))
                            allow=response==(0 if inspect else 6)
                        elif arm==1:
                            allow=existing is not None or (room and bool(j.current(db)&(1<<k)))
                        else:
                            # Wrong scope for fresh power, exact receipt
                            # otherwise not weakened in this ablation.
                            allow=existing is not None or (room and bool(issued&(1<<k)))
                        emit(int(allow))'''
assert s.count(a)==1
s=s.replace(a,b)
a='''                mov={1} if not blocked else set()
                propose=rad&({0,1} if prior else mov) if arm<2 else rad&mov if arm==2 else rad
                k=min(propose,default=-1)
                expected=0 if k<0 else 2 if prior else int(k in mov)
                assert (outcome,paid,rx,tx)==(expected,int(expected>0),int(k>=0),int(k>=0)*4)'''
b='''                mov={1} if not blocked else set()
                live={k for k in (0,1) if owner&(1<<k)}
                propose=rad&({0,1} if prior else (mov&live)) if arm<2 else rad&({0,1} if prior else mov) if arm==2 else rad
                k=min(propose,default=-1)
                expected=0 if k<0 else 2 if prior else int(k in mov&live)
                assert (outcome,paid,rx,tx)==(expected,int(expected>0),int(k>=0),int(k>=0)*4),(case,propose,outcome,tx)
                assert side==1+(2 if after==2 else 1),(case,side)
                runs[f"side/{arm}"]+=side
                runs[f"ungranted_attempt/{arm}"]+=int(not prior and k>=0 and k not in live)
                runs[f"historical_without_act/{arm}"]+=int(expected==2 and k not in live)'''
assert s.count(a)==1
s=s.replace(a,b)
a='''                if after==0 and not edge:
                    examples[str((prior,blocked,arm))]=[paid,rx,tx,result]'''
b='''                if after==0 and not edge and owner in (0,2):
                    examples[str((prior,blocked,arm,owner))]=[paid,rx,tx,result]'''
assert s.count(a)==1
s=s.replace(a,b)
s=s.replace('''range(4),range(4),range(2))),
        "results"''','''range(4),range(4),range(2),range(4))),
        "results"''')
m.write_text(s)
