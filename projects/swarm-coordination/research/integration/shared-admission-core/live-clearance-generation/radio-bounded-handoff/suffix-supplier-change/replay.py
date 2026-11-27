"""Test a second-fault supplier change in the pinned I1 warehouse/radio case."""
from pathlib import Path
from itertools import product
import json
import sys
import tempfile
import types

from core import Event, Use, Row, admitted

OPTIONS=tuple((s,b) for s,b in product(("Q","P"),(7,10)))
DUES={"diagnostic-1":7,"diagnostic-2":10,"old":8}


def direct(cells, debit, licensed, visible):
    # Enumerate same possible physical modes for each observed notice.
    # Q has spent 140 at 5 and 4 at 6. P has spent debit at 5 and 114 at 6.
    return tuple((s,b) for s,b in OPTIONS if all(
        s==physical and s in licensed and (
            s=="Q" and 140+4+173+(4 if b==7 else 0)<=320 or
            s=="P" and debit+114+173<=320)
        for physical in cells))


def row(mode, notice, debit, licensed):
    def debit_at(n,t,s,o,earned=(),need=()):
        return Event(t,o,need=frozenset(need),uses=(Use((s,),n,320,4),),paid=earned)
    facts={("ready",mode)} | {("licensed",name) for name in licensed}
    received=() if notice is None else ((notice,"entry",mode),)
    history=(debit_at(140,5,"Q",0),debit_at(debit,5,"P",1),
             debit_at(114,6,"P",0),debit_at(4,6,"Q",1,("diagnostic-1",)))
    choices={(s,b):(debit_at(173,8,s,0,("old",),(("ready",s),("licensed",s))),
                    debit_at(4,b,"Q",1,("diagnostic-2",)))
             for s,b in OPTIONS}
    return Row(received,frozenset(facts),history,choices)


def verdict(notice,debit,licensed):
    seen=admitted([row(s,notice,debit,licensed) for s in ("Q","P")],
                  "entry",7,DUES,OPTIONS)
    for view,result in seen.items():
        worlds=(view[0][1],) if view else ("Q","P")
        assert result==direct(worlds,debit,licensed,view)
    return seen


def audit():
    rows=over=0
    for n,d,p,q in product((None,7,8),range(0,207),(0,1),(0,1)):
        licensed={s for s,b in (("P",p),("Q",q)) if b}
        v=verdict(n,d,licensed)
        over+=len(v)
        for key,choices in v.items():
            if not key:
                assert not choices
            elif key[0][1]=="Q":
                assert bool(choices)==bool(q) and (("Q",7) not in choices)
            else:
                assert bool(choices)==bool(p and d<=33)
        rows+=1
    return dict(cases=rows,observation_cells=over)


def load_runner(path):
    source=path.read_text()
    run=types.ModuleType("feedback")
    exec(compile(source,str(path),"exec"),run.__dict__)
    return run


def instrument(path, prior_extension):
    # Start from the verified two-plant runner, then add one notice and
    # a guarded single suffix transmission. No changes to native C++.
    src=path.read_text()
    anchor="\ndef main():\n"
    assert src.count(anchor)==1
    source=src.split(anchor)[0]
    hook="    checks(6)\n    header_view=None\n"
    assert source.count(hook)==0
    # Capture the prior extension's actual instrumented source without
    # executing a broker; the program text is already pinned and verified.
    saved=prior_extension.__dict__["compile"] if "compile" in prior_extension.__dict__ else compile
    def intercepted(text,filename,kind):
        nonlocal source
        source=text
        return compile("",filename,kind)
    prior_extension.__dict__["compile"]=intercepted
    prior_extension.instrument(path)
    prior_extension.__dict__["compile"]=saved

    def replace(a,b):
        nonlocal source
        assert source.count(a)==1,a
        source=source.replace(a,b)
    replace("    checks(6)\n    header_view=None\n",
        """    if p_debit:
        assert not send(5,"P","sink","z"*p_debit,False)
    checks(6)
    header_view=None
""")
    replace("    step(7)\n    checks(7)\n",
        """    step(7)
    # The physical link mode is input to the fixture only. Controller reads
    # actual callback, not mode; the notice linkage is an authored contract.
    observed=send(7,"Base","preq",mode,int(notice==7))
    received=((7,observed),) if observed else ()
    feasible=plan.get(received,())
    selected=feasible[0] if feasible else None
    if selected:
        schedule=(6,selected[1])
    checks(7)
""")
    # schedule assignment makes it local; initialize it before the first use.
    replace("    def checks(due):\n","    schedule=(6,0)\n    def checks(due):\n")
    replace('            requested=send(7,"Base","preq","d?",True)=="d?"\n            assert requested',
        """            if selected:
                command="preq" if selected[0]=="Q" else "preP"
                requested=send(7,"Base",command,"d?",True)=="d?"
                assert requested""")
    replace('        late=send(8,"Q","owed",fragment if requested else row[0],late_link)',
        """        if notice==8:
            assert send(8,"Base","preq",mode,True)==mode
        late=None
        if selected and requested:
            permitted=selected[0]
            late=send(8,permitted,"owed",fragment if requested else row[0],
                      permitted==mode)
""")
    replace('    if arm in ("split","direct") and row and header_view and not first_complete:',
            '    if selected and row and header_view and not first_complete:')
    replace('                charged=sum(x[4] for x in tape)+2,side=2)',
            '                charged=sum(x[4] for x in tape)+2,side=2,selection=selected)')
    ns={}
    exec(compile(source,str(path),"exec"),ns)
    return ns


def main():
    up=Path(sys.argv[1])
    old=load_runner(up/"feedback.py")
    s=instrument(up/"parent.py",old)
    table=[]
    for mode,n,d,p,q in product(("Q","P"),(None,7,8),(33,34),(0,1),(0,1)):
        licensed={x for x,b in (("P",p),("Q",q)) if b}
        plan=verdict(n,d,licensed)
        s.update(mode=mode,notice=n,p_debit=d,plan=plan)
        with tempfile.TemporaryDirectory() as dpath:
            v=s["trial"](Path(dpath),"after-commit","after-witness-commit",True,True,140,"split")
        expected=n==7 and (mode=="Q" and q or mode=="P" and p and d<=33)
        assert bool(v["apply"])==bool(expected) and v["side"]==2
        tape=[x for x in v["radio"] if x[2:4]==("owed",173)]
        assert len(tape)==int(bool(expected))
        if expected:
            assert tape[0][1]==mode and tape[0][-2:]==(173,True)
            assert v["result"]=={"status":"cached","tick":8,"result":[1,0]}
        table.append(dict(mode=mode,notice=n,debit=d,backup_P=p,old_Q=q,native=v))
    s["air"].stdin.close()
    assert s["air"].wait()==0
    print(json.dumps(dict(audit=audit(),native=table),indent=2,sort_keys=True))


if __name__=="__main__":
    main()
