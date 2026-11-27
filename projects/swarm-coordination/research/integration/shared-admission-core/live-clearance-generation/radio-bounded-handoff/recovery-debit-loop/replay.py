"""I07 fixture: actual repeated SubT debits, same pinned recovery station."""
from pathlib import Path
import itertools
import json
import sys
import tempfile

from core import Event, Row, Use, check


def direct(q, cap, window, diagnostic, suffix, deadlines):
    names=[]
    for a,b in itertools.product(range(6,deadlines[0]+1),range(6,deadlines[1]+1)):
        debits=sorted(((5,q),(8,suffix),(a,diagnostic),(b,diagnostic)))
        load=[]
        for t,n in debits:
            load=[(pt,x) for pt,x in load if t-pt<=window]
            if sum(x for _,x in load)+n>cap:
                break
            load.append((t,n))
        else:
            names.append((a,b))
    return names


def compiled(q, cap, window, diagnostic, suffix, deadlines):
    key=("q-tx",)
    def ev(t,order,n,paid=()):
        return Event(t,order,uses=(Use(key,n,cap,window),),paid=paid)
    fixed=(ev(5,0,q),)
    dues={"check-1":deadlines[0],"check-2":deadlines[1],"old":8}
    options={}
    for a,b in itertools.product(range(6,deadlines[0]+1),range(6,deadlines[1]+1)):
        options[a,b]=(ev(a,1,diagnostic,("check-1",)),
                      ev(b,2,diagnostic,("check-2",)),
                      ev(8,3,suffix,("old",)))
    row=Row((),frozenset(),fixed,options)
    return [name for name in options if check(row,name,6,dues)]


def exact_audit():
    counts={"checked":0,"feasible":0}
    for q,cap,w,d,s,a,b in itertools.product(
        [0,3,10,140,147,148],[10,160,319,320],[2,4,5],[1,4,7],
        [6,116,173],range(6,9),range(8,12)):
        x=direct(q,cap,w,d,s,(a,b))
        assert x==compiled(q,cap,w,d,s,(a,b))
        counts["checked"]+=1
        counts["feasible"]+=bool(x)
    return counts


def instrument(parent_path):
    # Reuse pinned source and authored timing except for these named hooks.
    src=parent_path.read_text()
    anchor="\ndef main():\n"
    assert src.count(anchor)==1
    src=src.split(anchor)[0]
    old="    header_view=None\n"
    before="""    # Both checks reach a separate registered receiver, but share Q's TX.
    def checks(due):
        for idx,t in enumerate(schedule):
            if t==due:
                assert send(t,"Q","extra","chk"+str(idx))
    checks(6)
    header_view=None
"""
    assert src.count(old)==1
    src=src.replace(old,before)
    old="    step(7)\n"
    assert src.count(old)==1
    src=src.replace(old,old+"    checks(7)\n")
    old="    if result:\n        assert result=="
    before="""    # A refill is a failed repair probe, not a simulator reset. Missing
    # delivery actually triggers two more attempts in the early control.
    if arm=="early" and row and header_view and not first_complete:
        for t in (11,17):
            assert not send(t,"Q","sink","q"*q_debit,False)
            assert send(t+1,"Q","extra","chk0")
            assert send(t+2,"Q","extra","chk1")
            assert send(t+2,"Base","preq","d?")
            assert not send(t+3,"Q","owed",fragment,True)
    if arm in ("split","direct") and row and header_view and not first_complete:
        raise AssertionError("guaranteed old service was lost")
    checks(10)
    if result:
        assert result=="""
    assert src.count(old)==1
    src=src.replace(old,before)
    ns={}
    exec(compile(src,str(parent_path),"exec"),ns)
    return ns


def main():
    s=instrument(Path(sys.argv[1])/"parent.py")
    def run(arm,schedule):
        s["schedule"]=schedule
        with tempfile.TemporaryDirectory() as p:
            return s["trial"](Path(p),"after-commit","after-witness-commit",
                              True,True,140,arm)

    choices=compiled(140,320,4,4,173,(7,10))
    assert choices==direct(140,320,4,4,173,(7,10))==[(6,10),(7,10)]
    assert not compiled(140,320,4,4,173,(7,9))
    early=run("early",(6,7))
    joint=run("split",choices[0])
    comparator=run("direct",direct(140,320,4,4,173,(7,10))[0])
    assert joint==comparator and joint["apply"]==8 and joint["side"]==2
    assert early["apply"] is None and early["side"]==2
    attempted=[x for x in early["radio"] if x[1:4]==("Q","owed",173)]
    assert [x[0] for x in attempted]==[8,14,20] and all(x[-2:]==(0,False) for x in attempted)
    assert [x[0] for x in early["radio"] if x[1:4]==("Q","extra",4) and x[-1]]==[6,7,12,13,18,19]
    assert [x[0] for x in joint["radio"] if x[1:4]==("Q","extra",4) and x[-1]]==[6,10]
    s["air"].stdin.close()
    assert s["air"].wait()==0
    print(json.dumps(dict(audit=exact_audit(),choices=choices,early=early,joined=joint),
                     indent=2,sort_keys=True))


if __name__=="__main__":
    main()
