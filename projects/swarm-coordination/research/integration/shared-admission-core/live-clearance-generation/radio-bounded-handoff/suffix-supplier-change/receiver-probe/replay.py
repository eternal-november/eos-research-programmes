"""Held-in #659 test: earn a source-qualified supplier cue at the sink."""
import json,sys,tempfile
from itertools import product
from pathlib import Path
from core import Event,Use,Row,admitted
import supplier659 as prior

def options(seen,probe,early,d,licensed):
    if seen=="?":
        worlds=("Q","P")
    elif seen=="+":worlds=(probe,)
    else:worlds=("P" if probe=="Q" else "Q",)
    opts=prior.OPTIONS
    need={"old":8,"diagnostic-1":7,"diagnostic-2":10}
    def e(t,o,who,n,paid=(),needs=()):
        return Event(t,o,need=frozenset(needs),uses=(Use((who,),n,320,4),),paid=paid)
    def row(w):
        fixed=[e(5,0,"Q",140),e(5,1,"P",d),e(6,0,"P",114),e(6,1,"Q",4,("diagnostic-1",))]
        # A failed radio attempt is still charged at the sender.
        if early:fixed.append(e(7,0,probe,1))
        choices={(s,b):(e(8,0,s,173,("old",),(("ready",s),("licensed",s))),
                        e(b,1,"Q",4,("diagnostic-2",))) for s,b in opts}
        return Row(((7,"entry",seen),),frozenset({("ready",w)}|{("licensed",x) for x in licensed}),tuple(fixed),choices)
    out=next(iter(admitted([row(w) for w in worlds],"entry",7,need,opts).values()))
    exact=tuple((s,b) for s,b in opts if all(s==w and s in licensed and
        (144+173+int(probe=="Q" and early)+4*(b==7)<=320 if s=="Q"
         else d+114+173+int(probe=="P" and early)<=320) for w in worlds))
    assert out==exact,(out,exact)
    return out[0] if out else None

def instrument(up):
    raw=prior.load_runner(up/"feedback.py")
    orig=prior.compile if hasattr(prior,"compile") else compile
    source=""
    def intercepted(text,file,kind):
        nonlocal source
        source=text
        return compile("",file,kind)
    prior.compile=intercepted
    try:prior.instrument(up/"parent.py",raw)
    finally:prior.compile=orig
    def swap(a,b):
        nonlocal source
        assert source.count(a)==1,a
        source=source.replace(a,b)
    swap('    schedule=(6,0)\n','    schedule=(6,10)\n')
    swap('    assert send(3,"Side","owed","q"*130)\n',
         '    assert send(3,"Side","owed","q"*130)\n'
         '    if condition=="rx_full":assert send(3,"Side","owed","z"*76)\n')
    swap('    observed=send(7,"Base","preq",mode,int(notice==7))\n'
         '    received=((7,observed),) if observed else ()\n'
         '    feasible=plan.get(received,())\n'
         '    selected=feasible[0] if feasible else None\n',
         '    early=condition!="late"\n'
         '    observed=send(7,probe,"owed","c",probe==mode and condition!="erased") if early else None\n'
         '    seen="+" if observed else "-" if condition in ("closed","prep_erased") else "?"\n'
         '    selected=options(seen,probe,early,p_debit,licensed)\n')
    swap('                requested=send(7,"Base",command,"d?",True)=="d?"\n'
         '                assert requested\n',
         '                requested=send(7,"Base",command,"d?",condition!="prep_erased")=="d?"\n')
    swap('        if notice==8:\n            assert send(8,"Base","preq",mode,True)==mode\n',
         '        if condition=="late":send(8,probe,"owed","c",probe==mode)\n')
    swap('    if selected and row and header_view and not first_complete:',
         '    if selected and requested and row and header_view and not first_complete:')
    swap('side=2,selection=selected)', 'side=2,selection=selected,seen=seen)')
    ns={"options":options}
    exec(compile(source,str(up/"parent.py"),"exec"),ns)
    return ns

def main():
    up=Path(sys.argv[1])
    s=instrument(up)
    counts={}
    for d,mode,probe,condition,p,q in product(
        (32,33,34),("Q","P"),("Q","P"),("closed","erased","late","rx_full","prep_erased"),(0,1),(0,1)):
        licensed={a for a,yes in (("P",p),("Q",q)) if yes}
        s.update(mode=mode,probe=probe,condition=condition,p_debit=d,licensed=licensed)
        with tempfile.TemporaryDirectory() as scratch:
            v=s["trial"](Path(scratch),"after-commit","after-witness-commit",True,True,140,"split")
        expect=(condition=="closed" and mode in licensed and
                (mode=="Q" or d+int(probe=="P")<=33))
        assert bool(v["apply"])==expect and v["side"]==2
        if expect:
            assert v["result"]=={"status":"cached","tick":8,"result":[1,0]}
        tape=v["radio"]
        probes=[z for z in tape if z[1:4]==(probe,"owed",1)]
        assert len(probes)==1 and probes[0][4]==1
        assert probes[0][-1]==(mode==probe and condition not in ("erased","rx_full"))
        results=[z for z in tape if z[2:4]==("owed",173)]
        assert len(results)==int(expect)
        if expect:assert results[0][1]==mode and results[0][-2:]==(173,True)
        assert len([z for z in tape if z[1:4]==("Q","extra",4) and z[-1]])==2
        assert v["seen"]==("+" if condition not in ("erased","late","rx_full") and mode==probe
                           else "-" if condition in ("closed","prep_erased") else "?")
        key="/".join((probe,condition,str(d)))
        counts.setdefault(key,[0,0])
        counts[key][0]+=1
        counts[key][1]+=int(expect)
    s["air"].stdin.close()
    assert s["air"].wait()==0
    print(json.dumps({"runs":sum(v[0] for v in counts.values()),"cases":counts},sort_keys=True))
if __name__=="__main__":main()
