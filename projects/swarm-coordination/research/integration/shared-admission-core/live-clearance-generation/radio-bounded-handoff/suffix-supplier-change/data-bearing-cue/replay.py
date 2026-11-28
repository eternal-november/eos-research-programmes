"""Actual receiver callbacks and reuse of an early byte of the named suffix."""
import json,sys,tempfile
from itertools import product
from pathlib import Path
from core import Event,Use,Row,admitted
import supplier659 as base

def select(chunks,arm,d,licensed):
    if len(chunks)!=1:return None
    auth=next(iter(chunks))
    suffix=172 if arm=="reuse" else 173
    def e(t,o,who,n,paid=(),needs=()):
        return Event(t,o,need=frozenset(needs),uses=(Use((who,),n,320,4),),paid=paid)
    fixed=(e(5,0,"Q",140),e(5,1,"P",d),e(6,0,"P",114),e(6,1,"Q",4,("diagnostic-1",)),
           e(7,0,"Q",1),e(7,1,"P",1))
    choices={(s,b):(e(8,0,s,suffix,("old",),(("ready",s),("licensed",s))),
                    e(b,3,"Q",4,("diagnostic-2",))) for s,b in base.OPTIONS}
    row=Row(((7,"entry",auth),),frozenset({("ready",auth)}|{("licensed",x) for x in licensed}),fixed,choices)
    out=next(iter(admitted([row],"entry",7,base.DUES,base.OPTIONS).values()))
    expected=tuple((s,b) for s,b in base.OPTIONS if s==auth and s in licensed and
                 (145+suffix+4*(b==7)<=320 if s=="Q" else d+115+suffix<=320))
    assert out==expected
    return out[0] if out else None

def instrument(up):
    runner=base.load_runner(up/"feedback.py")
    original=getattr(base,"compile",compile)
    source=""
    def hook(text,file,kind):
        nonlocal source
        source=text
        return compile("",file,kind)
    base.compile=hook
    try:base.instrument(up/"parent.py",runner)
    finally:base.compile=original
    def swap(a,b):
        nonlocal source
        assert source.count(a)==1,a
        source=source.replace(a,b)
    swap('    schedule=(6,0)\n','    schedule=(6,10)\n')
    swap('    def send(t,src,dst,text,link=True):','    def send(t,src,dst,text,link=True,raw=False):')
    swap('if dst=="owed" and text[0]=="{" else result',
         'if dst=="owed" and text[0]=="{" and not raw else result')
    swap('    observed=send(7,"Base","preq",mode,int(notice==7))\n'
         '    received=((7,observed),) if observed else ()\n'
         '    feasible=plan.get(received,())\n'
         '    selected=feasible[0] if feasible else None\n',
         '    # Fixed payload layout for this protocol and declared archive schema.\n'
         '    offset=165\n'
         '    assert fragment[offset].isdigit(),repr(fragment)\n'
         '    assert len(fragment)==173\n'
         '    assert fragment[offset-1]=="["\n'
         '    piece=fragment[offset] if protocol=="reuse" else "c"\n'
         '    if condition=="corrupt":piece="9" if piece!="9" else "8"\n'
         '    chunks={}\n'
         '    for sender in ("Q","P"):\n'
         '        val=send(7,sender,"owed",piece,(sender==mode or condition=="both") and condition!="erased",raw=True)\n'
         '        if val is not None:chunks[sender]=val\n'
         '    selected=select(chunks,protocol,p_debit,licensed)\n')
    swap('                requested=send(7,"Base",command,"d?",True)=="d?"\n'
         '                assert requested\n',
         '                requested=send(7,"Base",command,"d?",condition!="prep_erased")=="d?"\n')
    swap('        if notice==8:\n            assert send(8,"Base","preq",mode,True)==mode\n','')
    swap('            late=send(8,permitted,"owed",fragment if requested else row[0],\n'
         '                      permitted==mode)\n',
         '            wire=fragment if protocol=="plain" else fragment[:offset]+fragment[offset+1:]\n'
         '            later=send(8,permitted,"owed",wire,permitted==mode,raw=True)\n'
         '            if later:\n'
         '                if protocol=="reuse":later=later[:offset]+chunks[permitted]+later[offset:]\n'
         '                late=json.loads(later)\n')
    swap('    if selected and row and header_view and not first_complete:',
         '    if selected and requested and row and header_view and not first_complete and condition!="corrupt":')
    swap('side=2,selection=selected)','side=2,selection=selected,chunks=tuple(chunks))')
    ns={"select":select}
    exec(compile(source,str(up/"parent.py"),"exec"),ns)
    return ns

def main():
    up=Path(sys.argv[1]); s=instrument(up); counts={}
    for d,mode,protocol,condition in product((32,33,34),("Q","P"),("reuse","plain"),
                                            ("closed","erased","both","prep_erased","corrupt","unlicensed")):
        if condition=="corrupt" and protocol=="plain":continue
        licensed={"P","Q"}-{mode} if condition=="unlicensed" else {"P","Q"}
        s.update(mode=mode,protocol=protocol,condition=condition,p_debit=d,licensed=licensed)
        with tempfile.TemporaryDirectory() as root:
            v=s["trial"](Path(root),"after-commit","after-witness-commit",True,True,140,"split")
        fits=mode=="Q" or d+int(protocol=="plain")<=33
        expected=condition=="closed" and fits
        assert bool(v["apply"])==expected and v["side"]==2
        if expected:assert v["result"]=={"status":"cached","tick":8,"result":[1,0]}
        tape=v["radio"]
        early=[z for z in tape if z[0]==7 and z[2:4]==("owed",1)]
        assert [z[1] for z in early]==["Q","P"] and all(z[4]==1 for z in early)
        assert sum(z[-1] for z in early)==(0 if condition=="erased" else 2 if condition=="both" else 1)
        later=[z for z in tape if z[0]==8 and z[2]=="owed"]
        final=condition in ("closed","corrupt") and fits
        assert len(later)==int(final)
        if final:assert later[0][1]==mode and later[0][3:]==(172+int(protocol=="plain"),172+int(protocol=="plain"),True)
        assert len([z for z in tape if z[1:4]==("Q","extra",4) and z[-1]])==2
        key="/".join((protocol,condition,str(d)))
        counts.setdefault(key,[0,0])
        counts[key][0]+=1
        counts[key][1]+=int(expected)
    s["air"].stdin.close()
    assert s["air"].wait()==0
    print(json.dumps(dict(runs=sum(v[0] for v in counts.values()),cases=counts,offset=165),sort_keys=True))
if __name__=="__main__":main()
