"""Actual receiver callbacks and reuse of an early byte of the named suffix."""
import json,sys,tempfile
from itertools import product
from pathlib import Path
from core import Event,Use,Row,admitted
import supplier659 as base

def select(chunks,arm,d,licensed,horizon):
    seen=frozenset(chunks)
    support=[seen] if horizon!="near-possible" else [seen,seen & {"Q"}]
    suffix=172 if arm=="reuse" else 173
    def e(t,o,who,n,paid=(),needs=()):
        return Event(t,o,need=frozenset(needs),uses=(Use((who,),n,320,4),),paid=paid)
    fixed=(e(5,0,"Q",140),e(5,1,"P",d),e(6,0,"P",114),e(6,1,"Q",4,("diagnostic-1",)),
           e(7,0,"Q",1),e(7,1,"P",1))
    choices={(s,b):(e(8,0,s,suffix,("old",),(("ready",s),("licensed",s))),
                    e(b,3,"Q",4,("diagnostic-2",))) for s,b in base.OPTIONS}
    view=((7,"entry",tuple(sorted(seen))),)
    rows=[Row(view,frozenset({("ready",s) for s in possibilities}|{("licensed",x) for x in licensed}),fixed,choices)
          for possibilities in support]
    out=next(iter(admitted(rows,"entry",7,base.DUES,base.OPTIONS).values()))
    expected=tuple((s,b) for s,b in base.OPTIONS if s in seen and all(s in f for f in support) and s in licensed and
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
    swap('subprocess.Popen([sys.argv[2]],','subprocess.Popen(sys.argv[2:4],')
    swap('send(6,"P","owed",header,early_link)','send(6,"P","owed",header,2)')
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
         '    if before:assert ask("relay",7,before)==str(int(before!="moving"))\n'
         '    for sender in ("Q","P"):\n'
         '        val=send(7,sender,"owed",piece,0 if condition=="erased" else 2,raw=True)\n'
         '        if val is not None:chunks[sender]=val\n'
         '    selected=select(chunks,protocol,p_debit,licensed,horizon)\n'
         '    if after:assert ask("relay",7,after)=="1"\n')
    swap('                requested=send(7,"Base",command,"d?",True)=="d?"\n'
         '                assert requested\n',
         '                requested=send(7,"Base",command,"d?",condition!="prep_erased")=="d?"\n')
    swap('        if notice==8:\n            assert send(8,"Base","preq",mode,True)==mode\n','')
    swap('            late=send(8,permitted,"owed",fragment if requested else row[0],\n'
         '                      permitted==mode)\n',
         '            wire=fragment if protocol=="plain" else fragment[:offset]+fragment[offset+1:]\n'
         '            later=send(8,permitted,"owed",wire,2,raw=True)\n'
         '            if later:\n'
         '                if protocol=="reuse":later=later[:offset]+chunks[permitted]+later[offset:]\n'
         '                late=json.loads(later)\n')
    swap('    if selected and row and header_view and not first_complete:',
         '    if selected and requested and row and header_view and not first_complete and condition!="corrupt" and horizon!="assume":')
    swap('side=2,selection=selected)','side=2,selection=selected,chunks=tuple(chunks))')
    ns={"select":select}
    exec(compile(source,str(up/"parent.py"),"exec"),ns)
    return ns

# Intentionally held-in, not independent case selection. "assume" tests a
# false continuity declaration against a late native registration.
SCENARIOS=(
 ("none",None,None,"stable",("P",)),
 ("moving","moving",None,"stable",("P",)),
 ("near","near",None,"stable",("Q",)),
 ("far","far",None,"stable",("Q","P")),
 ("stale-near",None,"near","assume",("P",)),
 ("open-near",None,None,"near-possible",("P",)),
 ("guard-near",None,"near","near-possible",("P",)),
 ("late-far",None,"far","stable",("P",)),
)
def main():
    up=Path(sys.argv[1]); s=instrument(up); counts={}; prefixes={}
    for (name,before,after,horizon,observed),d,protocol,condition in product(
       SCENARIOS,(32,33,34),("reuse","plain"),("closed","erased","prep_erased","corrupt","noP")):
        if condition=="corrupt" and protocol=="plain":continue
        licensed={"Q"} if condition=="noP" else {"Q","P"}
        s.update(before=before,after=after,horizon=horizon,protocol=protocol,
                 condition=condition,p_debit=d,licensed=licensed)
        with tempfile.TemporaryDirectory() as root:
            v=s["trial"](Path(root),"after-commit","after-witness-commit",True,True,140,"split")
        assert v["side"]==2 and v["chunks"]==(() if condition=="erased" else observed),(name,condition,v)
        admissible=[p for p in observed if p in licensed and
                    (p=="Q" or d+int(protocol=="plain")<=33)]
        if condition=="erased" or horizon=="near-possible":admissible=[]
        expected=admissible[0] if admissible else None
        assert (v["selection"][0] if v["selection"] else None)==expected
        payable=expected and condition!="prep_erased"
        delivered=payable and name!="stale-near"
        settled=bool(delivered and condition!="corrupt")
        assert bool(v["apply"])==settled,(name,d,protocol,condition,v)
        if settled:assert v["result"]=={"status":"cached","tick":8,"result":[1,0]}
        tape=v["radio"]
        assert (6,"P","owed",114,114,True) in tape
        prefixes[name,d,protocol,condition]=[z for z in tape if z[0]<8]
        early=[z for z in tape if z[0]==7 and z[2:4]==("owed",1)]
        assert [z[1] for z in early]==["Q","P"] and all(z[4]==1 for z in early)
        later=[z for z in tape if z[0]==8 and z[2]=="owed"]
        assert len(later)==int(bool(payable)),(name,d,protocol,condition,v)
        if payable:
            n=172+int(protocol=="plain")
            assert later[0][1]==expected and later[0][3:]==(n,n,bool(delivered))
        assert len([z for z in tape if z[1:4]==("Q","extra",4) and z[-1]])==2
        key="/".join((name,protocol))
        counts.setdefault(key,[0,0,0,0])
        counts[key][0]+=1
        counts[key][1]+=int(settled)
        counts[key][2]+=len(later)
        counts[key][3]+=int(bool(payable and not delivered))
    for d,protocol,condition in product((32,33,34),("reuse","plain"),
                                        ("closed","erased","prep_erased","corrupt","noP")):
        if condition=="corrupt" and protocol=="plain":continue
        def pfx(name):return prefixes[name,d,protocol,condition]
        assert pfx("none")==pfx("stale-near")==pfx("late-far")==pfx("moving")
        assert pfx("guard-near")==pfx("open-near")
    s["air"].stdin.close()
    assert s["air"].wait()==0
    print(json.dumps(dict(runs=sum(v[0] for v in counts.values()),cases=counts),sort_keys=True))
if __name__=="__main__":main()
