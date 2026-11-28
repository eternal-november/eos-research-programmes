"""Factor early-slot use and the exact wire format on native routes."""
import json,sys,tempfile
from itertools import product
from pathlib import Path
from core import Event,Use,Row,admitted
import supplier659 as base
from codec import restore,omit,canonical,mutated,codec_audit

def select(chunks,arm,d,licensed,horizon,fmt):
    seen=frozenset(chunks)
    support=[seen] if horizon!="near-possible" else [seen,seen & {"Q"}]
    suffix=(165 if fmt=="compact" else 173)-int(arm=="reuse")
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
         '    full=json.loads(fragment)\n'
         '    send_fragment=nat.encode(omit(full)) if fmt=="compact" else fragment\n'
         '    assert len(send_fragment)==(165 if fmt=="compact" else 173)\n'
         '    offset=95 if fmt=="compact" else 165\n'
         '    assert send_fragment[offset].isdigit(),repr(send_fragment)\n'
         '    assert send_fragment[offset-1]=="["\n'
         '    if condition in ("wrong-key","no-join","mutated-value"):\n'
         '        modified=nat.encode(mutated(json.loads(send_fragment),condition))\n'
         '        assert len(modified)==len(send_fragment)\n'
         '        send_fragment=modified\n'
         '    piece=send_fragment[offset] if protocol=="reuse" else "c"\n'
         '    if condition=="corrupt":piece="9" if piece!="9" else "8"\n'
         '    chunks={}\n'
         '    if before:assert ask("relay",7,before)==str(int(before!="moving"))\n'
         '    for sender in ("Q","P"):\n'
         '        val=send(7,sender,"owed",piece,0 if condition=="erased" else 2,raw=True)\n'
         '        if val is not None:chunks[sender]=val\n'
         '    selected=select(chunks,protocol,p_debit,licensed,horizon,fmt)\n'
         '    if after:assert ask("relay",7,after)=="1"\n')
    swap('                requested=send(7,"Base",command,"d?",True)=="d?"\n'
         '                assert requested\n',
         '                requested=send(7,"Base",command,"d?",condition!="prep_erased")=="d?"\n')
    swap('        if notice==8:\n            assert send(8,"Base","preq",mode,True)==mode\n','')
    swap('            late=send(8,permitted,"owed",fragment if requested else row[0],\n'
         '                      permitted==mode)\n',
         '            wire=send_fragment if protocol=="plain" else send_fragment[:offset]+send_fragment[offset+1:]\n'
         '            later=send(8,permitted,"owed",wire,2,raw=True)\n'
         '            if later:\n'
         '                if protocol=="reuse":later=later[:offset]+chunks[permitted]+later[offset:]\n'
         '                seen_suffix=True\n'
         '                try:\n'
         '                    val=json.loads(later)\n'
         '                    late=restore(val) if fmt=="compact" else val\n'
         '                    if condition=="closed":assert nat.encode(late)==fragment\n'
         '                    decoded_suffix=True\n'
         '                except (ValueError, TypeError):late=None\n')
    swap('    if selected and row and header_view and not first_complete:',
         '    if selected and requested and row and header_view and not first_complete and condition=="closed" and horizon!="assume":')
    swap('    step(7)\n','    seen_suffix=decoded_suffix=False\n    step(7)\n')
    swap('side=2,selection=selected)','side=2,selection=selected,chunks=tuple(chunks),suffix=seen_suffix,decoded=decoded_suffix,offset=offset)')
    ns={"select":select,"restore":restore,"omit":omit,"mutated":mutated}
    exec(compile(source,str(up/"parent.py"),"exec"),ns)
    return ns


SCENARIOS=(
 ("P",None,None,"stable",("P",)),
 ("Q","near",None,"stable",("Q",)),
 ("both","far",None,"stable",("Q","P")),
 ("late-near",None,"near","assume",("P",)),
 ("guard-near",None,"near","near-possible",("P",)),
)
CONTROLS=("closed","erased","prep_erased","corrupt","wrong-key","no-join","mutated-value")
BOUND={"full":{"plain":32,"reuse":33},"compact":{"plain":40,"reuse":41}}

def main():
    up=Path(sys.argv[1]); s=instrument(up); counts={}; focal={}
    for (name,before,after,horizon,sources),d,fmt,protocol,condition in product(
            SCENARIOS,(32,33,34,40,41,42),BOUND,("plain","reuse"),CONTROLS):
        # All negative wire controls in the two opposed stable native branches.
        # Other branches vary potential topology, holding the archive clean.
        if name not in ("P","Q") and condition!="closed":continue
        if d not in (33,40,41) and condition!="closed":continue
        if condition=="corrupt" and protocol=="plain":continue
        if condition=="no-join" and fmt!="compact":continue
        s.update(before=before,after=after,horizon=horizon,protocol=protocol,fmt=fmt,
                 condition=condition,p_debit=d,licensed={"P","Q"})
        with tempfile.TemporaryDirectory() as root:
            v=s["trial"](Path(root),"after-commit","after-witness-commit",True,True,140,"split")
        admissible=[p for p in sources if p=="Q" or d<=BOUND[fmt][protocol]]
        expected=admissible[0] if admissible and name!="guard-near" and condition!="erased" else None
        sent=bool(expected and condition!="prep_erased")
        delivered=sent and name!="late-near"
        decoded=delivered and condition!="no-join"
        applied=decoded and condition=="closed"
        assert (v["selection"][0] if v["selection"] else None)==expected
        assert bool(v["suffix"])==delivered and bool(v["decoded"])==decoded,(name,d,fmt,protocol,condition,v,delivered,decoded)
        assert bool(v["apply"])==applied and v["side"]==2
        if applied:assert v["result"]=={"status":"cached","tick":8,"result":[1,0]}
        tape=v["radio"]
        early=[z for z in tape if z[0]==7 and z[2:4]==("owed",1)]
        assert [z[1] for z in early]==["Q","P"] and all(z[4]==1 for z in early)
        assert v["chunks"]==(() if condition=="erased" else sources)
        suffix=[z for z in tape if z[0]==8 and z[2]=="owed"]
        assert len(suffix)==int(sent)
        if sent:
            wire_len=(165 if fmt=="compact" else 173)-int(protocol=="reuse")
            assert suffix[0]==(8,expected,"owed",wire_len,wire_len,delivered)
        second=[z[0] for z in tape if z[1:4]==("Q","extra",4) and z[-1]]
        assert second==[6,10 if expected is None or (expected=="Q" and fmt=="full") else 7]
        state=counts.setdefault("/".join((name,fmt,protocol,condition)),[0]*7)
        for i,val in enumerate((True,sent,delivered,decoded,applied,second[-1]==7,
                                decoded and not applied)):
            state[i]+=int(val)
        if condition=="closed" and name in ("P","Q"):
            focal["/".join((name,fmt,protocol,str(d)))]=[int(applied),second[-1]]
    s["air"].stdin.close()
    assert s["air"].wait()==0
    print(canonical(dict(runs=sum(v[0] for v in counts.values()),codec=codec_audit(),
                         cases=counts,focal=focal)))
if __name__=="__main__":main()
