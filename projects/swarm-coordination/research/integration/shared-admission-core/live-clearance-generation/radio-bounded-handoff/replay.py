"""Freeze, independent archival cut, actual application delivery, and local retry."""
from collections import Counter
from contextlib import closing
from itertools import product
import json
from pathlib import Path
import subprocess
import sys
import tempfile

def load(path, marker):
    text=path.read_text()
    assert text.count(marker)==1
    ns={}
    exec(compile(text.split(marker)[0],str(path),"exec"),ns)
    return ns

up=Path(sys.argv[1])
prior=load(up/"silent.py",'\nif len(sys.argv)>2:\n')
station=prior["scope"]
nat=prior["native"]
air=subprocess.Popen([sys.argv[2]],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True,bufsize=1)

def ask(*a):
    air.stdin.write(" ".join(map(str,a))+"\n")
    air.stdin.flush()
    return air.stdout.readline().strip()

def trial(root,phase,crash,early_link,late_link,q_debit,arm):
    assert ask("reset")=="ok"
    src=root/"donor.db"
    dst=root/"receiver.db"
    station["init"](src,True)
    assert station["transfer"](src,dst)==32768
    with closing(station["open_station"](dst)) as d:basis=station["tag"](d)
    prior["retry_old"](src,phase)
    w=subprocess.run([sys.executable,"-B",str(up/"silent.py"),str(up),"export",
                      str(root),crash,"suffix",basis],capture_output=True,text=True)
    assert w.returncode==73 and not w.stdout,w.stderr
    # The application cannot fall back to querying this file. The independent
    # archive, not the evaluator, supplies any actual wire payload.
    h=root/"offline"
    h.mkdir()
    for f in root.glob("donor.db*"):f.rename(h/f.name)
    assert not src.exists()
    with closing(prior["open_witness"](root/"envelope.db")) as ws:
        row=ws.execute("select effect_cut from seen where id=1").fetchone()
    if row:
        packet=json.loads(row[0])
        assert len(row[0]) in (240,286)
        s_fields={"old_epoch","closed","digest","tick"}
        header=nat.encode({k:v for k,v in packet.items() if k in s_fields})
        fragment=nat.encode({k:v for k,v in packet.items() if k not in s_fields})
        assert len(header)==114 and len(row[0])==len(header)+len(fragment)-1

    tape=[]
    def send(t,src,dst,text,link=True):
        result,charge=ask("send",t,src,dst,text,int(link)).split()
        assert result in (text,"-") and int(charge) in (len(text),0)
        tape.append((t,src,dst,len(text),int(charge),result!="-"))
        return None if result=="-" else json.loads(result) if dst=="owed" and text[0]=="{" else result

    # This actual prior competing report occupies the common receiver window.
    assert send(3,"Side","owed","q"*130)
    side=nat.iso.make(nat.n,False)
    def step(t):
        assert ask("side",t)=="1"
        nat.n.step(side,[nat.A.NOOP.value,nat.A.FORWARD.value])
    step(4)
    if q_debit:
        assert not send(5,"Q","sink","q"*q_debit,False)
        assert tape[-1][4]==q_debit
    header_view=None
    result=None
    first_complete=None
    def use(candidate,t):
        if not candidate:return False
        direct=prior["direct_adequacy"](dst,basis,candidate)
        actual=prior["recovered_prefix"](dst,basis,candidate)
        assert direct==actual
        if not (direct if arm=="direct" else actual):return False
        assert station["install"](dst,candidate["digest"],True)
        assert station["world_has_right"](dst)
        return t
    if row:
        if arm=="whole":
            whole=send(6,"P","owed",row[0],early_link)
            first_complete=use(whole,6)
        else:
            header_view=send(6,"P","owed",header,early_link)
            first_complete=use(header_view,6)
    if first_complete:
        result=prior["restart"](dst)
    step(7)
    if row and not first_complete:
        requested=False
        if header_view:
            requested=send(7,"Base","preq","d?",True)=="d?"
            assert requested
        late=send(8,"Q","owed",fragment if requested else row[0],late_link)
        maybe=(header_view|late if late and header_view else late)
        first_complete=use(maybe,8)
        if first_complete:result=prior["restart"](dst)
    if result:
        assert result=={"status":"cached" if phase=="after-commit" else "applied",
                        "tick":8,"result":[1,0]}
    else:
        with closing(station["open_station"](dst)) as d:assert station["tag"](d)==basis
    assert (side.agents[1].x,side.agents[1].y)==(3,1)
    return dict(apply=first_complete or None,result=result,radio=tape,
                charged=sum(x[4] for x in tape)+2,side=2)

def main():
    totals={}
    witness={}
    arms=("whole","split","direct")
    modes=product(("after-stage","after-commit"),("after-fence","after-witness-commit"),
                  (0,1),(0,1),(0,140,147,148))
    for phase,crash,p,q,debit in modes:
        a=(phase,crash,p,q,debit)
        rows={}
        for arm in arms:
            with tempfile.TemporaryDirectory() as d:
                x=rows[arm]=trial(Path(d),*a,arm)
            totals.setdefault(arm,Counter()).update(cases=1,side=2,charged=x["charged"],
                timely=int(bool(x["apply"])),early=int(x["apply"]==6))
        assert rows["split"]==rows["direct"]
        if p and q and ((crash=="after-fence" and debit==140) or
                        (crash=="after-witness-commit" and debit in (0,140,147,148))):
            witness["/".join(map(str,a))]=rows
    x=witness["after-commit/after-witness-commit/1/1/140"]
    assert x["whole"]["apply"] is None and x["split"]["apply"]==8
    x=witness["after-stage/after-witness-commit/1/1/140"]
    assert x["whole"]["apply"] is None and x["split"]["apply"]==6
    air.stdin.close()
    assert air.wait()==0
    print(json.dumps({"totals":totals,"witness":witness},sort_keys=True))

main()
