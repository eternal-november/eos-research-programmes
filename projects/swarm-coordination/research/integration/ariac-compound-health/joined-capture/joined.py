from collections import Counter
from hashlib import sha1
import importlib.util
from itertools import product
from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory
import sys,sqlite3
here=Path(__file__).resolve().parent
base=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else here.parent/'qualified-pose'
b=(base/'guard.py').read_bytes()
assert sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()=="868ef54aaca2d83c16e29aae74cff7aecc604caf"
spec=importlib.util.spec_from_file_location('g',base/'guard.py')
g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
rows=[];cases=[]
for good,healthy,ready,delayed_raw,epoch_ok,park_ok,missing_second in product((False,True),repeat=7):
    case=(good,healthy,ready,delayed_raw,epoch_ok,park_ok,missing_second)
    k=len(cases)*2
    # Ordinary public timestamp is chosen at the wrapper invocation (11);
    # same modeled target producer binds copy to the actual invocation of
    # native capture 8 or 10. Ground truth comes from that capture.
    rows += [
        f'{k} {int(healthy)} {10 if good else 8} 11 {int(ready)} {int(not delayed_raw)} {8 if park_ok else 9} {0 if epoch_ok else 1}',
        f'{k+1} 1 13 13 {int(not missing_second)} 1 8 0']
    cases.append(case)
def emit():
    p=run([sys.executable,here/'emit.py',base],input='\n'.join(rows)+'\n',text=True,capture_output=True,check=True)
    events={}
    for line in p.stdout.splitlines():
        k,n,*raw=map(int,line.split())
        assert n in (0,1) and len(raw)==n*5
        events[k]=tuple(raw) if n else None
    return events
def capture_qualified(db,name,producer,park,tick,payload,auth):
    with sqlite3.connect(db) as c:
        c.execute('BEGIN IMMEDIATE')
        active,current_park,current_auth=c.execute(
            'SELECT mode,park,auth FROM control WHERE name=?',(name,)).fetchone()
        expected=c.execute('SELECT producer,park FROM duty WHERE name=?',(name,)).fetchone()
        if not active or (producer,park)!=expected or (park,auth)!=(current_park,current_auth):
            return False
        old=c.execute('SELECT auth,tick FROM published WHERE key=?',(name,)).fetchone()
        if old is None or old<(auth,tick):
            c.execute('INSERT OR REPLACE INTO published VALUES (?,?,?,?,?,?)',
                      (name,producer,park,tick,payload,auth))
            return True
        return False
ev=emit()
stats=Counter()
for i,case in enumerate(cases):
    good,healthy,ready,delayed_raw,epoch_ok,park_ok,missing_second=case
    first,second=ev[2*i],ev[2*i+1]
    assert bool(first)==(healthy and ready)
    assert bool(second)==(not missing_second)
    with TemporaryDirectory() as t:
        db=Path(t)/'service.sqlite'
        g.init(db)
        # B is a separate prequalified order with its own slot; no new
        # public frame for B is assumed during A's denied publication.
        g.capture(db,'B',5,8,10,77)
        if first:
            _,p,tick,park,auth=first
            assert p==1000+tick
            capture_qualified(db,'A',5,park,tick,p,auth)
        # Standalone direct legality from actual source events, not guard state.
        def valid(event,t):
            return event and event[3:]==(8,0) and 10<=event[2]<=t<=event[2]+4
        got=g.service(db,'A','request',11)
        first_good=bool(good and healthy and ready and park_ok and epoch_ok)
        assert first_good==bool(valid(first,11))
        assert got==(('ok',1010) if first_good else ('defer',))
        # Publication header-only release may spend the sole read on a pose
        # captured before the cutoff. Count only cases with compatible
        # scope, separating timing and authority obstructions.
        header_legal=bool(first and first[3:]==(8,0) and first[0]>=10)
        stats['header_alias']+=header_legal and not first_good
        if second:
            _,p,tick,park,auth=second
            assert p==1000+tick
            capture_qualified(db,'A',5,park,tick,p,auth)
        r=g.service(db,'A','request',13)
        direct=next((e for e in (first,second) if valid(e,e[0] if e else 13)),None)
        assert r==(('ok',direct[1]) if direct else ('defer',))
        assert g.service(db,'B','old',13)==('ok',77)
        stats['kept_first']+=first_good
        stats['repaired']+=not first_good and bool(second)
        stats['honest_noncompletion']+=not first_good and not second
assert stats['kept_first']+stats['repaired']+stats['honest_noncompletion']==len(cases)
print(f"{len(cases)} native-to-ledger joined traces; {stats['kept_first']} kept a qualified first result; "
      f"{stats['repaired']} waited and qualified later; {stats['honest_noncompletion']} lacked an authorized pose")
print(f"{stats['header_alias']} matched identities where header-only admission differs; every old B read preserved")
# Source can be a qualified feed under a different authorization context
# without its capture being admissible for this pending receiver duty.
# Cache one global maximum incorrectly loses the current-scope next frame.
i=next(i for i,c in enumerate(cases) if c==(True,True,True,False,False,True,False))
with TemporaryDirectory() as t:
    db=Path(t)/'frontier.sqlite';g.init(db)
    for frame in (ev[2*i],ev[2*i+1]):
        _,p,tick,park,auth=frame
        g.capture(db,'A',5,park,tick,p,auth)
    assert g.service(db,'A','request',13)==('defer',)
    row=sqlite3.connect(db).execute("SELECT tick,auth FROM published WHERE key='A'").fetchone()
    assert row==(10,1)
print('Early wrong-scope publication poisoned the unscoped cache; the scoped frontier admitted the later valid frame.')
