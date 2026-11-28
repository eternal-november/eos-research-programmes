from collections import Counter
import importlib.util
from itertools import product
from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory
import sys

p=Path(__file__).resolve().parent
root=Path(sys.argv[1]) if len(sys.argv)>1 else p.parent
def records(cmd,lines):
    q=run(cmd,input='\n'.join(lines)+'\n',capture_output=True,text=True,check=True)
    return [tuple(map(int,s.split())) for s in q.stdout.splitlines()]
trace=records([sys.executable,p/'submission.py',root/'submission-cut'],
              [f'{i} {s} {rf} {cf}' for i,(s,rf,cf) in enumerate(product(range(10),(0,1),(0,1)))])
clock={}
for i,t,ann,floor,lcam in trace:
    s,rf,cf=list(product(range(10),(0,1),(0,1)))[i]
    clock[s,rf,cf,t]=ann,floor,lcam
    assert (ann,floor,lcam)==(int(t>s),int(t<=s or not rf),int(t<=s or not cf))
cam_cases=list(product((0,1),range(1,7),(0,1)))
rows=[]
for i,(health,t,ready) in enumerate(cam_cases):
    rows.append(f'{i} {health} {t} {t} {ready} 1 8 0')
pub={}
for i,n,*data in records([sys.executable,root/'joined-capture'/'emit.py',root/'qualified-pose'],rows):
    cam=cam_cases[i]
    assert n==int(cam[0] and cam[2])
    pub[cam]=tuple(data) if n else None
s=importlib.util.spec_from_file_location('guard',root/'qualified-pose'/'guard.py')
g=importlib.util.module_from_spec(s);s.loader.exec_module(g)

def actual(case,slot):
    t,q,D,rf,cf,effect_lost,sage,pre=case
    _,_,h=clock[slot,rf,cf,t]
    event=pub[h,t,1]
    ann=slot+1
    floor_ok=all(clock[slot,rf,cf,k][1] for k in range(q+1))
    ready=max(t,ann)
    correct=bool(event) and t>=sage and (pre or t>=ann) and not effect_lost
    return bool(correct and floor_ok and ready<=D and ready-t<=4),event,ready

def observed_prefix(case):
    t,_,D,rf,cf,_,_,_=case
    for now in range(D):
        evt=pub[clock[9,rf,cf,now][2],now,1] if now==t else None
        yield now,evt

def decide(old_floor_due,D,rf,cf,sage,pre,observations):
    # The schedule supplying these observations is not a controller input.
    # It only sees the current ordinary public event, if any.
    start=old_floor_due if rf else 0
    last=None
    for now,evt in observations:
        if evt and evt[2]>=sage:last=evt[2]
        if now>=D:break
        if now<start:continue
        if not cf:return now
        if pre and last is not None and now+1-last<=4:return now
    return None

def main():
    # Moving the recipient after announcement is a modeled effect-side
    # invalidation, not attributed to an actual robot motion in ARIAC.
    stats=Counter()
    for case in product(range(1,7),(0,2,4),(2,4,6,8),(0,1),(0,1),(0,1),(1,), (0,1)):
        t,q,D,rf,cf,lost,sage,pre=case
        chosen=decide(q,D,rf,cf,sage,pre,observed_prefix(case))
        direct=[s for s in range(D) if actual(case,s)[0]]
        policy=False if chosen is None else actual(case,chosen)[0]
        # Both methods may fail actual effect if the explicit final fault moved
        # the tray; the decision earlier does not know that it will occur.
        assert policy==bool(direct),(case,chosen,direct)
        if chosen is not None and not lost:
          assert chosen==min(direct) if direct else not policy
        stats['conditions']+=1
        stats['positives']+=policy
        stats['blackout_positives']+=cf and policy
        stats['positive_lost_by_eager']+=policy and not actual(case,0)[0]
        if chosen is None:continue
        verdict,e,ready=actual(case,chosen)
        with TemporaryDirectory() as td:
            db=Path(td)/'fixture.sqlite'
            g.init(db)
            # This authored order requires a capture at tick>=1. Nothing
            # in this intended-use validation changes the raw camera.
            with g.sqlite3.connect(db) as c:
                c.execute("UPDATE duty SET earliest=1 WHERE name='A'")
            g.capture(db,'B',5,8,1,77) # prequalified independent old duty
            assert g.service(db,'B','q-other',1)==('ok',77)
            ann=chosen+1
            assert clock[chosen,rf,cf,ann][0]
            if e and (pre or t>=ann):
                _,payload,capture,park,auth=e
                g.capture(db,'A',5,park,capture,payload,auth)
            if lost:g.set_control(db,1,9)
            reply=g.service(db,'A','named-new',ready) if ready<=D else ('defer',)
            assert (reply[0]=='ok')==verdict,(case,reply,chosen)
    print(dict(sorted(stats.items())))
    print(f'{len(trace)} native submission states; {len(pub)} native camera source types')
if __name__=='__main__':main()
