"""Shared-lane recovery workload on the pinned tick/event platform."""
from pathlib import Path
from hashlib import sha256
from collections import defaultdict
from itertools import product
from types import ModuleType
import json

HERE = Path(__file__).parent
def exact(file, digest):
    raw = (HERE / file).read_bytes()
    assert sha256(raw).hexdigest() == digest
    return raw.decode()
original_text = exact('primary_original.py','b540ced5fd26a41b287dd24e18c20fe7e53629bf061b4625f3a8ba9850397e04')
primary_text = exact('primary_replay.py','88747bf5cd3e86b3ef8f1a97a5f48b7c47cff63b45309dd2507af4f5e084a1ac')
original = ModuleType('original')
exec(compile(original_text, 'primary_original.py', 'exec'), original.__dict__)
primary_text = primary_text.replace('from original import setup, run as original_run','')
base = dict(setup=original.setup,original_run=original.run,__name__='primary')
exec(compile(primary_text, 'primary_replay.py', 'exec'), base)
primary = base['simulate']
# Add plant-side inspection service and resource guard. Physical support,
# authorization, root worker and endpoint reservation laws stay pinned.
def once(s,a,b):
    assert s.count(a)==1,a
    return s.replace(a,b,1)
p = once(primary_text,'    obs = defaultdict(list)','''    obs = defaultdict(list)
    cell = None
    inspection = None
    inspect_completed = None
    retry = False
    event_lane = []''')
p = once(p,"    event(-1, 'local_root_commitment', token)","""    event(-1, 'local_root_commitment', token)
    event(-1, 'inspection_commitment', 3, 4, "rack3")""")
p = once(p,'        if t == 0:\n', '''        if cell is not None and cell[1] == t:
            event(t,'lane_release',cell[0])
            cell = None
        if inspection == t:
            event(t,'inspection_accept',3)
            inspect_completed = t
            inspection = None
        if t == 1:
            assert stock[3] == 3 and cell is None
            if dwell_fault:
                obs[3].append([t,'failed_inspection_start','head_jam'])
                event(t,'inspection_jam_observed',3)
                retry = True
            else:
                event(t,'inspection_start',3)
                obs[3].append([t,'inspection_start','normal_window'])
                inspection = t+1
                cell = ('inspection',t+1)
        if t == 3 and retry:
            assert stock[3] == 3 and cell is None
            event(t,'inspection_retry_start',3)
            obs[3].append([t,'inspection_start','retry_window'])
            inspection = t+1
            cell = ('inspection',t+1)
            retry = False
        if t == 0:
''')
p = once(p,"            if dwell_fault:\n                event(t, 'dwell_fault_onset')\n","")
p = once(p,"            if (t < deadline and auth.get(b)",'''            if b == 2 and b in auth:
                event_lane.append((t, cell))
                obs[b].append([t,'lane_read',cell is None])
            if ((b != 2 or cell is None) and t < deadline and auth.get(b)''')
p = once(p,"                dt = 1 + int(dwell_fault and b == 2)","""                dt = 1
                if b == 2:
                    assert cell is None
                    cell = ('handoff',t+1)
                    event(t,'lane_acquire',1,2)""")
p = once(p,"                final=stock, trace=trace, local=dict(obs), refused=False)","""                final=stock, trace=trace, local=dict(obs), refused=False,
                inspection_completed=inspect_completed, cell_reads=event_lane)""")
ext = dict(setup=original.setup,original_run=original.run,__name__='extension')
exec(compile(p, 'recovery_workload.py', 'exec'), ext)
simulate = ext['simulate']
# A nonproduction mediation control keeps both incident flags and the retry
# schedule, but gives the inspector an independent unit lane.
q = p.replace("assert stock[3] == 3 and cell is None", "assert stock[3] == 3")
q = q.replace("cell = ('inspection',t+1)", "event(t,'acquire_extra_inspection_lane',3)")
assert q != p and q.count("acquire_extra_inspection_lane")==2
separate = dict(setup=original.setup,original_run=original.run,__name__='separate')
exec(compile(q, 'separate_inspection_lane.py', 'exec'), separate)

def reference(live,h,j,early,before,D):
    """Exhaustive schedule candidates, allowing voluntary waiting."""
    upstream = (h and before) if early else (1+h)
    occupied_slot = 3 if j else 1
    candidates=[]
    for root in range(D):
        if root < upstream:
            continue
        if live == 1:
            candidates.append(root+1)
        else:
            for terminal in range(root):
                if terminal>=upstream+1 and terminal!=occupied_slot:
                    candidates.append(root+1)
    return min(candidates,default=None)

def audit(run,j,D):
    pending=None
    done=False
    last=-2
    for t,k,*args in run['trace']:
        assert t>=last; last=t
        if k=='inspection_commitment':
            assert t==-1 and args==[3,4,'rack3']
        if k=='lane_release':
            assert pending==(t,args[0]); pending=None
        if k in ('inspection_start','inspection_retry_start','lane_acquire'):
            assert pending is None
            pending=(t+1,'handoff' if k=='lane_acquire' else 'inspection')
        if k=='inspection_accept':
            assert not done and t==(4 if j else 2); done=True
    assert pending is None and done
    assert run['inspection_completed']==(4 if j else 2) and not run['refused']

def main():
    rows=[]
    for live,early,before,(h,j),D in product((1,2),(False,True),(True,False),base['ARMS'],(4,5,6)):
        r=simulate(live,h,j,early,before,D)
        audit(r,j,D)
        assert r['completion']==reference(live,h,j,early,before,D)
        # The original non-jam physical workload agrees on root outcomes:
        # the ordinary inspection ends before the terminal is permitted to start.
        if not j and not early:
            assert r['completion']==primary(live,h,False,early,before,D)['completion']
        rows.append(dict(live=live,early=early,before=before,hop=h,jam=j,deadline=D,**r))
    assert [simulate(2,h,j,False)['completion'] for h,j in base['ARMS']]==[4,5,4,None]
    assert [simulate(2,h,j,True)['completion'] for h,j in base['ARMS']]==[4,4,3,4]
    assert [simulate(1,h,j,False)['completion'] for h,j in base['ARMS']]==[2,3,2,3]
    broken = simulate(2,True,True,False)
    mediated = separate['simulate'](2,True,True,False)
    assert broken['completion'] is None and mediated['completion']==5
    assert broken['inspection_completed']==mediated['inspection_completed']==4
    for k in ('inspection_jam_observed','inspection_retry_start','inspection_accept','hop_fault_onset'):
        assert [e for e in broken['trace'] if e[1]==k]==[e for e in mediated['trace'] if e[1]==k]
    print(json.dumps(dict(cases=rows,extra_lane_control=mediated),sort_keys=True,indent=1))
if __name__=='__main__': main()
