"""Executable adversarial checks for the addressed evolution/repair semantics.
This checks finite trace families and exact operational sublemmas; it is not the
coupled plant invariant proof. Run with --check to compare the checked record.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
import hashlib
import itertools
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
DEFAULT_LEAN = Path(r"C:\Users\Sean\.elan\toolchains\leanprover--lean4---v4.33.0\bin\lean.exe")

@dataclass(frozen=True)
class Timing:
    n: int
    cells: int
    inquiry: int
    lag: int
    @property
    def duration(self): return self.cells + 2 + self.inquiry + self.lag
    @property
    def slot(self): return self.duration + 1
    @property
    def period(self): return self.n * self.slot
    @property
    def horizon(self): return self.period + self.duration
    def phase(self, t, i): return (t - i*self.slot) % self.period
    def maintenance(self, t):
        return {i for i in range(self.n) if self.phase(t,i) < self.duration}

@dataclass(frozen=True)
class Acquisition:
    target: int
    start: int
    end: int
    mode: str = 'write'
    # Existing access writes arbitrarily on every tick of [start,end).
    def active(self,t): return self.start <= t < self.end


def run_trace(T, events, bad_tools=frozenset(), initial_dirty=frozenset(), steps=None,
              drop_halt=False, omit_last=False):
    steps = steps or (2*T.period + T.duration + 1)
    image = tuple((j+1)%2 for j in range(T.cells))
    poison = tuple(1-v for v in image)
    memory = [list(poison if i in initial_dirty else image) for i in range(T.n)]
    halted = [False]*T.n
    resident = [i in initial_dirty for i in range(T.n)]
    # These flags classify actual commands in this finite diagnostic, never
    # observations fed to a repairer. Actual repair instructions use phase only.
    warm = [None if i in initial_dirty else 0 for i in range(T.n)]
    effect_good = [i not in initial_dirty for i in range(T.n)]
    queue = []
    learned = set(initial_dirty) | set(bad_tools)
    active_history = []
    rows = []
    for t in range(steps):
        active = {e.target for e in events if e.active(t)}
        direct = {e.target for e in events if e.active(t) and e.mode=='write'}
        dependency_only = active-direct
        acquired = {e.target for e in events if e.start == t}
        learned |= acquired
        active_history.append(active)
        for i in range(T.n):
            ph=T.phase(t,i)
            if i not in bad_tools:
                if ph==0 and not drop_halt: halted[i]=True
                elif 1<=ph<=T.cells and (not omit_last or ph<T.cells):
                    memory[i][ph-1]=image[ph-1]
                elif ph==T.cells+1:
                    halted[i]=False
                    warm[i]=T.inquiry
                    resident[i] = tuple(memory[i]) != image
                # A correct reboot's first fresh command is issued at the
                # declared complete-inquiry boundary, not at boot itself.
                if ph==T.cells+2+T.inquiry:
                    if tuple(memory[i])==image and not halted[i]:
                        warm[i]=0
                        queue.append((t+T.lag,i,True))
                elif not halted[i] and warm[i]==0 and tuple(memory[i])==image:
                    queue.append((t+T.lag,i,True))
            # Strongest finite representative writes after the repair operation.
            # It cannot be suppressed by administrative revocation or release.
            if i in direct or i in bad_tools:
                memory[i][:]=poison
                resident[i]=True
                warm[i]=None
                queue.append((t+T.lag,i,False))
                effect_good[i]=False
            elif i in dependency_only:
                # Ordinary timeout/held-output uncertainty: no hostile store write
                # or direct hostile actuator command is invented by this branch.
                warm[i]=None
                effect_good[i]=False
            elif drop_halt and resident[i] and not halted[i]:
                # Resident poisoned code can undo an already written address.
                memory[i][0]=poison[0]
        due=[q for q in queue if q[0]==t]
        queue=[q for q in queue if q[0]>t]
        # For simultaneous completions choose hostile overwrite last.
        for _,i,good in sorted(due,key=lambda q: not q[2]): effect_good[i]=good
        actual={i for i in range(T.n) if i in active or i in bad_tools or halted[i]
                or tuple(memory[i])!=image or warm[i] is None or not effect_good[i]}
        recent=set().union(*active_history[max(0,t-T.horizon):t+1])
        startup=set(initial_dirty) if t<T.horizon else set()
        envelope=set(bad_tools)|recent|T.maintenance(t)|startup
        rows.append(dict(t=t,active=sorted(active),direct_authority=sorted(direct),actual=sorted(actual),
                         envelope=sorted(envelope),maintenance=sorted(T.maintenance(t)),
                         memory=[list(x) for x in memory],learned=sorted(learned),
                         queue=[list(x) for x in queue],effect_good=list(effect_good)))
    return rows


def finite_checks():
    cases=0
    # Every Boolean initial memory/image, every permutation and every address:
    # the proof is general; this is a separately executed interpretation check.
    for m in range(1,5):
        for image in itertools.product((0,1),repeat=m):
            for initial in itertools.product((0,1),repeat=m):
                for addresses in itertools.permutations(range(m)):
                    mem=list(initial)
                    for a in addresses: mem[a]=image[a]
                    assert tuple(mem)==image
                    cases+=1
    T=Timing(3,2,1,1)
    schedules=[]
    # Exhaustive one- and two-acquisition intervals from the explicitly bounded
    # enumeration, including overlap, repeat target and poisoned release.
    options=[Acquisition(i,s,s+d) for i in range(3) for s in range(6) for d in (1,2,4)]
    schedules.append(())
    schedules.extend((e,) for e in options)
    schedules.extend((a,b) for a in options for b in options if a.start<b.start)
    traces=0; ticks=0; max_actual=0
    for events in schedules:
        for tools in (frozenset(),frozenset({0}),frozenset({1}),frozenset({2})):
            for initial in (frozenset(),frozenset({0})):
                rows=run_trace(T,events,tools,initial)
                for r in rows:
                    assert set(r['actual'])<=set(r['envelope']), (events,tools,initial,r)
                    assert len(r['maintenance'])<=1
                    ticks+=1
                    max_actual=max(max_actual,len(r['actual']))
                assert all(set(a['learned'])<=set(b['learned']) for a,b in zip(rows,rows[1:]))
                traces+=1
    return dict(addressed_image_cases=cases,trace_family=dict(n=3,cells=2,inquiry=1,lag=1,
                start_ticks=list(range(6)),access_durations=[1,2,4],max_events=2,
                bad_tool_sets=[[],[0],[1],[2]],initial_dirty_sets=[[],[0]]),
                traces=traces,tick_checks=ticks,max_actual_bad=max_actual)


def quantitative_checks():
    T=Timing(13,8,20,4)
    assert (T.duration,T.slot,T.period,T.horizon)==(34,35,455,489)
    # Eight consequential sequential acquisitions, plus a permanently bad tool.
    # Every event retains learned identity; all selected targets get later repaired.
    events=[Acquisition((j+1)%13,1+j*(T.horizon+1),9+j*(T.horizon+1)) for j in range(8)]
    end=events[-1].end+T.horizon+T.period
    rows=run_trace(T,events,frozenset({0}),frozenset({12}),end)
    returned={}
    for e in events:
        first=next(r['t'] for r in rows if e.end<=r['t']<e.end+T.horizon
                   and e.target not in r['actual'])
        returned[str(e.start)]=dict(target=e.target,release=e.end,first_nominal=first)
    max_count=0
    for r in rows:
        assert set(r['actual'])<=set(r['envelope'])
        assert len(r['envelope'])<=4, r
        max_count=max(max_count,len(r['envelope']))
    assert len(rows[-1]['learned'])==10 # eight acquisitions, initial contamination, bad tool
    # Every possible schedule residue has its next attempt within one period.
    residues=0
    for i in range(T.n):
        for t in range(T.period):
            wait=(i*T.slot-t)%T.period
            assert 0<=wait<T.period
            assert T.phase(t+wait,i)==0
            residues+=1
    return dict(n=13,cells=8,inquiry=20,lag=4,D=T.duration,S=T.slot,P=T.period,H=T.horizon,
                acquisition_spacing=T.horizon+1,c_target=8,r_tool=1,f_target=1,f0=1,
                scheduled_residue_checks=residues,max_effective_envelope=max_count,
                restoration_witnesses=returned,trace_ticks=len(rows),
                final_learned=rows[-1]['learned'],per_tick_port_operation_bound=2)


def countermodels():
    T=Timing(3,2,1,2)
    released=run_trace(T,[Acquisition(1,0,1)],steps=4)
    assert not released[1]['active'] and 1 in released[1]['actual']
    assert 1 in released[1]['learned'] and any(not q[2] for q in released[1]['queue'])
    nohalt=run_trace(T,[],initial_dirty=frozenset({0}),steps=T.horizon+1,drop_halt=True)
    assert 0 in nohalt[-1]['actual']
    omitted=run_trace(T,[],initial_dirty=frozenset({0}),steps=T.horizon+1,omit_last=True)
    assert 0 in omitted[-1]['actual']
    timeline=run_trace(T,[],initial_dirty=frozenset({0}),steps=T.duration+1)
    assert 0 in timeline[T.cells+2]['actual'] and 0 not in timeline[T.duration]['actual']
    # A stolen report key can still forge after release; granting it write reach
    # adds an actual writer rather than being repaired by deletion of local key.
    learned={4}; local_keys=set(); recipient_valid_keys={4}
    assert 4 in learned and 4 not in local_keys and 4 in recipient_valid_keys
    simultaneous_halts={i for i in range(3)}
    assert len(simultaneous_halts)==3
    broad_tool_reach={0,1,2}
    assert len(broad_tool_reach)>1
    dep=run_trace(T,[Acquisition(1,0,1,'request-path')],steps=T.horizon+1)
    assert dep[0]['direct_authority']==[] and dep[0]['memory'][1]==[1,0]
    assert 1 in dep[0]['actual'] and 1 not in dep[-1]['actual']
    for row in dep: assert set(row['actual'])<=set(row['envelope'])
    return dict(dependency_only_impairment=dict(target=1,direct_authority=dep[0]['direct_authority'],
                    code_unchanged=dep[0]['memory'][1],restored_by=dep[-1]['t']),
                instantaneous_count=dict(t=1,current=0,still_bad=released[1]['actual'],
                    retained_key=released[1]['learned'],pending_world_effects=released[1]['queue']),
                missing_halt=dict(t=nohalt[-1]['t'],bad=nohalt[-1]['actual']),
                omitted_address=dict(t=omitted[-1]['t'],bad=omitted[-1]['actual']),
                last_write_is_not_functional=dict(code_complete=T.cells+2,functional=T.duration),
                simultaneous_healthy_maintenance=dict(n=3,physical_outages=3,claimed_if_ignored=0),
                installer_reach_spread=dict(one_bad_tool=1,actual_footprint=[0,1,2]),
                credential_reset=dict(local_keys=[],attacker_keys=[4],can_forge=True),
                reacquisition=dict(targets=[1,1],distinct_targets=1,events=2))


def lean_check(executable):
    version=subprocess.run([str(executable),'--version'],capture_output=True,text=True,encoding='utf-8',check=True).stdout.strip()
    assert 'version 4.33.0' in version
    reports={}
    with tempfile.TemporaryDirectory(prefix='.evolution-check-',dir=ROOT) as folder:
        temp=Path(folder).resolve()
        assert temp.parent==ROOT.resolve() and temp.name.startswith('.evolution-check-')
        shutil.copyfile(ROOT.parent/'research'/'Execution.lean',temp/'Execution.lean')
        subprocess.run([str(executable),'-o','Execution.olean','Execution.lean'],cwd=temp,
                       capture_output=True,text=True,encoding='utf-8',check=True)
        env=dict(os.environ,LEAN_PATH=str(temp))
        for name in ('Evolution.lean','Restoration.lean'):
            out=subprocess.run([str(executable),str(ROOT/name)],cwd=temp,env=env,
                         capture_output=True,text=True,encoding='utf-8',check=True).stdout
            assert 'sorryAx' not in out and 'error:' not in out
            declarations=re.findall(r'^theorem\s+(\w+)',(ROOT/name).read_text(encoding='utf-8'),re.M)
            for declaration in declarations:
                assert re.search(r"\."+declaration+r"' (?:depends on axioms|does not depend on any axioms)",out), (name,declaration)
            dependencies=sorted(set(a.strip() for group in re.findall(r'depends on axioms: \[(.*?)\]',out) for a in group.split(',')))
            assert set(dependencies)<={'propext','Classical.choice','Quot.sound'}
            reports[name]=dict(declarations=len(declarations),names=declarations,axioms=dependencies)
    return dict(version=version,modules=reports)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--check',action='store_true')
    parser.add_argument('--lean',type=Path,default=DEFAULT_LEAN)
    args=parser.parse_args()
    data=dict(status='pass',scope='Finite adversarial operational checks and named Lean lemmas; no plant-invariant completion verdict.',
              finite=finite_checks(),quantitative=quantitative_checks(),countermodels=countermodels(),lean=lean_check(args.lean))
    names=['EVOLUTION.md','RESTORATION.md','evolution_model.py','Evolution.lean','Restoration.lean']
    data['sources_sha256_lf']={name:hashlib.sha256((ROOT/name).read_bytes().replace(b'\r\n',b'\n')).hexdigest() for name in names}
    data['legacy_execution_sha256_lf']=hashlib.sha256((ROOT.parent/'research'/'Execution.lean').read_bytes().replace(b'\r\n',b'\n')).hexdigest()
    path=ROOT/'evolution_results.json'
    if args.check:
        assert data==json.loads(path.read_text(encoding='utf-8')), 'Record differs; inspect changes and regenerate deliberately.'
        print('Evolution/restoration record reproduced.')
    else:
        path.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n',encoding='utf-8')
        print(json.dumps({k:data[k] for k in ('status','finite','quantitative')},indent=2))

if __name__=='__main__': main()
