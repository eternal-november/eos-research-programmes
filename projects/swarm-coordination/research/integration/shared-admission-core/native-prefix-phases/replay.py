import importlib.util
import json
from collections import defaultdict
from itertools import product
from pathlib import Path
import subprocess
import sys
from core import Fragment, admitted, check, join, view
from phase import radio_history, warehouse_history, options, BACKUP, SIDE_R, SIDE_W, OLD

up=Path(sys.argv[1])
spec=importlib.util.spec_from_file_location('fixture',up/'isolated.py')
iso=importlib.util.module_from_spec(spec)
spec.loader.exec_module(iso)
n=iso.load_native(up/'native_source.py')

def plant(short,stutter):
    w=iso.make(n,True)
    a,b=w.agents
    a.dir=n.Direction.RIGHT if short else n.Direction.UP
    b.x,b.y,b.dir=1,3,n.Direction.RIGHT
    w._recalc_grid()
    word=[n.Action.NOOP]*2+[n.Action.TOGGLE_LOAD]
    if not short: word.append(n.Action.RIGHT)
    if stutter: word.append(n.Action.NOOP)
    word.append(n.Action.FORWARD)
    rows=[]
    for i in range(1,7):
        cmd=word[i-1] if i<=len(word) else n.Action.NOOP
        n.step(w,[cmd.value,(n.Action.FORWARD if i==4 else n.Action.NOOP).value])
        rows.append((i,a.x,a.y,a.carrying_shelf is not None,(b.x,b.y)))
    assert rows[2][1:4]==(2,0,False)
    assert rows[3][-1]==(2,3)
    return rows

shapes={k:plant(*k) for k in product((False,True),repeat=2)}
matrix=list(product((4,5,6),(1,3,4),(1,3,4),range(4),range(2)))
schedule=[(0,4),(1,4),(0,6)]
plans=[x+(who,cut) for x in matrix for who,cut in schedule]
p=subprocess.run([sys.argv[2]],input=''.join(' '.join(map(str,x))+'\n' for x in plans),
                 text=True,capture_output=True,check=True)
out=[tuple(map(int,x.split())) for x in p.stdout.splitlines()]
assert len(out)==len(plans)
native=dict(zip(plans,out))

def compile_rows(cap,a,b,alias,backup,allow_stutter,loss_radio=False,loss_motion=False):
    physical=[]; radio=[]
    for (short,stutter),samples in shapes.items():
        if stutter and not allow_stutter:
            continue
        for mode in range(4):
            key=(short,stutter,mode)
            seed,tx,rx,heard,side,_=native[cap,a,b,mode,alias,0,4]
            assert all(native[(cap,a,b,mode,alias)+s][:-1]==(seed,tx,rx,heard,side) for s in schedule)
            # Initial heading qualification is available; stutter and earlier
            # attempt reason are hidden. The only early radio report is delivery.
            physical.append(Fragment(key,((1,'dispatcher',('heading-east',short)),),
                  frozenset((BACKUP,)) if backup else frozenset(),
                  warehouse_history(samples,loss_motion)))
            radio.append(Fragment(key,((1,'dispatcher',('earlier-callback',bool(heard))),),
                  frozenset(),radio_history(cap,seed,tx,rx,heard,side,loss_radio)))
    return join(physical,radio,options(cap,a,alias))

names=('early','backup','late')
cases=0;cells=0
false_radio=false_motion=0
false_radio_cells=false_motion_cells=0
used={n:0 for n in names}
witness={}
for cap,a,b,alias,backup,allow_stutter in product((4,5,6),(1,3,4),(1,3,4),range(2),range(2),range(2)):
    rows=compile_rows(cap,a,b,alias,backup,allow_stutter)
    atom=compile_rows(cap,a,b,alias,backup,allow_stutter,loss_radio=True)
    unlatches=compile_rows(cap,a,b,alias,backup,allow_stutter,loss_motion=True)
    keys=[(*v,mode) for v in shapes if allow_stutter or not v[1] for mode in range(4)]
    for due in (4,6):
        dues={OLD:due,SIDE_R:2,SIDE_W:4}
        reference=defaultdict(list)
        result=admitted(rows,'dispatcher',1,dues,names)
        for r,r0,r1,(short,stutter,mode) in zip(rows,atom,unlatches,keys):
            truth=[]
            for j,(who,t) in enumerate(schedule):
                seed,tx,rx,heard,side,pay=native[cap,a,b,mode,alias,who,t]
                _,x,y,load,side_at=shapes[short,stutter][t-1]
                allowed=(not who or backup) and not load and (x,y)==(3,0)
                want=bool(pay and side and side_at==(2,3) and allowed and t<=due)
                truth.append(want)
                assert check(r,names[j],1,dues)==want
                false_radio+=check(r0,names[j],1,dues) and not want
                false_motion+=check(r1,names[j],1,dues) and not want
                cases+=1
            reference[view(r,'dispatcher',1)].append(truth)
            if (cap,a,b,alias,backup,due,short,stutter,mode)==(5,3,3,0,1,4,True,False,1):
                witness['erased_with_clear']=dict(tx=tx,rx=rx,choices=truth,
                   collapsed_packet=check(r0,'early',1,dues))
            if (cap,a,b,alias,backup,due,short,stutter,mode)==(5,3,3,0,0,4,False,False,0):
                witness['unloaded_not_departed']=dict(choices=truth,
                   collapsed_clearance=check(r1,'early',1,dues))
        exp={v:tuple(n for i,n in enumerate(names) if all(x[i] for x in rr))
             for v,rr in reference.items()}
        assert result==exp
        atom_r=admitted(atom,'dispatcher',1,dues,names)
        bad_w=admitted(unlatches,'dispatcher',1,dues,names)
        for local,opts in result.items():
            false_radio_cells+=len(set(atom_r[local])-set(opts))
            false_motion_cells+=len(set(bad_w[local])-set(opts))
            if opts:
                used[opts[0]]+=1
                assert all(z[names.index(opts[0])] for z in reference[local])
        if (cap,a,b,alias,backup,due,allow_stutter)==(5,3,3,0,1,4,0):
            key=((1,('heading-east',True)),(1,('earlier-callback',False)))
            assert result[key]==('backup',) and 'early' in atom_r[key]
            witness['same_silence_robust']={'correct':result[key],'collapsed':atom_r[key]}
        cells+=len(exp)
assert witness['erased_with_clear']==dict(tx=3,rx=0,choices=[False,True,False],collapsed_packet=True)
assert witness['unloaded_not_departed']==dict(choices=[False,False,False],collapsed_clearance=True)
print(json.dumps(dict(native_radio_models=len(native),joint_policy_checks=cases,
    local_information_cells=cells,atomic_packet_false_approvals=false_radio,
    unload_as_clear_false_approvals=false_motion,chosen_on_positive_cells=used,
    atomic_packet_false_local_choices=false_radio_cells,
    unload_as_clear_false_local_choices=false_motion_cells,witness=witness),sort_keys=True))
