"""Receive and consume old-scope receipts from an ordered native command gate."""
from dataclasses import replace
from hashlib import sha1
from pathlib import Path
from itertools import product
import json
import sys
from gate import Gate,Op

ap=Path(sys.argv[3]).resolve()
sys.path.insert(0,str(ap))
src=(ap/'native.py').read_bytes()
assert sha1(f"blob {len(src)}\0".encode()+src).hexdigest()=="3c8870664b7bd6054cd756a6ffc7c365d8aae0c6"
env={'__name__':'native_dependency'}
exec(compile(src,str(ap/'native.py'),'exec'),env)
BAY,F,T,L,R,E,HEAD=[env[k] for k in ('BAY','F','T','L','R','E','HEAD')]

def run(side,kind):
    c,common,storage=env['prefix'](side)
    step,at,agents,shelves,via_y=[c[k] for k in ('step','at','agents','shelves','via_y')]
    w=c['env']
    names={shelves[0].id:'X',shelves[1].id:'Y'}
    orig_x,orig_y=BAY[side],BAY[1-side]
    def seen(actor):
        item=agents[actor].carrying_shelf
        return (at(actor),None if item is None else names.get(item.id,'unrelated'))
    def on(cell):
        x,y=cell
        return names.get(int(w.grid[1,y,x]))
    heading_contract={}
    def typed(actor,waypoints,asset,end=None):
        pos,holds=seen(actor)
        facing=agents[actor].dir
        tape=[]
        for cmd,dest in env['plan'](pos,agents[actor].dir,waypoints,end):
            after=holds
            if cmd==T:after=asset if holds is None else None
            op=Op(actor,cmd,pos,dest,holds,after)
            turn=1 if cmd==R else -1 if cmd==L else 0
            next_facing=HEAD[(HEAD.index(facing)+turn)%4]
            heading_contract[id(op)]=(facing,next_facing)
            tape.append(op)
            pos,holds,facing=dest,after,next_facing
        return tuple(tape)
    def old_x(target):
        ty=target[1]
        return typed(0,[None,(2,3),(2,ty),target,None,
                          (2,ty),(1,ty),(0,ty),*via_y(0,ty,3)],'X',E)
    p_a=typed(1,[orig_y,None,(3,3),orig_x,None,(3,3)],'Y',E)
    p_b=old_x(orig_y)
    seat=old_x(orig_x)
    long=p_a+p_b
    last_turn=Op(0,R,(0,3),(0,3),None,None)
    heading_contract[id(last_turn)]=(E,HEAD[(HEAD.index(E)+1)%4])
    harmless=seat+(last_turn,)

    def prepared():
        bay=[j for j,b in enumerate(BAY) if on(b)=='Y']
        if len(bay)!=1:return None
        j=bay[0]; refuge=(3,1 if j==0 else 5)
        moves=typed(j+2,[BAY[j],None,refuge,None],'Y')
        assert len(moves)==6
        return (j,moves,refuge)

    # Reference lookup never uses Op.footprint; it checks each named field.
    def direct(tape):
        actors=set();slots=set();assets=set()
        for a in tape:
            actors.add(("actor",a.actor))
            slots.update((("cell",*a.before),("cell",*a.after)))
            for n in (a.holds_before,a.holds_after):
                if n is not None:assets.add(("asset",n))
        return actors|slots|assets

    gate=Gate(long if kind in ('phase','late-proof') else seat)
    ac=None;events=[];new_done=None; verified_release=False
    independent=False
    initial=gate.read()
    tick=0
    y_mark=None
    source_done=None
    def acquire(receipt,age):
        nonlocal ac
        j,moves,refuge=prepared()
        use=direct(moves)
        accepted=gate.acquire(receipt,use)
        ref=(receipt.epoch==gate.epoch and receipt.phase==gate.phase
             and set(receipt.pending)==direct(gate.tape)
             and gate.claim is not None if accepted else False)
        # Compare to the same ordered interlock, not an unfenced scheduler.
        expected=(ac is None and receipt.epoch==gate.epoch
                  and receipt.phase==gate.phase and set(receipt.pending)==direct(gate.tape)
                  and not (use&direct(gate.tape)))
        assert accepted==expected
        if accepted:
            assert ref
            ac=[j,moves,refuge,0,tick]
            # Organizer cannot release before actual effect reports.
            assert not gate.release(False)
        events.append(("acquire",tick,age,accepted))
        return accepted
    def edit(new,label):
        expected=not(direct(new)&gate.claim) if gate.claim is not None else True
        accepted=gate.edit(new)
        assert accepted==expected
        events.append(("amend",tick,label,accepted))
        return accepted

    if kind=='pre-conflict':
        assert edit(long,kind)
        assert not acquire(initial,'old-epoch')
        assert not acquire(gate.read(),'current-overlap')
    elif kind=='post-conflict':
        assert acquire(initial,'pre-edit')
        assert not edit(long,kind)
    elif kind=='post-disjoint':
        assert acquire(initial,'pre-edit')
        assert edit(harmless,kind)
        assert gate.epoch==1 and gate.claim is not None
    elif kind=='phase' or kind=='late-proof':
        assert not acquire(initial,'current-overlap')
    else:raise AssertionError(kind)

    candidate_phase=None
    while gate.tape or ac is not None:
        old=gate.tape[0] if gate.tape else None
        new=ac[1][ac[3]] if ac is not None else None
        commands={}
        pre={}
        for a in (old,new):
            if a is None:continue
            assert a.actor not in commands
            commands[a.actor]=a.action
            sample=seen(a.actor)
            assert sample==(a.before,a.holds_before)
            assert agents[a.actor].dir==heading_contract[id(a)][0]
            pre[a.actor]=sample
            if a.action==T and a.holds_before is None:
                # Old/new plan's label checked BEFORE native physical pickup.
                assert on(a.before)==a.holds_after
        tick+=1
        if tick==1:commands[6]=F
        r=step(commands)
        assert r==((0,0,0,0,0,0,.5) if tick==1 else (0,)*7)
        independent|=tick==1
        for op in (old,new):
            if op is not None:
                assert agents[op.actor].dir==heading_contract[id(op)][1]
        if old is not None:
            gate.mark(old,pre[old.actor],seen(old.actor))
            if not gate.tape:source_done=tick
            if old.actor==1 and old.holds_before=='Y' and old.holds_after is None:
                assert on(orig_x)=='Y' and at(1)==orig_x
                assert ('asset','Y') not in direct(gate.tape)
                # Asset-only scope would release too soon: carrier/route is live.
                cells=prepared()[1]
                assert direct(cells)&direct(gate.tape)
                assert not acquire(gate.read(),'old-unloaded-not-cleared')
        if new is not None:
            assert seen(new.actor)==(new.after,new.holds_after)
            ac[3]+=1
            if ac[3]==len(ac[1]):
                j,moves,refuge,_,start=ac
                # Validated native terminal effect, not a scheduled tick.
                assert on(BAY[j]) is None and on(refuge)=='Y'
                assert seen(new.actor)==(refuge,None)
                assert gate.release(True)
                verified_release=True
                new_done=tick
                ac=None
        if kind in ('pre-conflict','phase','late-proof') and gate.phase==len(p_a) and candidate_phase is None:
            # Native after-state plus the actual allowed suffix fixes remaining
            # scope, rather than treating a dispatched operation as completed.
            assert at(1)==(3,3) and seen(1)[1] is None
            assert on(orig_x)=='Y' and on((1,3))=='X'
            assert ('asset','Y') not in direct(gate.tape)
            y_mark=tick;candidate_phase=gate.read()
            events.append(("phase-observed",tick,len(gate.tape)))
            if kind!='late-proof':assert acquire(candidate_phase,'current-after-clear')
        if kind=='late-proof' and candidate_phase is not None and not verified_release and tick==y_mark+1:
            assert not acquire(candidate_phase,'delayed-phase')
            assert acquire(gate.read(),'fresh-checked')
    assert source_done is not None and independent and verified_release
    ending='exchange' if kind in ('pre-conflict','phase','late-proof') else 'reseat'
    assert on(orig_y if ending=='exchange' else orig_x)=='X'
    cleared=side if ending=='exchange' else 1-side
    follower=4+cleared
    assert step({follower:F})==(0,)*7
    assert step({follower:F})==(0,)*7
    assert step({follower:F})[follower]==.5
    expected_time={'pre-conflict':18,'post-conflict':6,'post-disjoint':6,
                   'phase':18,'late-proof':19}[kind]
    assert new_done==expected_time
    assert source_done==({'pre-conflict':28,'post-conflict':16,'post-disjoint':17,
                          'phase':28,'late-proof':28}[kind])
    return dict(side=side,case=kind,done=source_done,real_y_relocation=new_done,
                actual_due_paid=True,independent_paid=True,events=events,
                scope_scan_step_reads=gate.scope_reads,
                native_old_steps_qualified=gate.commands_verified,edit_scan_steps=gate.edits_checked)

if __name__=='__main__':
    print(json.dumps([run(side,kind) for side,kind in
          product((0,1),('pre-conflict','post-conflict','post-disjoint','phase','late-proof'))],
          sort_keys=True,indent=2))
