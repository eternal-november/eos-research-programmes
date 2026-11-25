"""Native MRWS source qualification, not a held-out policy test."""
from collections import Counter
from itertools import product
from pathlib import Path
import json
import math
import os
import random
import sys
import types

os.environ.pop("ROBOTSIM_TRANSMIT",None)
# Genetic mode is unselected; fail closed if it is ever called.
m=types.ModuleType("pygad")
def no_genetics(*args, **kwargs):
    raise RuntimeError("Unselected genetic scheduler invoked")
m.GA=no_genetics
sys.modules["pygad"]=m

from mrws.engine.warehouse import Warehouse
from mrws.io import transport
from mrws.exceptions import SimulationError

def capture(seed, with_faults, data):
    random.seed(seed)
    events=[]
    observer={}
    def hook(message):
        w=observer.get('plant')
        native_tick=w.get_total_steps() if w else 0
        events.append((native_tick,json.loads(message)))
    transport.send_message=hook
    actual=[]
    rejected=[]
    outcome="budget"
    w=Warehouse(str(data),10,3,"simple-interrupt",
                [0,0,1/64,1/128] if with_faults else [0,0,0,0],True,240)
    observer['plant']=w
    move_native=w.update_robot_position
    def audit_move(actor,x,y):
        # Record the rejected native precondition without changing the step.
        if w.cell_contains_robot(x,y):
            occupant=w._position_to_robot[(x,y)]
            rejected.append({'tick':w.get_total_steps(),'actor':actor,
                             'cell':[x,y],'occupant':str(occupant),
                             'sensor_faulted':w._robots[actor].sensors_faulted})
        return move_native(actor,x,y)
    w.update_robot_position=audit_move
    for _ in range(241):
        try:
            done=w.step()
        except SimulationError as e:
            outcome='native stop: '+str(e)
            break
        used={}
        for r in w._robots.values():
            used[r.get_name()]={
                'position':r.get_position(),
                'items':r.report_inventory_item_names(),
                'wait':r.get_wait_steps() if math.isfinite(r.get_wait_steps()) else 'infinite'}
        actual.append(used)
        if done:
            outcome="all orders completed"
            break
    assert all(len(set(tuple(r['position']) for r in snapshot.values()))==len(snapshot) for snapshot in actual)
    return {'seed':seed,'with_faults':with_faults,'outcome':outcome,'events':events,'actual':actual,'rejected':rejected}

def qualify(run):
    carry=Counter()
    loaded_faults=[]
    overlaps=[]
    last_fault={}
    count=Counter()
    station_received=set()
    for tick, ev in run['events']:
        cmd=ev['command']; actor=ev.get('objName','')
        count[cmd]+=1
        if cmd=='ITEMGAINED' and actor.startswith('goal'):
            station_received.add(tick)
        if cmd=='ORDERCOMPLETE':
            assert tick in station_received
        if cmd=='ITEMGAINED' and actor.startswith('robot'):
            carry[actor]+=1
        if cmd=='ITEMLOST' and actor.startswith('robot'):
            carry[actor]-=1
        if cmd=='CLEARINV' and actor.startswith('robot'):
            carry[actor]=0
            last_fault.pop(actor,None)
        if cmd=='ROBOTFAULT':
            if carry[actor]>0:
                loaded_faults.append((tick,actor,ev['faultType'],carry[actor]))
            for name,(old_tick,kind) in sorted(last_fault.items()):
                if tick>old_tick and carry[name]>0:
                    overlaps.append((old_tick,name,kind,tick,actor,ev['faultType']))
            if carry[actor]>0:
                last_fault[actor] = (tick,ev['faultType'])
    assert len(run['rejected']) == int("Two robots collided" in run['outcome'])
    return {'rejected_occupied_moves':len(run['rejected']),
            'rejected_sensor_faulted':sum(e['sensor_faulted'] for e in run['rejected']),
            'order_completions':count['ORDERCOMPLETE'],'native_faults':count['ROBOTFAULT'],
            'loaded_faults':len(loaded_faults),'later_faults_before_load_empty':len(overlaps)}

def main():
    dir=Path(sys.argv[1])
    rows=[]
    path=Path(sys.argv[2])
    with path.open('w') as out:
        for with_faults,seed in product([False,True],range(16)):
            data=capture(seed,with_faults,dir/'whouse7x11.txt')
            row=qualify(data)
            rows.append({'seed':seed,'with_faults':with_faults,'outcome':data['outcome'],**row})
            out.write(json.dumps(data,separators=(',',':'),allow_nan=False)+'\n')
    for with_faults in (False,True):
        own=[r for r in rows if r['with_faults']==with_faults]
        summary={'with_faults':with_faults,'completed_runs':sum(r['outcome']=="all orders completed" for r in own),
                 'stops':dict(Counter(r['outcome'] for r in own if r['outcome']!="all orders completed")),
                 'rejected_occupied_moves':sum(r['rejected_occupied_moves'] for r in own),
                 'rejected_sensor_faulted':sum(r['rejected_sensor_faulted'] for r in own),
                 'order_completions':sum(r['order_completions'] for r in own),
                 'native_faults':sum(r['native_faults'] for r in own),
                 'loaded_faults':sum(r['loaded_faults'] for r in own),
                 'later_faults_before_load_empty':sum(r['later_faults_before_load_empty'] for r in own)}
        print(json.dumps(summary,sort_keys=True))
if __name__=='__main__':
    main()

