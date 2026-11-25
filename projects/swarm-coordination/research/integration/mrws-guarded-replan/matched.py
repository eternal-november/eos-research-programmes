"""Matched development comparison of a terminal guard and two continuations."""
from pathlib import Path
from hashlib import sha256
from itertools import product
from collections import Counter
import math
import random
import json
import sys

_calibration = Path(__file__).resolve().parents[1] / "mrws-native-calibration"
if _calibration.is_dir():
    sys.path.insert(0, str(_calibration))
from native_calibration import Warehouse, transport, SimulationError
import mrws.engine.order_manager as om
import mrws.entities.robot as rm

MODE=('terminal','wait','replan')
MAX=240
RATES=(0,0,1/64,1/128)

def fixed_inputs(seed, names):
    rng=random.Random(300100+seed)
    return {(t,a):tuple(rng.random() for _ in RATES)
            for t,a in product(range(1,MAX+1),names)}

class Blocked(Exception):
    pass

class Draws:
    def __init__(self, floats):
        self.floats=list(floats)
    def random(self):
        return self.floats.pop(0)

def run(seed,mode,layout):
    random.seed(51201+seed)
    om.random=random.Random(41201+seed)
    events=[]; box={'tick':0}
    transport.send_message=lambda raw: events.append((box['tick'],json.loads(raw)))
    pl=Warehouse(layout,10,3,"simple-interrupt",RATES,True,MAX)
    names=tuple(pl._robots)
    opportunities=fixed_inputs(seed,names)
    digest=sha256(json.dumps(list(opportunities.items()),separators=(',',':')).encode()).hexdigest()
    for name,robot in pl._robots.items():
        def draw(native=robot.maybe_introduce_fault,actor=name):
            rm.random=Draws(opportunities[(box['tick'],actor)])
            picks=native()
            assert not rm.random.floats # Both battery rates pinned to zero.
            return picks
        robot.maybe_introduce_fault=draw
    move=pl.update_robot_position
    act=pl.decide_robot_action
    guards=[]
    def move_with_gate(actor,x,y):
        if not pl.cell_contains_robot(x,y):
            return move(actor,x,y)
        rob=pl._robots[actor]
        before=(rob.get_position(),rob.report_inventory_item_names())
        guards.append((box['tick'],actor,(x,y),before))
        if mode=="terminal":
            return move(actor,x,y)
        # Native cell validation unchanged. Only the disposition is different.
        if mode=="replan":
            rob.get_movement_path().clear()
        after=(rob.get_position(),rob.report_inventory_item_names())
        assert before==after
        raise Blocked()
    def consume(robot):
        try:return act(robot)
        except Blocked:return None
    pl.update_robot_position=move_with_gate
    pl.decide_robot_action=consume
    report={}
    outcome="budget"
    for t in range(1,MAX+2):
        box['tick']=t
        try:
            done=pl.step()
        except SimulationError as e:
            outcome='native stop: '+str(e).split(' at (')[0]
            break
        ps=[r.get_position() for r in pl._robots.values()]
        assert len(set(ps))==len(ps)
        if done:
            outcome="completed"
            break
    landed=sum(e['command']=='ORDERCOMPLETE' for _,e in events)
    made={(e['objName'],t,e['prio'],e['itemName']) for t,e in events if e['command']=='ORDERCREATE'}
    assert len(made)>=3
    from_tape=sorted((t,e['objName'],e['faultType']) for t,e in events if e['command']=='ROBOTFAULT')
    return dict(seed=seed,mode=mode,tape=digest,landed=landed,outcome=outcome,
                tick=min(MAX,t),rejections=guards,offered=sorted(made),actual_faults=from_tape,
                terminal_loads={a:r.report_inventory_item_names() for a,r in pl._robots.items()})

def main():
    path=sys.argv[1]
    rows=[run(seed,mode,path) for seed,mode in product(range(16),MODE)]
    for i in range(16):
        x,y,z=rows[3*i:3*i+3]
        assert x['tape']==y['tape']==z['tape']
        assert len(y['offered'])==len(z['offered'])==4
        assert y['offered']==z['offered'] # Complete modes can be paired on delivered offers.
        assert set(map(tuple,x['offered']))<=set(map(tuple,y['offered']))
    for mode in MODE:
        own=[x for x in rows if x['mode']==mode]
        print(json.dumps(dict(mode=mode,orders=sum(r['landed'] for r in own),
                              rejects=sum(len(r['rejections']) for r in own),
                              outcomes=dict(Counter(r['outcome'] for r in own))),sort_keys=True))
    print(json.dumps({'replan_vs_wait_orders':dict(Counter(
        ('better' if rows[3*i+2]['landed']>rows[3*i+1]['landed'] else
         'worse' if rows[3*i+2]['landed']<rows[3*i+1]['landed'] else 'tie')
        for i in range(16)))},sort_keys=True))
    with open(sys.argv[2],'w') as fh:
        json.dump(rows,fh,separators=(',',':'),sort_keys=True)
        fh.write('\n')

if __name__=='__main__':
    main()

