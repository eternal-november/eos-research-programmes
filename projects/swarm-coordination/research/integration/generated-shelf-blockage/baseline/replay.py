from collections import Counter,deque
from itertools import product
from unittest.mock import patch
from pathlib import Path
import json, random,sys
import os,types
os.environ.pop('ROBOTSIM_TRANSMIT',None)
m=types.ModuleType('pygad')
def no_genetics(*_a,**_k):
    raise RuntimeError('unselected genetic scheduler')
m.GA=no_genetics
sys.modules['pygad']=m
from mrws.io import transport
from mrws.engine.warehouse import Warehouse
from mrws.engine.order_manager import OrderManager
from mrws.models.order import Order
from mrws.entities.order_station import OrderStation
from mrws.entities.home import RobotHome

T=200
EXPECTED=[f'item{x}' for x in range(9,0,-1)]
def one_order(self,n,d,sz):
    o=Order([self._item_set[k] for k in EXPECTED],5,0)
    self._all_orders[0]=o
    self._init_orders.append(o)
def run(seed,arm,lag,off_shelf):
    random.seed(seed)
    events=[]
    obs={}
    transport.send_message=lambda raw:events.append((getattr(obs.get('w'),'_total_steps',0),json.loads(raw)))
    with patch.object(OrderManager,'generate_orders_uniform',one_order):
        w=Warehouse('simu/data/whouse7x11.txt',10,3,'multi-robot',[0,0,0,0],True,T)
    obs['w']=w
    s=w.get_scheduler()
    names=list(w._robots)
    stage={}
    epochs=0; grants={}; reject=[]; moves=Counter(); repair_log=[]; first=None; second=None
    pending=set()
    old=s.reassign_orders_if_faulted
    old_parse=s.parse_schedule_value
    stock=w._order_stations
    for g in stock.values():
        orig=g.interact
        def guard(r,g=g,orig=orig):
            a=r.get_name()
            prefix=g.report_inventory_item_names()
            inv=r.report_inventory_item_names()
            before=(prefix,inv,r._goal_visit_flag)
            grant=grants.pop(a,None)
            valid=(grant==(epochs,0,g.get_name(),a) and not r.battery_faulted_critical
                   and r._amount_items_transfer_next_time is None
                   and s._robot_to_order.get(a)==0
                   and s._order_goal_assignment.get(0)==g.get_name()
                   and r.get_position()==g.get_position()
                   and bool(inv) and (prefix+inv)==EXPECTED[:len(prefix)+len(inv)])
            if not valid:
                assert before==(g.report_inventory_item_names(),r.report_inventory_item_names(),r._goal_visit_flag)
                reject.append((w.get_total_steps(),a,g.get_name(),grant,before))
                raise Halt()
            orig(r)
        g.interact=guard
    def parse(value,r):
        x=old_parse(value,r)
        if isinstance(x,OrderStation):
            a=r.get_name()
            grants[a]=(epochs,s._robot_to_order.get(a),x.get_name(),a)
        return x
    s.parse_schedule_value=parse
    def retire(a,r,to=None):
        grants.pop(a,None)
        r.consume_flag()
        r.set_amount_of_items_to_transfer_next_time(None)
        r.set_target(to)
        r.get_movement_path().clear()
    def reassign():
        nonlocal epochs
        if not pending:return
        pending.clear()
        aa=s._order_robots_assignment.get(0,[])[:]
        if not any(w._robots[a].battery_faulted_critical for a in aa):return
        epochs+=1
        for a in aa:retire(a,w._robots[a])
        if arm=='discard':
            old()
            repair_log.append((w.get_total_steps(),epochs,'native-discard'))
            return
        order=next(o for o in s._orders_active if o.get_id()==0)
        goal=s._order_goal_assignment[0]
        pre=stock[goal].report_inventory_item_names()
        assert pre==EXPECTED[:len(pre)]
        left=EXPECTED[len(pre):]
        kept={}
        for a in aa:
            r=w._robots[a]; inv=r.report_inventory_item_names()
            if not r.battery_faulted_critical and inv:
                j=left.index(inv[0]); assert left[j:j+len(inv)]==inv
                assert j not in kept
                kept[j]=(a,inv)
            s._schedule[a]=deque()
            s._unassign_robot(a)
        empty=[a for a in names if not w._robots[a].battery_faulted_critical
               and not w._robots[a].report_inventory_item_names()]
        segments=[]; i=0; e=0
        while i<len(left):
            if i in kept:
                a,inv=kept[i];segments.append((a,inv,True)); i+=len(inv);continue
            j=min([i+3,len(left),*(k for k in kept if k>i)])
            if not empty:
                repair_log.append((w.get_total_steps(),epochs,'no-empty-carrier'))
                # Fail closed rather than silently constructing phantom inventory.
                raise Halt()
            segments.append((empty[e%len(empty)],left[i:j],False));i=j;e+=1
        s._order_robots_assignment[0]=list(dict.fromkeys(a for a,_,_ in segments))
        for a in s._order_robots_assignment[0]:
            s._assign_robot_to_order(a,0)
            s._schedule[a]=deque()
            r=w._robots[a]
            retire(a,r);r.set_assigned_order(0);r.set_prio(order.get_prio())
        for a,inv,keep in segments:
            # An actor may carry more than one segment in successive trips.
            if not keep:
                for k in inv:s.add_to_schedule(a,s._item_to_shelf_mapping[k][0])
            s.add_to_schedule(a,'block|flag'+str(s._mr_flag_ctr)) if segments[0]!=(a,inv,keep) else None
            if segments[-1]!=(a,inv,keep):
                s._mr_flag_ctr+=1
                s.add_to_schedule(a,goal+'|flag'+str(s._mr_flag_ctr))
            else:s.add_to_schedule(a,goal)
        repair_log.append((w.get_total_steps(),epochs,segments))
    s.reassign_orders_if_faulted=reassign
    for a,r in w._robots.items():
        native=r.maybe_introduce_fault
        def draw(a=a,r=r,native=native):
            if (first is not None and (w.get_total_steps()==first[0] and a==first[1] or
                second is not None and w.get_total_steps()==second[0] and a==second[1])):
                r._battery_critical_fault_rate=1
                pending.add(a)
                try:return native()
                finally:r._battery_critical_fault_rate=0
            return native()
        r.maybe_introduce_fault=draw
    # Shared deterministic form of the previously audited step guard.
    def travel(r):
        r.set_movement_path(w.compute_robot_astar_path(r))
        if r.get_movement_path():
            nx,ny=r.get_movement_path()[0];x,y=r.get_position()
            if (abs(x-nx)+abs(y-ny)==1 and w.is_within_grid(nx,ny)
                and not w.cell_is_full(nx,ny)):
                k=(w.get_total_steps(),r.get_name());assert not moves[k]
                w.move_robot_next_path_spot(r);moves[k]+=1
    w.move_robot_towards_astar_collision_detect=travel
    result='budget'
    for t in range(1,T+1):
        if arm!='clean' and first is None:
            a=s._order_robots_assignment.get(0,[])
            b=[x for x in a[1:] if w._robots[x].get_inventory_usage()]
            goal=s._order_goal_assignment.get(0)
            if (a and w._robots[a[0]].get_inventory_usage() and b and not stock[goal].get_inventory_usage()
                and (not off_shelf or w._robots[a[0]].get_position() not in {x.get_position() for x in w._shelves.values()})):
                first=(t,a[0]);second=None if lag is None else (t+lag,b[0])
        if arm=='discard' and s._orders_backlog:s.schedule(t-1)
        try:w.step()
        except Halt:
            result='guard-refusal';break
        pos=[r.get_position() for r in w._robots.values()];assert len(pos)==len(set(pos))
        if w.get_order_manager().get_order_finish_work_times():
            result='completed';break
    fin=w.get_order_manager().get_order_finish_work_times().get(0)
    land=[x['itemName'] for _,x in events if x['command']=='ITEMGAINED' and x.get('objName','').startswith('goal')]
    assert land==EXPECTED[:len(land)]
    assert sum(x['command']=='ORDERCOMPLETE' for _,x in events)==int(fin is not None)
    if fin is not None:assert land==EXPECTED
    pick=sum(x['command']=='ITEMGAINED' and x.get('objName','').startswith('robot')
             and first and ts>=first[0] for ts,x in events) if first else None
    return dict(seed=seed,arm=arm,lag=lag,first=first,second=second,finish=fin,
        result=result,landed=land,picks_after=pick,moves=sum(moves.values()),reject=reject,
        events=events,repairs=repair_log, last={a:dict(pos=r.get_position(), items=r.report_inventory_item_names(), target=r.get_target().get_name() if r.get_target() else None, queue=list(s._schedule.get(a,[])), dead=r.battery_faulted_critical) for a,r in w._robots.items()})

class Halt(Exception):pass
if __name__=='__main__':
    cases=[(a,b) for a,b in product(('discard','retain'),(None,1,4))]+[('clean',None)]
    rows=[run(s,a,b,sys.argv[2]=='off-shelf') for s,(a,b) in product(range(16),cases)]
    for seed in range(16):
        subset=[r for r in rows if r['seed']==seed and r['arm']!='clean']
        assert len(set(r['first'] for r in subset))==1
    for a,b in cases:
        rs=[r for r in rows if (r['arm'],r['lag'])==(a,b)]
        print(a,b,Counter(r['result'] for r in rs),
            Counter(r['first'] for r in rs), sorted({r['finish'] for r in rs if r['finish'] is not None}),
            'picks',Counter(r['picks_after'] for r in rs))
    Path(sys.argv[1]).write_text(json.dumps(rows,sort_keys=True,separators=(',',':'))+'\n')
