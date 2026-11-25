"""MRWS source callback calibration and bounded retained-load replay."""
import ast
from collections import Counter,deque
from itertools import product, combinations
from pathlib import Path
from types import SimpleNamespace
import copy
import hashlib
import json

from mrws.models.item import Item
from mrws.models.order import Order
from mrws.entities.inventory import InventoryEntity
from mrws.entities.order_station import OrderStation
from mrws.entities.home import RobotHome
from mrws.io import transport

HASHES={'scheduling/multi_robot.py':'c476c3ed75088c87599b0023759362d888a3b9cf',
        'scheduling/scheduler.py':'f755edc0d513a2629968d123e916546c81a58df1',
        'entities/order_station.py':'66762db94fe0cd25b2d9265bc93183b3e6b07477'}

def original(path, names):
    data=(Path(__import__('mrws').__path__[0])/path).read_bytes()
    assert hashlib.sha1(f'blob {len(data)}\0'.encode()+data).hexdigest()==HASHES[path]
    nodes=[n for n in ast.walk(ast.parse(data)) if isinstance(n,ast.FunctionDef) and n.name in names]
    assert {n.name for n in nodes}==set(names) and len(nodes)==len(names)
    o=dict(Counter=Counter,copy=copy,deque=deque,Order=Order,OrderManager=object,transport=transport)
    exec(compile(ast.fix_missing_locations(ast.Module(body=nodes,type_ignores=[])),path,'exec'),o)
    return {s:o[s] for s in names}

class Carrier(InventoryEntity):
    def __init__(self,s,load=()):
        super().__init__(s,3);self.battery_faulted_critical=False;self.battery_faulted=False
        self.gone_home_to_clear_inv=False;self.apply_charge_wait_upon_reaching_home=False
        self.target=None;self.wait=0;self.pending_flag=None;self.receive_inventory([items[x] for x in load])
    def get_name(self):return self._name
    def set_target(self,x):self.target=x
    def add_wait_steps(self,x):self.wait+=x
    def consume_flag(self):f=self.pending_flag;self.pending_flag=None;return f

items={i:Item('item'+str(i),i) for i in range(3,9)}
class Fixture:
    def __init__(self):
        self._robots={k:Carrier(k,x) for k,x in {'A':[7,6],'B':[5,4],'C':[3],'D':[]}.items()}
        self._homes={k:RobotHome(k,k,0,0) for k in self._robots}
        self._robots['A'].battery_faulted_critical=True
        self._goals={'station':OrderStation(0,0,'station',lambda:self,lambda:self,lambda:9)}
        self._goals['station'].receive_inventory([items[8]])
        self._order_robots_assignment={1:['A','B','C']}
        self._assigned_robots={'A','B','C'}
        self._robot_to_order={k:1 for k in ('A','B','C')}
        self._order_goal_assignment={1:'station'}
        self._orders_active=[Order([items[i] for i in range(7,2,-1)],1,1,[items[i] for i in range(8,2,-1)])]
        self._orders_backlog=[]
        self._schedule={k:deque() for k in self._robots}
        self.completions=[]
    def add_flag(self,f):raise AssertionError('no old flag authorized in this fixture')
    def get_home_name_for_robot_name(self,name):return name
    def schedule(self,step):pass
    def set_order_completion_time(self,order,step):self.completions.append((order.get_id(),step))

for filename,methods in [('scheduling/multi_robot.py',['reassign_orders_if_faulted','generate_order_to_complete_fault']),
                         ('scheduling/scheduler.py',['is_this_a_complete_order','get_items_already_delivered_for_order','_unassign_robot'])]:
    for s,f in original(filename,methods).items():setattr(Fixture,s,f)

def replacement(arm,failed):
    events=[]
    transport.send_message=lambda raw:events.append(json.loads(raw))
    x=Fixture()
    A=x._robots
    station=x._goals['station']
    accepted=[]
    if arm=='native-discard':
        x.reassign_orders_if_faulted()
        assert all(A[r].gone_home_to_clear_inv and A[r].get_inventory_usage()>0 for r in ('B','C'))
        for r in ('B','C'):x._homes[r].interact(A[r])
        if failed is not None:A[failed].battery_faulted_critical=True
        remaining=x._orders_backlog.pop()
        assert [q.get_dependency() for q in remaining.get_items()]==list(range(7,2,-1))
        x._orders_active=[remaining]
        x._order_robots_assignment={1:['D']}
        batches=[('D',tuple(range(7,4,-1))),('D',(4,3))]
    else:
        # The authored repair preserves the order and destination, and
        # cancels the old launch grants. The evaluator injects the second
        # fault before any of these replacement batches is received. The
        # dispatch input is the admitted local authoritative notice.
        if failed is not None:A[failed].battery_faulted_critical=True
        grants=[r for r in ('B','C') if not A[r].battery_faulted_critical]
        x._order_robots_assignment={1:['D']+grants}
        status=[(r,A[r].report_inventory()) for r in grants]
        assert all(A[r].get_inventory_usage()==len(inv) for r,inv in status)
        named={k:tuple(q.get_dependency() for q in inv) for k,inv in status}
        batches=[('D',(7,6))]
        batches += [('B',()) if 'B' in named else ('D',(5,4))]
        batches += [('C',()) if 'C' in named else ('D',(3,))]
    new_picks=0
    for r,pick in batches:
        assert not A[r].battery_faulted_critical
        new_picks+=len(pick)
        A[r].receive_inventory([items[i] for i in pick])
        accepted+=A[r].report_inventory_item_names()
        station.interact(A[r])
    assert x.completions==[(1,9)]
    assert not station.report_inventory()
    assert [e['objName'] for e in events if e['command']=='ORDERCOMPLETE']==['order1']
    assert accepted==['item'+str(i) for i in range(7,2,-1)]
    return {'arm':arm,'later_loss':failed,'new_picks':new_picks,
            'complete':len(x.completions),'station_classes_received':accepted}

def main():
    cases=[]
    for which in (None,'B','C'):
        for arm in ('native-discard','retained'):
            y=replacement(arm,which)
            assert y['new_picks']==(5 if arm=='native-discard' else {None:2,'B':4,'C':3}[which])
            cases.append(y)
    # For disjoint, indivisible class batches, the worst missing count after
    # at most k later losses is missing now plus the sum of the k largest.
    checks=0
    for n in range(6):
        for w in product((1,2,3),repeat=n):
            for k in range(n+1):
                assert max(map(sum,combinations(w,k)))==sum(sorted(w,reverse=True)[:k])
                checks+=1
    print(json.dumps(dict(cases=cases,reserve_checks=checks),sort_keys=True))
if __name__=='__main__':main()
