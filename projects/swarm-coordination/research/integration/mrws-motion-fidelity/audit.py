"""Defensive movement-fidelity audit on already-used MRWS development seeds."""
from collections import Counter
from itertools import product
from pathlib import Path
import json
import sys
import matched

Native=matched.Warehouse

class Audited(Native):
    guard_mode="native"

    def __init__(self,*a,**k):
        super().__init__(*a,**k)
        self.audit=Counter()
        self.first_nonunit=None
        self.current_turn=None
        self.during_plan=None
        self.move_serial=0
        self.record={}
        self.exclusion_seen=False
        Audited.last=self

    def decide_robot_action(self,robot):
        self.current_turn=robot.get_name()
        try:return super().decide_robot_action(robot)
        finally:self.current_turn=None

    def move_robot_towards_astar_collision_detect(self,robot):
        self.during_plan=robot.get_name()
        self.exclusion_seen=False
        old=self.audit['applied']
        try:return super().move_robot_towards_astar_collision_detect(robot)
        finally:
            if self.exclusion_seen and old==self.audit['applied']:
                self.audit['no_move_after_exclusion_query']+=1
            self.during_plan=None

    def cell_is_full(self,x,y):
        blocked=super().cell_is_full(x,y)
        if self.during_plan and blocked and not self.cell_contains_robot(x,y) and not self.cell_is_wall(x,y):
            self.exclusion_seen=True
        return blocked

    def update_robot_position(self,name,x,y):
        old=self._robots[name].get_position()
        dist=abs(old[0]-x)+abs(old[1]-y)
        over=self.record.get(name)==self.get_total_steps()
        if (self.guard_mode!='native' and dist!=1) or (self.guard_mode=='unit-per-tick' and over):
            self.audit['nonunit_denied' if dist!=1 else 'second_move_denied']+=1
            before=self._robots[name].report_inventory_item_names()
            self._robots[name].get_movement_path().clear()
            assert self._robots[name].get_position()==old
            assert before==self._robots[name].report_inventory_item_names()
            raise matched.Blocked()
        result=super().update_robot_position(name,x,y)
        tick=self.get_total_steps()
        self.audit['applied']+=1
        if self.record.get(name)==tick:
            self.audit['extra_same_actor_tick']+=1
        self.record[name]=tick
        if dist!=1:
            self.audit['applied_nonunit']+=1
            if self.first_nonunit is None:self.first_nonunit=tick
        return result

def main():
    info=[]
    matched.Warehouse=Audited
    for guard,seed,mode in product(('native','unit','unit-per-tick'),range(16),matched.MODE):
        Audited.guard_mode=guard
        r=matched.run(seed,mode,sys.argv[1])
        a=Audited.last
        r.update(motion_law=guard, motion=dict(a.audit), first_nonunit=a.first_nonunit)
        assert not (guard!='native' and a.audit['applied_nonunit'])
        assert not (guard=='unit-per-tick' and a.audit['extra_same_actor_tick'])
        info.append(r)
    for seed in range(16):
        rows=[r for r in info if r['seed']==seed]
        assert len({r['tape'] for r in rows})==1
        nonterminal=[r['offered'] for r in rows if r['mode']!='terminal']
        assert all(len(o)==4 and o==nonterminal[0] for o in nonterminal)
    for guard,mode in product(('native','unit','unit-per-tick'),matched.MODE):
        subset=[r for r in info if r['mode']==mode and r['motion_law']==guard]
        summary=Counter()
        for r in subset:summary.update(r['motion'])
        print(json.dumps(dict(motion_law=guard,mode=mode,orders=sum(r['landed'] for r in subset),
                              outcomes=dict(Counter(r['outcome'] for r in subset)),
                              nonunit_runs=sum(bool(r['motion'].get('applied_nonunit')) for r in subset),
                              **summary),sort_keys=True))
    with Path(sys.argv[2]).open('w') as f:
        json.dump(info,f,sort_keys=True,separators=(',',':'))
        f.write('\n')
if __name__=='__main__':main()

