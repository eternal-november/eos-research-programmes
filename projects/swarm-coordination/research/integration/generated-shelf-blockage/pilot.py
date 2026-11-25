"""Generate native MRWS histories and check a factored event interpretation."""
import json,sys
from pathlib import Path
from itertools import product
from collections import Counter,defaultdict
D=Path(__file__).resolve().parent
S=D/'baseline'
sys.path.insert(0,str(S/'return-route-guard'))
import shield
import with_notices

def sources():
    target=S/'replay.py'
    base=shield.shielded_base(target.read_text())
    witness='''                if r.battery_faulted_critical:
                    goal=s._order_goal_assignment.get(0)
                    delivered=w._order_stations[goal].report_inventory_item_names() if goal else []
                    events.append((w.get_total_steps(),dict(command='CUTWITNESS',objName=a,
                        x=r.get_position()[0],y=r.get_position()[1],prefix=delivered,
                        commissioned=a in s._robot_to_order,actor_faulted=True,
                        inventories={n:b.report_inventory_item_names() for n,b in w._robots.items()})))'''
    old='                try:return native()\n                finally:r._battery_critical_fault_rate=0'
    new='''                try:
                    value=native()
'''+('    '+witness).replace('\n','\n    ')+'''
                    return value
                finally:r._battery_critical_fault_rate=0'''
    assert base.count(old)==1
    both=base.replace(old,new)
    at="                repair_log.append((w.get_total_steps(),epochs,'no-empty-carrier'))"
    assert both.count(at)==1
    both=both.replace(at,at+'\n'+'''                events.append((w.get_total_steps(),dict(command='NOEMPTYCUT',
                    live={actor:bot.report_inventory_item_names() for actor,bot in w._robots.items()
                          if not bot.battery_faulted_critical}, delivered=pre)))''')
    selector='\n        if type(r.get_target()) is RobotHome:'
    assert both.count(selector)==1
    tap="{'command':'HOMEAUDIT','objName':k[1],'posX':nx,'posY':ny}"
    assert both.count(tap)==1
    expr={'none':'False', 'all':'True', 'withdrawn':'r.get_name() not in s._robot_to_order'}
    builds={}
    for key,guard in expr.items():
        short=both.replace(selector,'\n        if type(r.get_target()) is RobotHome and ('+guard+'):')
        a=both if key=='all' else short
        a=a.replace(tap, tap[:-1]+", 'guard_applied':"+guard+"}")
        builds[key]=with_notices.instrument(a)
    return builds

class Location:
    def __init__(self):self.xy={};self.last_home={}
    def step(self,c,a,e,t):
        if c in ('CREATEROBOT','MOVEROBOT'):
            self.xy[a]=e['posX'],e['posY']
            self.last_home.pop(a,None)
        elif c=='HOMEAUDIT':
            x,y=e['posX'],e['posY']
            assert self.xy[a]==(x,y)
            if e["guard_applied"]:self.last_home[a]=t

class Stock:
    def __init__(self):self.shelf={};self.prefix=[];self.cargo=defaultdict(list)
    def step(self,c,a,e):
        if c=='CREATESHELF':
            self.shelf[(e['posX'],e['posY'])]=e['itemName']
        elif c=='CREATEROBOT':
            self.cargo[a]=[]
        elif c=='ITEMGAINED' and a.startswith('goal'):
            self.prefix.append(e['itemName'])
        elif a in self.cargo and c=='ITEMGAINED':
            self.cargo[a].append(e['itemName'])
        elif a in self.cargo and c=='ITEMLOST':
            self.cargo[a].remove(e['itemName'])
        elif a in self.cargo and c=='CLEARINV':
            self.cargo[a].clear()
    def unique_needed_at(self,xy):
        s=self.shelf.get(xy)
        return s if s in {f"item{i}" for i in range(1,10)} and s not in self.prefix and list(self.shelf.values()).count(s)==1 else None

class Failure:
    def __init__(self):self.events={}
    def step(self,c,a,t):
        assert c!='ROBOTRECOVERED'
        if c=='ROBOTFAULT':
            assert a not in self.events
            self.events[a]=t
        if c in ('MOVEROBOT','HOMEAUDIT'):
            assert a not in self.events

def summary(row,guard):
    loc=Location(); stock=Stock(); fail=Failure()
    stops=[]; pending=None; noempty=[]
    for t,e in row['events']:
        c=e['command']; a=e.get('objName','')
        loc.step(c,a,e,t);stock.step(c,a,e);fail.step(c,a,t)
        if c=='NOEMPTYCUT':
            assert all(e['live'].values())
            noempty.append((t,e['live'],e['delivered']))
        if c=='CUTWITNESS':
            assert pending is None
            pending=(t,a,e)
        if c=='ROBOTFAULT':
            ft,fa,witness=pending
            p=loc.xy[a];pre=tuple(stock.prefix)
            assert (t,a,p,pre)==(ft,fa,(witness['x'],witness['y']),tuple(witness['prefix']))
            assert witness['actor_faulted']
            assert all(Counter(v)==Counter(stock.cargo[k]) for k,v in witness['inventories'].items()),(witness['inventories'],stock.cargo)
            block=stock.unique_needed_at(p)
            spare_has_item=block is not None and any(block in cargo and actor not in fail.events
                                                     for actor,cargo in stock.cargo.items())
            after_home=a in loc.last_home
            stops.append(dict(actor=a,time=t,pos=p,source=block,proved_guarded_home=after_home,
                              commissioned=witness['commissioned'], physical_copy_on_survivor=spare_has_item))
            if after_home:assert block is None,(row["arm"],row["lag"],row["notice_delays"], t,a,p,pre,block,loc.last_home)
            pending=None
    assert pending is None
    notices=tuple(map(tuple,row['notices']))
    for t,a in notices:assert fail.events[a]<=t
    for actor,pos in loc.xy.items():assert tuple(row['last'][actor]['pos'])==pos
    assert row['landed']==stock.prefix
    return dict(stops=stops,notices=notices,finish=row['finish'],result=row['result'],
                repair_refused_for_no_empty=any(kind=='no-empty-carrier' for _,_,kind in row['repairs']),
                no_empty_cuts=noempty)

def main():
    fn=sources(); profiles=[]; checked=0
    for g,a,lag,u,v in product(('none','all','withdrawn'),('discard','retain'),
                               (None,*range(1,9)),(0,1,2,None),(0,1,2,None)):
        if lag is None and v!=0:continue
        r=fn[g](0,a,lag,True,(u,v))
        h=summary(r,g)
        assert h['stops'] and h['stops'][0]['time']==19
        if lag is None:assert len(h['stops'])==1
        else:assert len(h['stops'])==2 and h['stops'][1]['time']==19+lag
        profiles.append(dict(guard=g,arm=a,opportunity=(lag,u,v),**h))
        checked+=len(r['events'])
    d={(r['guard'],r['arm'],tuple(r['opportunity'])):r for r in profiles}
    contrasts=[]
    worlds=0
    for (g,a,o),r in d.items():
        if g!='none' or len(r['stops'])<2:continue
        s=d['all',a,o]
        assert r['notices']==s['notices']==d['withdrawn',a,o]['notices']
        old,new=r['stops'][1],s['stops'][1]
        if old['source']!=new['source']:
            contrasts.append((a,o,old['source'],new['source'],r['finish'],s['finish']))
        worlds+=1
    print('native histories',len(profiles),'aligned events',checked,'paired second-stop worlds',worlds)
    print('blocked required shelf at either fault',sorted(Counter((r['guard'],bool(any(s['source'] for s in r['stops']))) for r in profiles).items()))
    print('stops after a guarded home move',Counter(r['guard'] for r in profiles for s in r['stops'] if s['proved_guarded_home']))
    print('same notice sequence, changed physical shelf blockage',len(contrasts))
    print('sample changed history',contrasts[0])
    print('blocked but surviving copy already present',
          sum(s['source'] is not None and s['physical_copy_on_survivor'] for r in profiles for s in r['stops']))
    for guard in ('all','withdrawn'):
        print('paired completion transitions',guard, sorted(Counter(
             (bool(r['finish']),bool(d[guard,a,o]['finish'])) for (g,a,o),r in d.items() if g=='none').items()))
    fresh=[x for x in contrasts if x[1][0] not in (1,4)]
    print('physical contrasts outside original second-stop lags',len(fresh))
    for g,a,o in d:
        if g!='none':continue
        base=d[g,a,o];wide=d['all',a,o];scope=d['withdrawn',a,o]
        if base['finish'] and not wide['finish']:
            print('wide regression',a,o,'base',base['finish'],'wide',wide['result'],
                  'replan refused for no empty carrier',wide['repair_refused_for_no_empty'],
                  'scoped',scope['finish'], 'live cargo at refusal',wide['no_empty_cuts'])
    Path('profiles.json').write_text(json.dumps(profiles,sort_keys=True,separators=(',',':'))+'\n')
if __name__=='__main__':main()
