from collections import Counter
from itertools import product
from pathlib import Path
import json
from prefix_source import sources,summary

def check_effects(row):
    cargo={}; station=set(); pending={}
    verified=[]; cancelled=[]
    for t,e in row['events']:
        c=e['command'];a=e.get('objName','')
        if c=='CREATEROBOT':cargo[a]=[]
        if c=='ITEMGAINED' and a.startswith('goal'):station.add(e['itemName'])
        if c=='PREFIXCREDIT':
            if a in pending:cancelled.append((a,t))
            assert cargo[a]==e['items'],(cargo,e)
            pending[a]=(set(e['items']),False,t)
        if c=='ITEMGAINED' and a in cargo:
            if a in pending:
                items,cleared,earlier=pending.pop(a)
                assert cleared and not cargo[a] and items<=station,(a,e,items,cleared,station,cargo)
                verified.append((a,earlier,t,e['itemName']))
            cargo[a].append(e['itemName'])
        if c=='ITEMLOST' and a in cargo:cargo[a].remove(e['itemName'])
        if c=='CLEARINV' and a in cargo:
            cargo[a]=[]
            if a in pending:
                items,_,earlier=pending[a]
                pending[a]=(items,True,earlier)
    return verified

def matched():
    old,new=sources(False),sources(True)
    aggregate=Counter();fixed=[];but=None;traces=[];effects=0
    for guard,a,lag,u,v in product(('none','all','withdrawn'),('discard','retain'),
                               (None,*range(1,9)),(0,1,2,None),(0,1,2,None)):
        if lag is None and v!=0:continue
        settings=(0,a,lag,True,(u,v))
        x,y=[rules[guard](*settings) for rules in (old,new)]
        assert x['notices']==y['notices']
        obsx,obsy=[summary(r,guard) for r in (x,y)]
        witnessed=check_effects(y);effects+=len(witnessed)
        bx,by=bool(x['finish']),bool(y['finish'])
        aggregate[guard,a,bx,by]+=1
        if x['finish']!=y['finish']:
            traces.append(dict(guard=guard,arm=a,opportunity=(lag,u,v),
                               old=obsx,new=obsy,repair=y['repairs'],
                               effects=witnessed, credit=[(t,e) for t,e in y['events'] if e['command']=='PREFIXCREDIT']))
        if obsx['repair_refused_for_no_empty']:
            if by:
                fixed.append((guard,a,lag,u,v,y['finish']))
            else:
                but=(guard,a,lag,u,v,y['result'])
    print('paired comparisons',sum(aggregate.values()),'receipt-before-reuse checks',effects)
    print('completed after earlier no-empty refusal',fixed)
    print('terminal transitions',sorted(aggregate.items()))
    if but:print('still not enough one specimen',but)
    Path('prefix_profiles.json').write_text(json.dumps(traces,sort_keys=True,separators=(',',':'))+'\n')
if __name__=='__main__':matched()
