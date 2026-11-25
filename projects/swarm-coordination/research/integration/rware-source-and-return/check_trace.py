"""Cross-check trace outcomes without running the extraction or the controller."""
from itertools import product
import json,sys
r=json.load(open(sys.argv[1]))
six={(f,g,l,s) for f,g,l,s in product([None,1,2,3,4,5,6],(False,True),(False,True),(False,True))}
rows={(x['stop'],x['guard'],x['loaded'],x['second_stop']):x for x in r['rows']}
assert set(rows)==six
assert all(r['detector_controls'].values())
for x in rows.values():
    tr=x['trace']
    assert len(tr)==15
    effect=[(z[0],z[5]) for z in tr if z[5]]
    assert effect==([(x['deliver'],.5)] if x['deliver'] else [])+([(x['drop'],.5)] if x['drop'] else [])
    assert all(z[6]==[] and len({tuple(a[:2]) for a in z[3]})==2 for z in tr)
    if x['deliver']:
        z=tr[x['deliver']-1]
        assert z[3][1]==[4,1,True,1] and z[4]==[2]
    if x['drop']:
        z=tr[x['drop']-1]
        assert z[3][1]==[4,2,False,None] and z[4]==[2]
    if x['second_stop'] and x['deliver']:
        assert x['drop'] is None and tr[-1][3][1]==[4,1,True,1]
    if x['physical_halt'] is not None:
        assert all(z[3][0][:2]==x['physical_halt'] for z in tr[x['stop']-1:])
assert rows[2,False,False,False]['physical_halt']==[2,1]
assert rows[2,False,False,False]['deliver'] is None
assert (rows[2,True,False,False]['deliver'],rows[2,True,False,False]['drop'])==(5,8)
assert (rows[None,False,False,False]['drop'],rows[None,True,False,False]['drop'])==(10,15)
print('56 traces and 840 native effect cycles audited; both published label controls checked')
