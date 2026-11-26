"""The mode can change which read matters without changing the compiled edge."""
from dependency import Producer,evaluate
import json

c=lambda n:('constant',n)
r=lambda n:('read',n)
rows={'rescue_arc':('if',r('use_alternate'),r('alt_pool'),r('old_pool'))}
cells={'use_alternate':False,'old_pool':('retired',),'alt_pool':('retired',)}
for i in range(4096):
    rows[f'disjoint{i}']=r(f'd{i}')
    cells[f'd{i}']=('untouched',)
p=Producer(rows,cells)
res=[]
for change in ({'use_alternate':True},
               {'old_pool':('unreachable-old-state',)},
               {'alt_pool':('issued_old_action_enters',)}):
    base=dict(p.memo)
    delta,recheck=p.update(change,{})
    cold={r:evaluate(code,p.cells) for r,code in p.recipes.items()}
    assert cold==p.memo
    assert delta=={r:v[0] for r,v in cold.items() if v[0]!=base[r][0]}
    res.append(dict(changed_cell=list(change), changed_rows=delta,
                    new_rescue_reads=sorted(p.memo['rescue_arc'][1]),
                    semantic_recipes_rechecked=len(recheck),
                    cold_recipes_checked=len(cold)))
assert [r['semantic_recipes_rechecked'] for r in res]==[1,0,1]
assert res[0]['changed_rows']=={} and res[1]['changed_rows']=={}
assert 'alt_pool' in res[0]['new_rescue_reads']
assert res[-1]['changed_rows']=={'rescue_arc':('issued_old_action_enters',)}
print(json.dumps(res,sort_keys=True,indent=2))
