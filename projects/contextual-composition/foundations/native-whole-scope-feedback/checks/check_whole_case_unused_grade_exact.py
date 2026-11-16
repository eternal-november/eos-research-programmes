"""Checks whole-case unused shapes and actual nontrivial coefficient arrows.
Finite diagnostics, not a substitute for the all-shape categorical proof.
"""
from itertools import product
from pathlib import Path
import json

I1=((1,),)
A=((1,0),(0,2)) # nonidentity full content arrow on the unused binary shape

def kron(x,y):
    return tuple(tuple(x[i][j]*y[k][l] for j in range(len(x[0]))
                       for l in range(len(y[0])))
                 for i in range(len(x)) for k in range(len(y)))

def terms(depth):
    ans=[('c0',())]
    opts=[None] # I/external alternative, never deleted from the full grade
    if depth>1:
        opts += terms(depth-1)
    ans += [('c2',slots) for slots in product(opts,repeat=2)]
    return ans

def arity(t):
    name,slots=t
    return 0 if name=='c0' else sum(1 if s is None else arity(s) for s in slots)

def factors(t):
    name,slots=t
    out=[I1 if name=='c0' else A]
    for s in slots:
        if s is not None: out += factors(s)
    return out

def flattened_arrow(t):
    out=I1
    for f in factors(t): out=kron(out,f)
    return out

def root_split_arrow(t):
    name,slots=t
    out=I1 if name=='c0' else A
    for s in slots:
        # full I alternatives retain actual unit maps; internal edges labeled u
        out=kron(out,I1 if s is None else root_split_arrow(s))
    return out

def shape_name(t):
    name,slots=t
    if name=='c0': return 'c0'
    return 'c2('+','.join('I' if s is None else 'u:'+shape_name(s) for s in slots)+')'

all_terms=terms(2)
assert len(all_terms)==10
rows=[]
for t in all_terms:
    arrow=root_split_arrow(t)
    assert arrow==flattened_arrow(t)
    k=sum(f==A for f in factors(t))
    assert len(arrow)==2**k
    if k:
        assert any(arrow[i][i]!=1 for i in range(len(arrow)))
    rows.append({'shape':shape_name(t),'arity':arity(t),
                 'unused_binary_vertices':k,'coefficient_dimension':len(arrow),
                 'actual_arrow_diagonal':[arrow[i][i] for i in range(len(arrow))],
                 'operationally_realized':t==('c0',())})
# Source process uses only completed c0 bodies, but its GLOBAL C contains c2.
assert sum(r['operationally_realized'] for r in rows)==1
assert sum(not r['operationally_realized'] for r in rows)==9
nested=next(r for r in rows if r['shape']=='c2(I,u:c2(I,I))')
assert nested['arity']==3 and nested['actual_arrow_diagonal']==[1,2,2,4]
# A body-only check would see only I1; the full native grade sees A and A tensor A.
assert A!=((1,0),(0,1))
report={'status':'PASS','scope':'finite exact unused-grade diagnostic, not formal verification',
        'all_raw_actual_body':'c0 only','full_grade_contains':['c0: arity 0','c2: arity 2'],
        'root_split_equals_flattened_actual_arrow':True,'terms':rows}
out=Path(__file__).with_name('whole_case_unused_grade_exact_results.json')
out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='terms'},indent=2))
print('Verified',len(rows),'full formal shapes, including 9 unused shapes.')
