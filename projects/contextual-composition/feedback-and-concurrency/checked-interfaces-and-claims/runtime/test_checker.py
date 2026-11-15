from copy import deepcopy
from fractions import Fraction as F
from checker import Checker,Rejected
I={'pair':{'kinds':('K','K'),'values':('x',)},'one':{'kinds':('K',),'values':('same',)},'empty':{'kinds':(),'values':('z',)},'other':{'kinds':('L',),'values':('same',)}}
S={'K':(0,),'L':(0,)};W=(0,)
leaf=lambda slot:{'tag':'one','value':'same','slots':[slot]}
row={'weight':F(1),'cost':[1],'world':0,'stores':{'0':0,'1':0},'tree':{'node':'split','children':[leaf('0'),leaf('1')]}}
O={'split':{'input':'pair','output':['one'],'table':{('x',0,(0,0)):[[row,dict(deepcopy(row),weight=F(0))]]}}}
P={'loop':{'input':'one','output':['one'],'body':{'op':'call','name':'loop'}},'main':{'input':'pair','output':['one'],'body':{'op':'bind','left':{'op':'primitive','name':'split'},'handlers':{('one','same'):{'op':'ret'}}}}}
Checker(I,S,W,O,P)
# Two equal-valued leaves remain two distinct checked slot occurrences.
assert len(row['tree']['children'])==2 and row['tree']['children'][0]['slots']!=row['tree']['children'][1]['slots']
def bad(mutator):
    i,o,p=deepcopy(I),deepcopy(O),deepcopy(P);mutator(i,o,p)
    try:Checker(i,S,W,o,p)
    except Rejected:return
    raise AssertionError('bad formation accepted')
bad(lambda i,o,p:p['main']['body']['handlers'].clear())
bad(lambda i,o,p:p['loop'].update(body={'op':'call','name':'main'}))
bad(lambda i,o,p:o['split']['table'][('x',0,(0,0))][0][1].update(consume=['0']))
bad(lambda i,o,p:o['split']['table'][('x',0,(0,0))][0][1]['tree']['children'][1].update(slots=['0']))
bad(lambda i,o,p:o['split']['table'][('x',0,(0,0))][0][0]['tree']['children'][0].update(tag='other'))
bad(lambda i,o,p:p['loop'].update(body=lambda:None))
bad(lambda i,o,p:o['split']['table'].clear())
bad(lambda i,o,p:o['split']['table'][('x',0,(0,0))][0][0].update(weight=1.0))
bad(lambda i,o,p:p['loop'].update(output=['empty'],body={'op':'ret'}))
print('PASS: recursive loop formation and addressed equal leaves; nine all-branch negative cases including zero-weight aliases')

bad(lambda i,o,p:p["main"]["body"].update(op="primitive",name="unknown"))
bad(lambda i,o,p:o["split"]["table"][("x",0,(0,0))][0][0].update(cost=[0,1]))
print("PASS: schema errors produce Rejected; cost dimension mismatch rejected")
