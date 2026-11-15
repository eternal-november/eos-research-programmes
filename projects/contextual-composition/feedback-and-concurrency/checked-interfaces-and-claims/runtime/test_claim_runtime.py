from fractions import Fraction as F
from claim_runtime import *

# Mint-like claim labels already used by ordinary resources cannot alias issuance.
child=Batch(lambda v,cs:((Ret(),'one',cs),(Ret(),'two',())))
prog=Bind(ClaimSpawn(child,(1,),'two-leaf'),lambda h:ClaimAwait(2))
m=ClaimMachine(prog,value='caller',caps=('@claim:0','work','reserve'),stores={'@claim:0':0,'work':0,'reserve':0})
m.prefix(100,stop_at_root=True)
assert m.jobs[0].mode=='done'
assert len(m.claim_rights)==1 and '@claim:1' in m.claim_rights
assert m.ledger['@claim:1']==('retired','@claim:1')
assert [x.caps for x in leaves(m.jobs[0].result.tree)]==[('work',),(),('@claim:0','reserve')]
assert not m.events
print('PASS: fresh linear claim, multi-hole await and separate caller reserve')

# A claim right, not merely the public handle, moves through message escrow.
creator=Bind(ClaimSpawn(Ret(),(0,),'one-leaf'),lambda h:Send('q',payload=lambda h:h,take=lambda v,cs:(cs[-1],)))
receiver=Bind(Receive('q'),lambda h:ClaimAwait(0))
prog=Batch(lambda v,cs:((creator,'creator',cs),(receiver,'receiver',())))
m=ClaimMachine(prog,caps=('work',),stores={'work':0}).prefix(100,stop_at_root=True)
assert m.jobs[0].mode=='done' and len(m.claim_rights)==1
assert all(m.ledger[c][0]=='retired' for c in m.claim_rights)
assert m.ledger['work']==('result',0)
assert len([x for x in m.trace if x[0]=='claim-await'])==1
print('PASS: unique ticket transfers through actual message escrow and receiver claims')

m=ClaimMachine(ClaimAwait(0),value=77).prefix(5,stop_at_root=True)
assert m.jobs[0].result.tree.value=={'refused':'missing claim right'}
try:ClaimMachine(Await(),value=77).step(0)
except ValueError:pass
else:raise AssertionError('bare handle await admitted')
print('PASS: copied/public handle alone gives no claim authority')

forge=lambda v,c,w,s:((Outcome('forge',F(1),(0,),'bad',Leaf(None,('x',)),w,mint={'x':ClaimMachine.JOIN}),),)
m=ClaimMachine(Op('forge'),primitives={'forge':forge},allow_mint=True)
try:m.step(0)
except ValueError:pass
else:raise AssertionError('primitive forged claim')
assert not m.claim_rights and 'x' not in m.ledger
print('PASS: primitive mint cannot create privileged join claims')
