from ordered_runtime import *
from fractions import Fraction as F
# Input order differs from lexical names; output deliberately reverses kind order.
def swap(v,c,w,s):
    assert c==('z','a') and tuple(s[x] for x in c)==('Kstore','Lstore')
    return ((Outcome('swap',F(1),(0,),'swap',Leaf('post',('a','z')),w),),)
def observe(v,c,w,s):
    assert c==('a','z') and tuple(s[x] for x in c)==('Lstore','Kstore')
    return ((Outcome('seen',F(1),(0,),'seen',Leaf(v,c),w),),)
m=OrderedMachine(Bind(Op('swap'),lambda _:Op('observe')),caps=('z','a'),kinds={'z':'K','a':'L'},stores={'z':'Kstore','a':'Lstore'},primitives={'swap':swap,'observe':observe})
while m.jobs[0].mode!='done':m.step();m.assert_invariant()
assert m.jobs[0].result.tree.caps==('a','z')
b=OrderedMachine(Batch(lambda v,c:((Ret(),1,(c[1],)),(Ret(),2,(c[0],)))),caps=('z','a')).prefix(20,stop_at_root=True)
assert [l.caps for l in leaves(b.jobs[0].result.tree)]==[('a',),('z',)]
print('PASS: private ordered injections preserve heterogeneous Bind and explicit Batch order at every step')
