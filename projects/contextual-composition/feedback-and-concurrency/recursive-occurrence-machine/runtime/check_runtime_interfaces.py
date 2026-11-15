"""Independent small probes; not an adequacy proof."""
import sys
from pathlib import Path
from fractions import Fraction
from occurrence_machine import Machine, Batch, Bind, Op, Ret, Outcome, Leaf, Node, leaves
seen=[]
def primitive(value,caps,world,stores):
    seen.append((caps,set(stores)))
    return [[Outcome('one',Fraction(1),(0,),'check',Leaf(value,caps),world)]]
m=Machine(Batch(lambda v,cs: ((Op('p'),0,('a',)),(Op('p'),0,('b',)))),caps=('a','b'),stores={'a':1,'b':2},primitives={'p':primitive})
m.prefix(100)
assert seen==[(('a',),{'a'}),(('b',),{'b'})]
assert m.jobs[0].mode=='done'
def nullary(value,caps,world,stores):
    return [[Outcome('empty',Fraction(0),(2,),'empty',Node('closed'),world),Outcome('one',Fraction(1),(1,),'one',Leaf(0),world)]]
n=Machine(Bind(Op('z'),lambda v: Ret()),primitives={'z':nullary})
for _ in range(100):
    if n.jobs[0].mode=='done': break
    n.step(outcome=0)
assert n.jobs[0].mode=='done'
assert not leaves(n.jobs[0].result.tree) and n.weight==0 and n.cost==(2,)
print('PASS: held-store isolation and zero-mass nullary-bind probes')
