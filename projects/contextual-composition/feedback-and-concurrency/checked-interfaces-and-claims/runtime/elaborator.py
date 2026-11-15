"""Elaborate accepted explicit finite syntax, excluding mint until fresh-ID adapter.
Callbacks below are fixed lookups/instantiations, not submitted source code.
"""
from copy import deepcopy
from checker import Checker,Rejected
from ordered_runtime import *

class Elaborated:
    def __init__(self,checked):
        checked=Checker(checked.I,checked.S,checked.W,checked.O,checked.P,checked.cost_dimension)
        self.c=checked
        for o in checked.O.values():
            if any(r.get('mint') for a in o['table'].values() for law in a for r in law):
                raise Rejected('mint formation supported, fresh-ID elaboration not yet supplied')
        self.bodies={n:self.term(p['body']) for n,p in checked.P.items()}
        self.procedures={n:(lambda value,n=n:ProcedureEntry(self.bodies[n],value)) for n in self.bodies}
        self.primitives={n:self.primitive(o) for n,o in checked.O.items()}
    def term(self,t):
        op=t['op']
        if op=='ret':return Ret()
        if op=='primitive':return Op(t['name'])
        if op=='call':return Call(t['name'])
        if op=='yield':return Yield(self.term(t['body']))
        if op=='choice':return Choice(tuple(self.term(b) for b in t['branches']))
        if op=='case':
            pairs=tuple(t['branches'].items());indices={v:i for i,(v,_) in enumerate(pairs)}
            return Case(lambda value:indices[value[1]],tuple(self.term(b) for _,b in pairs))
        if op=='bind':
            bodies={k:self.term(v) for k,v in t['handlers'].items()}
            return Bind(self.term(t['left']),lambda value:bodies[value])
        if op=='batch':
            entries=tuple((self.term(c['body']),(c['tag'],c['value']),tuple(c['slots'])) for c in t['children'])
            return Batch(lambda value,caps:tuple((body,data,tuple(caps[n] for n in ids)) for body,data,ids in entries))
        raise Rejected('unrecognized checked syntax')
    def primitive(self,o):
        table=deepcopy(o['table'])
        def perform(value,caps,world,stores):
            assert value[0]==o['input']
            slot={str(n):c for n,c in enumerate(caps)}
            rows=table[value[1],world,tuple(stores[c] for c in caps)]
            def tree(t):
                if 'node' in t:return Node(t['node'],tuple(tree(c) for c in t['children']))
                return Leaf((t['tag'],t['value']),tuple(slot[n] for n in t['slots']))
            return tuple(tuple(Outcome(str(index),r['weight'],tuple(r['cost']),r.get('event',o.get('event','primitive')),tree(r['tree']),r['world'],
                       consume=tuple(slot[n] for n in r.get('consume',())),
                       retype={slot[n]:k for n,k in r.get('retype',{}).items()},
                       stores={slot[n]:v for n,v in r['stores'].items()})
                       for index,r in enumerate(law)) for law in rows)
        return perform
    def start(self,name,value,caps,world,stores):
        p=self.c.P[name];i=self.c.I[p['input']]
        if value not in i['values'] or world not in self.c.W or len(caps)!=len(i['kinds']):raise Rejected('invalid initial interface')
        if len(set(caps))!=len(caps) or set(stores)!=set(caps):raise Rejected('invalid initial injection')
        if any(stores[c] not in self.c.S[k] for c,k in zip(caps,i['kinds'])):raise Rejected('invalid initial stores')
        return OrderedMachine(Call(name),value=(p['input'],value),caps=tuple(caps),kinds=dict(zip(caps,i['kinds'])),stores=stores,world=world,primitives=self.primitives,procedures=self.procedures,cost_dimension=self.c.cost_dimension)
