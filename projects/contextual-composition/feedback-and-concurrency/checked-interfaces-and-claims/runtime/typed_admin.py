"""Finite checked administrative scripts, with terminal whole-tree await.
All queue participants must use this checked layer. No nominal recursion.
"""
from copy import deepcopy
from dataclasses import dataclass
from claim_runtime import *
from checker import Checker,Rejected,plain,require
from elaborator import Elaborated

@dataclass(frozen=True)
class Package:
    handle: int

class Admin:
    def __init__(self, core, channels, initial_kinds, script):
        plain((channels,initial_kinds,script))
        self.core=Elaborated(core)
        self.channels,self.initial,self.script=deepcopy((channels,tuple(initial_kinds),script))
        c=self.core.c
        require(ClaimMachine.JOIN not in c.S,'reserved claim kind cannot be ordinary')
        for spec in self.channels.values():
            require(set(spec['Q'])<=set(c.I),'unknown channel result bound')
            require(all(k in c.S for k in spec['kinds']),'unknown channel package kind')
        self.plans=[];slots=[('s'+str(i),('ordinary',k)) for i,k in enumerate(self.initial)];handles=set()
        require(bool(self.script),'empty script')
        for index,step in enumerate(self.script):
            names=[n for n,_ in slots];typ=dict(slots);op=step['op'];plan={'before':tuple(names)}
            if 'handle' in step:require(type(step['handle']) is str,'handle binder must be a string')
            require(op in ('spawn','send','receive','await','return'),'unsupported admin syntax')
            require((op in ('await','return'))==(index==len(self.script)-1),'await/return must be terminal')
            if op=='spawn':
                proc=c.P[step['child']];inp=c.I[proc['input']];selected=step['slots']
                require(len(selected)==len(set(selected)) and set(selected)<=set(names),'spawn slot alias')
                require(tuple(typ[n] for n in selected)==tuple(('ordinary',k) for k in inp['kinds']),'child input kinds')
                require(step['value'] in inp['values'],'child input data')
                h,t=step['handle'],step['ticket'];require(h not in handles and t not in names,'fresh binder required')
                Q=tuple(sorted(proc['output']));require('Q' not in step,'child Q is derived, not supplied')
                plan.update(indices=tuple(names.index(n) for n in selected),Q=Q,input=proc['input'])
                slots=[s for s in slots if s[0] not in selected]+[(t,('join',h,Q))];handles.add(h)
            elif op=='send':
                spec=self.channels[step['channel']];t,h=step['ticket'],step['handle'];ordinary=step['slots'];Q=tuple(sorted(spec['Q']))
                require(h in handles and typ.get(t)==('join',h,Q),'payload/ticket target or Q mismatch')
                require(len(ordinary)==len(set(ordinary)) and t not in ordinary,'package alias')
                require(tuple(typ.get(n) for n in ordinary)==tuple(('ordinary',k) for k in spec['kinds']),'package kinds')
                sent=[t]+ordinary;plan['indices']=tuple(names.index(n) for n in sent)
                slots=[s for s in slots if s[0] not in sent]
            elif op=='receive':
                spec=self.channels[step['channel']];h,t=step['handle'],step['ticket'];ns=step['slots'];Q=tuple(sorted(spec['Q']))
                require(h not in handles and len(ns)==len(spec['kinds']),'receive binder/arity')
                require(len([t]+ns)==len(set([t]+ns)) and not(set([t]+ns)&set(names)),'receive slot alias')
                slots+= [(t,('join',h,Q))]+[(n,('ordinary',k)) for n,k in zip(ns,spec['kinds'])];handles.add(h)
            elif op=='await':
                t=step['ticket'];require(t in typ and typ[t][0]=='join','await requires owned ticket')
                plan['index']=names.index(t);plan['Q']=typ[t][2]
            self.plans.append(plan)

    def term(self):
        verified=Admin(self.core.c,self.channels,self.initial,self.script)
        script,plans=deepcopy((verified.script,verified.plans))
        def run(index,env):
            s=script[index];p=plans[index];op=s['op']
            if op=='return':return Ret(lambda _:dict(env))
            if op=='await':return ClaimAwait(p['index'])
            if op=='spawn':
                child=Bind(Ret(lambda _:(p['input'],s['value'])),lambda _:Call(s['child']))
                operation=ClaimSpawn(child,p['indices'],repr(p['Q']))
                return Bind(operation,lambda h:run(index+1,dict(env,**{s['handle']:h})))
            if op=='send':
                operation=Send(s['channel'],take=lambda v,c:tuple(c[i] for i in p['indices']),payload=lambda _:Package(env[s['handle']]))
                return Bind(operation,lambda _:run(index+1,env))
            if op=='receive':
                return Bind(Receive(s['channel']),lambda package:run(index+1,dict(env,**{s['handle']:package.handle})))
            raise AssertionError(op)
        # env is local public substitution; ticket authority is never data.
        # Await reserve keeps current actual public value, not a forged child value.
        return run(0,{})

def start_network(participants, bundles, stores, world):
    """Closed checked-participant network, not an API admitting arbitrary senders."""
    require(bool(participants) and len(participants)==len(bundles),'network arity')
    participants=[Admin(a.core.c,a.channels,a.initial,a.script) for a in participants]
    first=participants[0];c=first.core.c
    flat=tuple(x for b in bundles for x in b)
    require(len(flat)==len(set(flat)) and set(stores)==set(flat),'initial network ownership')
    require(world in c.W,'initial world')
    kinds={}
    for admin,bundle in zip(participants,bundles):
        d=admin.core.c
        require(admin.channels==first.channels,'incompatible channel declarations')
        require((d.I,d.S,d.W,d.O,d.P,d.cost_dimension)==(c.I,c.S,c.W,c.O,c.P,c.cost_dimension),'incompatible core declarations')
        require(len(bundle)==len(admin.initial),'initial participant interface')
        for cap,k in zip(bundle,admin.initial):
            require(k in c.S and stores[cap] in c.S[k],'initial kind/store')
            kinds[cap]=k
    entries=tuple((a.term(),None,tuple(b)) for a,b in zip(participants,bundles))
    return ClaimMachine(Batch(lambda value,caps:entries),caps=flat,kinds=kinds,stores=stores,world=world,primitives=first.core.primitives,procedures=first.core.procedures,cost_dimension=c.cost_dimension)
