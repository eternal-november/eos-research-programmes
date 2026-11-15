"""Finite explicit formation checker. No execution, callbacks, or termination claim."""
from copy import deepcopy
from fractions import Fraction
from itertools import product

class Rejected(ValueError): pass

def require(b, why):
    if not b: raise Rejected(why)

def plain(x):
    require(not callable(x), 'host callback forbidden')
    if isinstance(x,dict):
        for k,v in x.items():plain(k);plain(v)
    elif isinstance(x,(tuple,list,set,frozenset)):
        for v in x:plain(v)
    else:require(isinstance(x,(str,int,Fraction,type(None))), 'unsupported host object')

class Checker:
    def __init__(self, interfaces, stores, worlds, primitives, procedures, cost_dimension=1):
        try:
            self._check(interfaces,stores,worlds,primitives,procedures,cost_dimension)
        except (KeyError, TypeError, IndexError, AttributeError) as e:
            raise Rejected('malformed declaration schema: '+str(e)) from e

    def _check(self, interfaces, stores, worlds, primitives, procedures, cost_dimension):
        plain((interfaces,stores,worlds,primitives,procedures))
        require(type(cost_dimension)==int and cost_dimension>=0,'invalid cost dimension')
        self.cost_dimension=cost_dimension
        interfaces,stores,worlds,primitives,procedures=deepcopy((interfaces,stores,worlds,primitives,procedures))
        self.I,self.S,self.W,self.O,self.P=interfaces,stores,worlds,primitives,procedures
        require(bool(worlds),'empty world domain')
        for tag,i in interfaces.items():
            require(bool(i['values']), 'empty public domain')
            require(all(k in stores and stores[k] for k in i['kinds']), 'unknown/empty kind')
        for name,o in primitives.items():self.primitive(name,o)
        for name,p in procedures.items():
            require(p['input'] in interfaces,'unknown procedure input')
            require(set(p['output'])<=set(interfaces),'unknown procedure output')
        for name,p in procedures.items():
            require(self.term(p['body'],p['input'])<=set(p['output']), 'procedure output mismatch: '+name)

    def tree(self,t,slots):
        if 'node' in t:
            require(set(t)=={'node','children'},'malformed node')
            found=[];tags=set()
            for c in t['children']:
                a,b=self.tree(c,slots);found+=a;tags|=b
            return found,tags
        require(set(t)=={'tag','value','slots'},'malformed leaf')
        tag=t['tag'];require(tag in self.I,'unknown leaf sort')
        i=self.I[tag];require(t['value'] in i['values'],'invalid leaf value')
        names=t['slots'];require(len(names)==len(i['kinds']),'leaf arity')
        require(all(n in slots for n in names),'unknown/consumed slot')
        require(tuple(slots[n] for n in names)==tuple(i['kinds']),'wrong leaf kind')
        return list(names),{tag}

    def primitive(self,name,o):
        tag=o['input'];require(tag in self.I,'unknown primitive input')
        i=self.I[tag];kinds=i['kinds'];base={str(n):k for n,k in enumerate(kinds)}
        expected=set(product(i['values'],self.W,product(*(self.S[k] for k in kinds))))
        require(set(o['table'])==expected,'primitive table not exhaustive: '+name)
        inferred=set()
        for key,alts in o['table'].items():
            require(bool(alts),'no alternatives')
            for alt in alts:
                require(bool(alt),'empty law')
                for row in alt:
                    w=row['weight'];require(isinstance(w,(int,Fraction)) and not isinstance(w,bool) and w>=0,'inexact/negative weight')
                    require(len(row['cost'])==self.cost_dimension,'cost dimension mismatch')
                    require(all(type(c)==int and c>=0 for c in row['cost']),'nonnatural cost')
                    require(row['world'] in self.W,'invalid world')
                    consume=row.get('consume',[]);require(len(consume)==len(set(consume)) and set(consume)<=set(base),'consume alias')
                    slots={n:k for n,k in base.items() if n not in consume}
                    for n,k in row.get('retype',{}).items():
                        require(n in slots and k in self.S,'invalid retype');slots[n]=k
                    fresh=row.get('mint',{});require(not(set(fresh)&set(base)),'mint alias')
                    require(not fresh or o.get('allow_mint',False),'mint unauthorized')
                    require(all(k in self.S for k in fresh.values()),'unknown minted kind');slots.update(fresh)
                    require(set(row['stores'])==set(slots),'poststore domain mismatch')
                    require(all(v in self.S[slots[n]] for n,v in row['stores'].items()),'poststore kind mismatch')
                    used,tags=self.tree(row['tree'],slots)
                    require(len(used)==len(set(used)) and set(used)==set(slots),'posttree does not partition slots')
                    inferred|=tags
                require(sum(r['weight'] for r in alt)==1,'unnormalized law')
        require(inferred<=set(o['output'])<=set(self.I),'primitive output mismatch')

    def term(self,t,tag):
        require(tag in self.I,'unknown input sort');op=t['op']
        if op=='ret':return {tag}
        if op=='call':
            p=self.P[t['name']];require(p['input']==tag,'recursive call input mismatch');return set(p['output'])
        if op=='primitive':
            p=self.O[t['name']];require(p['input']==tag,'primitive input mismatch');return set(p['output'])
        if op=='yield':return self.term(t['body'],tag)
        if op=='choice':
            require(bool(t['branches']),'empty choice');return set().union(*(self.term(b,tag) for b in t['branches']))
        if op=='case':
            require(set(t['branches'])==set(self.I[tag]['values']),'incomplete case')
            return set().union(*(self.term(b,tag) for b in t['branches'].values()))
        if op=='bind':
            outs=self.term(t['left'],tag)
            keys={(u,v) for u in outs for v in self.I[u]['values']}
            require(set(t['handlers'])==keys,'incomplete/extra continuation branch')
            return set().union(*(self.term(t['handlers'][u,v],u) for u,v in keys))
        if op=='batch':
            used=[];outs=set();ks=self.I[tag]['kinds']
            for child in t['children']:
                ids=child['slots'];require(all(type(n)==int and 0<=n<len(ks) for n in ids),'invalid batch slot')
                require(tuple(ks[n] for n in ids)==tuple(self.I[child['tag']]['kinds']),'batch kind mismatch')
                require(child['value'] in self.I[child['tag']]['values'],'batch data mismatch')
                used+=ids;outs|=self.term(child['body'],child['tag'])
            require(len(used)==len(set(used)) and set(used)==set(range(len(ks))),'batch alias/omission')
            return outs
        raise Rejected('unknown syntax '+str(op))
