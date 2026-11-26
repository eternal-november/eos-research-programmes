"""Typed named supplier edits compiled to explicit graph edits at an audited cut."""
from collections import defaultdict
from copy import deepcopy
from hashlib import sha1
from itertools import product
from pathlib import Path
import json,random,sys
from dependency import Producer,evaluate

src=Path(sys.argv[1]).resolve()
for row in Path(__file__).with_name('SOURCE.tsv').read_text().splitlines():
    p,h=row.split('\t')
    b=(src/p).read_bytes()
    assert sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==h
sys.path.insert(0,str(src))
from reuse import Edits,Fact,Graph,full,infer,update,witnesses,validate_path
from direct_incremental import update_with_witnesses
import plant

C=lambda v:('constant',v)
R=lambda k:('read',k)
I=lambda b,x,y:('if',b,x,y)

def static_reads(e):
    a,*b=e
    if a=='constant':return set()
    if a=='read':return {b[0]}
    return set().union(*(static_reads(u) for u in b))

class Static:
    """Ordinary syntactic dependency indexing; no cold scan on parameter edits."""
    def __init__(self, recipes, cells):
        self.code=dict(recipes);self.cells=dict(cells);self.index=defaultdict(set)
        self.value={k:evaluate(v,cells)[0] for k,v in recipes.items()}
        for k,e in recipes.items():
            for z in static_reads(e): self.index[z].add(k)

    def update(self,cs,es):
        todo=set(es)
        for k,v in cs.items():
            if self.cells[k]!=v:todo.update(self.index[k])
        self.cells.update(cs)
        for named,new in es.items():
            for k in static_reads(self.code[named]):self.index[k].discard(named)
            self.code[named]=new
            for k in static_reads(new):self.index[k].add(named)
        delta={}
        for k in todo:
            v,_=evaluate(self.code[k],self.cells)
            if self.value[k]!=v:delta[k]=v
            self.value[k]=v
        return delta,todo

def model(n):
    p=lambda s,m,l:frozenset({plant.id(plant.step(plant.Mode(m,l),s))})
    choose=I(R('alternate'),R('alternate-pool'),R('original-pool'))
    recipe={}
    cells={'alternate':False,'alternate-pool':False,'original-pool':False,'late':False}
    for s in plant.states:
        ik=plant.id(s)
        normal=p(s,False,False)
        alternate=p(s,True,False) if s.t==0 else p(s,False,True)
        expr=C(normal)
        if alternate!=normal:
            expr=I(choose if s.t==0 else R('late'),C(alternate),C(normal))
        recipe[ik]=expr
    for i in range(n):
        # Distinct, unaffected cells and rows, all required in the root policy.
        k=f'lease-{i}'
        cells[k]=frozenset({k})
        recipe[k]=R(k)
    old=plant.compile(plant.Mode(False,False))
    roots=old.roots|{f'lease-{i}' for i in range(n)}
    facts=old.facts|{f'lease-{i}':Fact() for i in range(n)}
    return recipe,cells,roots,facts

LABELS=('safety','deadline')
def key(w):
    return {k for k,p in w.items() if p is not None}

class Run:
    def __init__(self,n):
        rec,cells,roots,facts=model(n)
        self.n=n
        self.prod=Producer(rec,cells)
        self.static=Static(rec,cells)
        self.graph=Graph(frozenset(roots),{k:v[0] for k,v in self.prod.memo.items()},facts)
        self.cache,_=full(self.graph)
        self.comparator=self.cache

    def apply(self,cs,code=None,oracle=True):
        code=code or {}
        d,r=self.prod.update(cs,code)
        ds,rs=self.static.update(cs,code)
        assert d==ds
        e=Edits(out=d)
        old=self.graph
        self.graph,self.cache,work=update(old,self.cache,e)
        gs,self.comparator,sw=update_with_witnesses(old,self.comparator,e)
        frozen=Graph(self.graph.roots,
                {k:evaluate(v,self.prod.cells)[0] for k,v in self.prod.recipes.items()},
                self.graph.facts)
        assert frozen.out==self.graph.out==gs.out
        if oracle:
            # Compare a separately defined direct slotted semantics.
            q=self.prod.cells
            m=q['alternate-pool'] if q['alternate'] else q['original-pool']
            explicit=plant.compile(plant.Mode(m,q['late']))
            assert all(frozen.out[k]==v for k,v in explicit.out.items())
        cold,cw=full(frozen)
        found=witnesses(self.cache,LABELS)
        assert key(found)==key(witnesses(cold,LABELS))==key(witnesses(self.comparator,LABELS))
        for k,v in found.items():
            if v is not None:
                assert k in LABELS and validate_path(self.graph,v)
                assert k in self.graph.facts[v[-1]].bad
        return dict(verdict=sorted(key(found)), witnesses=found,
                    producer=dict(demanded_rows=len(r),static_rows=len(rs),
                            cold_rows=len(self.prod.recipes),changed_rows=len(d),
                            affected_cells=list(cs),code_changed=list(code)),
                    receiver=dict(cone=work,witness_worklist=sw,cold=cw))

r=Run(4096)
rows=[r.apply({'alternate':True}),
      r.apply({'original-pool':True}),
      r.apply({'alternate-pool':True}),
      r.apply({'late':True})]
assert [z['verdict'] for z in rows]==[[],[],['safety'],['deadline','safety']]
assert [z['producer']['demanded_rows'] for z in rows]==[8,0,8,8]
assert [z['producer']['changed_rows'] for z in rows]==[0,0,8,8]
assert [z['producer']['static_rows'] for z in rows]==[8,8,8,8]

# Current local notices don't determine the installed alias. Keep versions
# complete and mutually exclusive rather than creating a per-row mixed world.
experiment=Run(24)
options={}
for shared in (False,True):
    branch=deepcopy(experiment)
    out=branch.apply({'alternate':True,'alternate-pool':shared})
    options[str(shared)]=out['witnesses']['safety']
assert infer(options)=='undecided'
unknown=dict(verdict=infer(options),witnesses=options,
             discriminator='identity of the effective diagnostic spend pool')

# A recipe's change cannot be ignored merely because the old trace has no read.
case=Run(12)
target='0:1:pending:0'
unsafe=frozenset({'1:0:pending:0'})
edited=case.apply({},{target:C(unsafe)},oracle=False)
assert edited['verdict']==['safety'] and edited['producer']['code_changed']==[target]

# Deliberately broken comparator: update output values only, retaining
# an old read index if a guard switch happened to keep the same value.
class OutputOnly(Producer):
    def _set(self,name,new):
        if name in self.memo and self.memo[name][0]==new[0]:
            return
        super()._set(name,new)

rec,params,roots,facts=model(0)
bad=OutputOnly(rec,params)
d0,k0=bad.update({'alternate':True},{})
d1,k1=bad.update({'alternate-pool':True},{})
assert not d0 and len(k0)==8 and not d1 and not k1
coldBad=plant.compile(plant.Mode(True,False))
sound_graph=Graph(roots,{k:v[0] for k,v in bad.memo.items()},facts)
assert not key(witnesses(full(sound_graph)[0],LABELS))
assert key(witnesses(full(coldBad)[0],LABELS))=={'safety'}
stale_control=dict(apparent_verdict='carries',real_verdict='refuted',
                   wrong_rechecks_after_actual_change=len(k1))

rng=random.Random(48721)
small=Run(7)
keys=('alternate','alternate-pool','original-pool','late')
for _ in range(512):
    change={x:bool(rng.randrange(2)) for x in keys if rng.randrange(3)==0}
    small.apply(change)
print(json.dumps(dict(sequence=rows,unknown=unknown,recipe_edit=edited,stale_control=stale_control,
          deterministic_check_count=512),sort_keys=True,indent=2))
