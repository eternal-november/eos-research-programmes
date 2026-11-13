#!/usr/bin/env python3
"""Generic FINITE CLOSED typed observational model, not all-profile graph engine.
Nodes are (sort, local_id). Deterministic contexts are total within a source sort.
Cuts retain tuples of typed factor nodes, including repeated occurrences and ().
"""
from itertools import product
import json
from functools import lru_cache
from verify_encoder_decoder import concrete_monoid, compose

class Model:
    def __init__(self, carriers, obs, operations, cuts):
        self.carriers=carriers;self.obs=obs;self.operations=operations;self.cuts=cuts
        self.nodes={ (s,x) for s,xs in carriers.items() for x in xs }
        assert set(obs)==self.nodes
        for (s,name),f in operations.items():
            assert set(f)=={(s,x) for x in carriers[s]} and set(f.values())<=self.nodes
        for (s,name),r in cuts.items():
            assert set(r)=={(s,x) for x in carriers[s]}
            assert all(y in self.nodes for outputs in r.values() for tup in outputs for y in tup)

    def evaluate(self,node,formula):
        tag,*args=formula
        if tag=='obs':return self.obs[node]==args[0]
        if tag=='not':return not self.evaluate(node,args[0])
        if tag=='and':return all(self.evaluate(node,f) for f in args)
        if tag=='op':return self.evaluate(self.operations[node[0],args[0]][node],args[1])
        if tag=='cut':
            name,children=args
            return any(len(tup)==len(children) and all(self.evaluate(y,f) for y,f in zip(tup,children)) for tup in self.cuts[node[0],name][node])
        raise ValueError('unknown formula')


def all_slot_contexts(carriers,name,input_sorts,table):
    """Expand a finite total multioperation into ALL one-hole partial evaluations.
    table maps tuples of typed inputs to a typed output. No bounded context-depth claim.
    """
    domains=[tuple((s,x) for x in carriers[s]) for s in input_sorts]
    assert set(table)==set(product(*domains))
    result={}
    for slot,s in enumerate(input_sorts):
        other=[i for i in range(len(domains)) if i!=slot]
        for fixed in product(*(domains[i] for i in other)):
            context={}
            for variable in domains[slot]:
                inputs=[None]*len(domains);inputs[slot]=variable
                for i,value in zip(other,fixed):inputs[i]=value
                context[variable]=table[tuple(inputs)]
            result[s,(name,slot,fixed)]=context
    return result


def refine(model):
    def partition(values):
        result={}; dictionary={}
        for s,xs in model.carriers.items():
            ids={}
            for x in xs:
                node=(s,x);signature=values[node]
                if signature not in ids:ids[signature]=len(ids)
                result[node]=(s,ids[signature])
            dictionary[s]=ids
        return result,dictionary
    q,_=partition(model.obs);history=[q];certificates=[]
    seed_definitions={q[n]:model.obs[n] for n in model.nodes}
    while True:
        signatures={}
        for node in model.nodes:
            s=node[0]
            ds=tuple((name,q[f[node]]) for (domain,name),f in model.operations.items() if domain==s)
            cs=tuple((name,frozenset(tuple(q[y] for y in tup) for tup in r[node])) for (domain,name),r in model.cuts.items() if domain==s)
            signatures[node]=(q[node],ds,cs)
        qnew,_=partition(signatures)
        definitions={qnew[node]:signatures[node] for node in model.nodes}
        certificates.append(definitions);history.append(qnew)
        if all((q[x]==q[y])==(qnew[x]==qnew[y]) for s,xs in model.carriers.items() for x,y in product(((s,z) for z in xs),repeat=2)):
            q=qnew;break
        q=qnew
    # Quotient construction checks representative independence, not just chooses one.
    carriers={s:tuple(sorted({q[s,x][1] for x in xs})) for s,xs in model.carriers.items()}
    obs={};ops={key:{} for key in model.operations};cuts={key:{} for key in model.cuts}
    for node in model.nodes:
        code=q[node]
        assert code not in obs or obs[code]==model.obs[node];obs[code]=model.obs[node]
        for key,f in model.operations.items():
            if key[0]!=node[0]:continue
            value=q[f[node]];assert code not in ops[key] or ops[key][code]==value;ops[key][code]=value
        for key,r in model.cuts.items():
            if key[0]!=node[0]:continue
            value=frozenset(tuple(q[y] for y in tup) for tup in r[node])
            assert code not in cuts[key] or cuts[key][code]==value;cuts[key][code]=value
    quotient=Model(carriers,obs,ops,cuts)
    # Every quotient joint tuple is realized at EVERY concrete representative.
    for key,r in model.cuts.items():
        for node,tuples in r.items():assert {tuple(q[y] for y in tup) for tup in tuples}==set(quotient.cuts[key][q[node]])
    @lru_cache(None)
    def certificate_holds(node,stage,code):
        """DAG class predicate independently re-evaluated on concrete transitions.
        Definitions refer only to earlier-stage class predicates; never inspect q[node].
        """
        if node[0]!=code[0]:return False
        if stage==0:
            seed=seed_definitions[code]
            return model.obs[node]==seed
        old,ds,cs=certificates[stage-1][code]
        if not certificate_holds(node,stage-1,old):return False
        for name,target in ds:
            if not certificate_holds(model.operations[node[0],name][node],stage-1,target):return False
        previous_classes=set(history[stage-1].values())
        for name,wanted in cs:
            actual=set()
            for tup in model.cuts[node[0],name][node]:
                classes=[]
                for y in tup:
                    matches=[c for c in previous_classes if c[0]==y[0] and certificate_holds(y,stage-1,c)]
                    assert len(matches)==1;classes.append(matches[0])
                actual.add(tuple(classes))
            if actual!=set(wanted):return False
        return True
    certificate_holds.definitions=certificates
    certificate_holds.seed_definitions=seed_definitions
    certificate_holds.history=history
    return q,quotient,history,certificate_holds


def check():
    carrier,e,a,b=concrete_monoid(4);s='unary_M4';nodes=tuple((s,x) for x in carrier)
    H={e,b,compose(b,b)};obs={n:n[1] in H for n in nodes}
    ops={(s,'left_a'):{n:(s,compose(a,n[1])) for n in nodes},(s,'right_a'):{n:(s,compose(n[1],a)) for n in nodes},(s,'left_b'):{n:(s,compose(b,n[1])) for n in nodes},(s,'right_b'):{n:(s,compose(n[1],b)) for n in nodes}}
    cuts={(s,'factor'):{n:{((s,u),(s,v)) for u,v in product(carrier,repeat=2) if compose(u,v)==n[1]} for n in nodes}}
    fullcontexts=all_slot_contexts({s:carrier},'multiply',(s,s),{((s,x),(s,y)):(s,compose(x,y)) for x,y in product(carrier,repeat=2)})
    assert len(fullcontexts)==2*len(carrier)
    fullmodel=Model({s:carrier},obs,fullcontexts,cuts)
    fullenc,fullquotient,_,_=refine(fullmodel)
    assert len(fullquotient.nodes)==10
    model=Model({s:carrier},obs,ops,cuts);enc,quotient,stages,certificate=refine(model)
    assert len(quotient.nodes)==10
    # All final class certificates distinguish their states; source semantics re-evaluated.
    for n in nodes:
        for c in quotient.nodes:assert certificate(n,len(stages)-1,c)==(enc[n]==c)
    formulas=[('obs',True),('not',('obs',True)),('cut','factor',(('obs',True),('obs',False))),('op','left_a',('cut','factor',(('obs',False),('obs',True))))]
    formulas += [('and',f,('op','right_b',g)) for f,g in product(formulas,repeat=2)]
    for n,f in product(nodes,formulas):assert model.evaluate(n,f)==quotient.evaluate(enc[n],f)
    # Separate exact old sorts and distinguish feasible nullary cut {()} from none.
    tiny=Model({'emptyA':(0,1),'emptyB':(0,)},{('emptyA',0):0,('emptyA',1):0,('emptyB',0):0},{},{('emptyA','nullary'):{('emptyA',0):{()},('emptyA',1):set()},('emptyB','nullary'):{('emptyB',0):{()}}})
    en,qu,_,_=refine(tiny)
    assert en['emptyA',0]!=en['emptyA',1] and en['emptyA',0]!=en['emptyB',0]
    for n in tiny.nodes:assert tiny.evaluate(n,('cut','nullary',()))==qu.evaluate(en[n],('cut','nullary',()))
    return {'result':'PASS','scope':'finite closed unary M4 model plus typed nullary control','M4_classes':len(quotient.nodes),'stages_including_seed_and_final_check':len(stages),'final_class_certificates_checked':100,'formula_checks':len(nodes)*len(formulas)}

if __name__=='__main__':print(json.dumps(check(),indent=2))
