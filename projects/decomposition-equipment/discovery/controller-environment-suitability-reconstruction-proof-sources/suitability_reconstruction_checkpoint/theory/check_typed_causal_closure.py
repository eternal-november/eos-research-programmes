#!/usr/bin/env python3
"""Finite regressions for relative-support substitution and causal cubes.
This does not replace the all-generated proof. It uses actual finite maps,
retains boundary values through empty blocks, and keeps parallel records.
"""
from dataclasses import dataclass
from itertools import product
import json
from pathlib import Path

@dataclass(frozen=True)
class Carrier:
    name: str
    values: tuple
    lr: tuple
    def boundary(self, x):
        return dict(self.lr)[x]

@dataclass(frozen=True)
class Rep:
    left: object
    right: object
    values: tuple

class Op:
    def __init__(self, root, leaves, table):
        self.root=root; self.leaves=tuple(leaves); self.table=dict(table)
        assert set(self.table)==set(root.values)
        self.inv={}
        for x, vals in self.table.items():
            l,r=root.boundary(x)
            assert len(vals)==len(self.leaves)
            point=l
            for c,v in zip(self.leaves,vals):
                assert v in c.values
                a,b=c.boundary(v)
                assert a==point
                point=b
            assert point==r
            rep=Rep(l,r,tuple(vals))
            assert rep not in self.inv, 'relative map must be injective'
            self.inv[rep]=x
    def forward(self,x):
        l,r=self.root.boundary(x)
        return Rep(l,r,self.table[x])
    def inverse(self,rep): return self.inv[rep]


def substitute(outer, inners):
    assert len(inners)==len(outer.leaves)
    assert all(h.root==c for c,h in zip(outer.leaves,inners))
    leaves=tuple(c for h in inners for c in h.leaves)
    table={x:tuple(v for p,h in zip(outer.table[x],inners)
                   for v in h.forward(p).values) for x in outer.root.values}
    composite=Op(outer.root,leaves,table)
    # Independently test the constructive inverse: split inner blocks, retain
    # the actual boundary at empty blocks, then test the outer JOINT support.
    for rep,x in composite.inv.items():
        recovered=[]; at=0; point=rep.left
        for h in inners:
            n=len(h.leaves); block=rep.values[at:at+n]
            if n:
                left=h.leaves[0].boundary(block[0])[0]
                right=h.leaves[-1].boundary(block[-1])[1]
                assert left==point
            else: left=right=point
            recovered.append(h.inverse(Rep(left,right,block)))
            point=right; at+=n
        assert at==len(rep.values) and point==rep.right
        assert outer.inverse(Rep(rep.left,rep.right,tuple(recovered)))==x
    return composite


def complete_reps(leaves, left=0,right=0):
    out=[]
    for vals in product(*(c.values for c in leaves)):
        p=left
        for c,v in zip(leaves,vals):
            a,b=c.boundary(v)
            if a!=p: break
            p=b
        else:
            if p==right: out.append(Rep(left,right,vals))
    return out


def carrier(name,values,boundary=lambda x:(0,0)):
    values=tuple(values)
    return Carrier(name,values,tuple((x,boundary(x)) for x in values))


def run():
    tests=0
    bit=carrier('bit',(0,1))
    pair=carrier('pair',tuple(product((0,1),repeat=2)))
    split=Op(pair,(bit,bit),{p:p for p in pair.values})
    repeat=Op(bit,(bit,bit),{b:(b,b) for b in bit.values})
    ident=Op(bit,(bit,),{b:(b,) for b in bit.values})
    # All nonempty correlated supports on a pair of 4-valued components.
    points=tuple(product(pair.values,repeat=2))
    for mask in range(1,1<<len(points)):
        selected=tuple(p for i,p in enumerate(points) if mask>>i&1)
        whole=carrier('whole',selected)
        outer=Op(whole,(pair,pair),{p:p for p in selected})
        expanded=substitute(outer,(split,split))
        left=substitute(expanded,(repeat,ident,repeat,ident))
        inner=substitute(split,(repeat,ident))
        right=substitute(outer,(inner,inner))
        assert left.table==right.table and left.leaves==right.leaves
        tests+=1
    # Explicit natural-join mutation: diagonal correlations must survive.
    whole=carrier('diagonal',((0,0),(1,1)))
    diag=Op(whole,(bit,bit),{p:p for p in whole.values})
    assert len(diag.inv)==2 and len(complete_reps(diag.leaves))==4
    assert Rep(0,0,(0,1)) not in diag.inv
    # All-nullary keeps a two-point boundary rather than collapsing to unit.
    bd=carrier('boundary-carrier',(0,1),lambda b:(b,b))
    null=Op(bd,(),{b:() for b in bd.values})
    dup=Op(bd,(bd,bd),{b:(b,b) for b in bd.values})
    allnull=substitute(dup,(null,null))
    assert len(allnull.inv)==2 and allnull.inverse(Rep(1,1,()))==1
    # Mixed nullary block before/after an actual record.
    mixed=substitute(dup,(null,Op(bd,(bd,),{b:(b,) for b in bd.values})))
    assert mixed.table=={0:(0,),1:(1,)}
    # Same state, different parallel event record retained independently.
    records=carrier('parallel-events',((s,r) for s in (0,1) for r in ('a','b')))
    record_copy=Op(records,(records,records),{e:(e,e) for e in records.values})
    assert len(record_copy.inv)==4
    assert record_copy.forward((0,'a'))!=record_copy.forward((0,'b'))
    # Derived update cube: parent is two stores, children separate stores.
    # A shared reply updates both. All adverse replies, no choice by controller.
    delta=lambda m,y:(m[0]^y,m[1]^y)
    for m,y in product(pair.values,(0,1)):
        assert split.table[delta(m,y)]==tuple(v^y for v in split.table[m])
    # An event-only bit NOT delivered at the interface cannot drive update.
    hidden_events=((0,0),(0,1)) # visible reply, hidden actual record bit
    demanded={e:e[1] for e in hidden_events}
    feasible=any(all(table[e[0]]==demanded[e] for e in hidden_events)
                 for table in product((0,1),repeat=1))
    assert not feasible
    result={
      'status':'PASS',
      'correlated_support_associativity_cases':tests,
      'all_nullary_nonterminal_boundary':'PASS',
      'mixed_nullary_boundary_recovery':'PASS',
      'parallel_record_distinction':'PASS',
      'actual_reply_update_cubes':8,
      'negative_controls':[
        'Replacing retained joint support by marginal natural join adds two spurious tuples',
        'Collapsing empty profile to unit loses one boundary value',
        'Treating hidden completed-event bit as delivered reply falsely enables forbidden update'
      ]}
    out=Path(__file__).with_name('check_typed_causal_closure_results.json')
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': run()
