#!/usr/bin/env python3
"""Executable normalized finite certificate compiler with metered RAM operations.

Input parser/type/shape validation and arbitrary-name normalization are OUTSIDE
this core and charged C_norm. Original evidence/provenance and physical premises
are supplied validated references, with verification cost C_phys, not oracles
silently proved by this code. The core checks their numerical/boolean guards.
Python implements the explicit word-RAM below; counts are NOT Python bytecodes.
"""
from dataclasses import dataclass, replace
from collections import Counter
from pathlib import Path
import json

class Reject(Exception): pass

class RAM:
    def __init__(self): self.counts=Counter(); self.phase='header'
    def charge(self,k=1): self.counts[self.phase]+=k
    def literal(self,v): self.charge(); return v
    def read(self,a,i): self.charge(); return a[i]
    def write(self,a,i,v): self.charge(); a[i]=v
    def alloc(self,n): self.charge(n+1); return [0]*n
    def add(self,a,b): self.charge(); return a+b
    def sub(self,a,b): self.charge(); return a-b
    def mul(self,a,b): self.charge(); return a*b
    def xor(self,a,b): self.charge(); return a^b
    def bor(self,a,b): self.charge(); return a|b
    def shl(self,a,b): self.charge(); return a<<b
    def band(self,a,b): self.charge(); return a&b
    def eq(self,a,b): self.charge(); return a==b
    def le(self,a,b): self.charge(); return a<=b
    def choose(self,test,a,b): self.charge(); return a if test else b
    def require(self,test):
        self.charge() # conditional branch, even on success
        if not test: raise Reject(self.phase)
    def loop(self,n):
        # Explicit counted-loop initialization, then comparison/increment/jump.
        self.charge(2) # initialization plus final failed comparison
        for i in range(n):
            self.charge(3)
            yield i

@dataclass(frozen=True)
class Input:
    # Shape-checked canonical schema. All lists immutable normalized word arrays.
    n:int; source_chart:int; target_chart:int
    refs:tuple  # original evidence, physical K, confidence event, premise token
    source_ids:tuple # 0..n, same IDs in both charts
    triples:tuple # n rows: (r_prev,z,r_next,basis0,basis1,basis2)
    endpoint:tuple # (rn,d,basis0,basis1)
    guards:tuple # stationarity, isolation, sensing, XOR, clock, interlock
    caps:tuple # capture bits, message word bits, selected slot, service/tail ticks
    budget:tuple # remaining, C_norm, C_phys, tau_word


def plane_mask(r,rows,start,dim):
    # Always enumerate full 2^dim subsets, including padded zero basis rows.
    mask=r.literal(0)
    for subset in r.loop(1<<dim): # dim is a program constant 2 or 3
        value=r.literal(0)
        for j in r.loop(dim):
            row=r.read(rows,r.add(start,j))
            bit=r.band(subset,r.shl(1,j))
            selected=r.choose(r.eq(bit,0),0,row)
            value=r.xor(value,selected)
        mask=r.bor(mask,r.shl(1,value))
    return mask


def compile_certificate(inp):
    """Returns output plus phase ledger; raises Reject on any failed core check.
    Shape/type/range validation is a REQUIRED prior admission, not this core.
    No unselected-delay law or physical premise is independently reconstructed.
    """
    r=RAM(); n=inp.n # field dispatch is charged below, flat normalized header
    r.charge(10) # ten Input-field reads; wrapper attribute lookup implements them
    r.require(r.le(2,n)); r.require(r.eq(r.band(n,1),0))
    r.require(r.le(inp.source_chart,1)); r.require(r.le(inp.target_chart,1))
    end_id=r.add(r.mul(2,n),1); count=r.add(n,1)
    r.phase='retained_refs'
    refs=r.alloc(4)
    for j in r.loop(4): r.write(refs,j,r.read(inp.refs,j))
    # No hash/revalidation represented as one operation: upstream verifies refs.
    r.phase='sources'
    sources=r.alloc(count)
    for j in r.loop(count):
        eid=r.read(inp.source_ids,j); r.require(r.eq(eid,j)); r.write(sources,j,eid)
    r.phase='planes'
    for j in r.loop(n):
        i=r.add(j,1); row=r.read(inp.triples,j)
        r.require(r.eq(r.read(row,0),j))
        r.require(r.eq(r.read(row,1),r.add(n,i)))
        r.require(r.eq(r.read(row,2),i))
        r.require(r.eq(plane_mask(r,row,3,3),105)) # 000,011,101,110
    r.require(r.eq(r.read(inp.endpoint,0),n))
    r.require(r.eq(r.read(inp.endpoint,1),end_id))
    r.require(r.eq(plane_mask(r,inp.endpoint,2,2),9)) # 00,11
    r.phase='template'
    # Constant template: all 8 (a,u,v), exact delivered registers, XOR outputs.
    for a in r.loop(2):
      for u in r.loop(2):
       for v in r.loop(2):
        regs=r.alloc(5)
        r.write(regs,0,a) # supplied seam
        r.write(regs,1,u) # draw u: source held
        r.write(regs,2,r.read(regs,1)) # delivery u
        b=r.xor(r.read(regs,0),r.read(regs,2)); r.write(regs,3,b)
        r.write(regs,1,v) # draw v after first event consumed
        r.write(regs,2,r.read(regs,1)) # delivery v
        c=r.xor(r.read(regs,3),r.read(regs,2)); r.write(regs,4,c)
        outgoing=r.read(regs,4) # seam send
        r.require(r.eq(b,r.xor(a,u)))
        r.require(r.eq(outgoing,r.xor(r.xor(a,u),v)))
    r.phase='assembly'
    # Fixed-width cell records: [source id,z occurrence,previous r,next r,
    # source owner,xor owner]. Canonical numbering replaces global distinct-ID sort.
    cells=r.alloc(r.mul(6,n))
    for j in r.loop(n):
        i=r.add(j,1); base=r.mul(6,j)
        # In tile j//2 owners are 0/1. Integer quotient is one word operation.
        r.charge(); tile=j//2
        ownerbase=r.mul(2,tile)
        within=r.band(j,1)
        colowner=r.add(ownerbase,within)
        isrow=r.eq(inp.target_chart,1)
        sourceowner=r.choose(isrow,ownerbase,colowner)
        xorowner=r.choose(isrow,r.add(ownerbase,1),colowner)
        vals=(i,r.add(n,i),j,i,sourceowner,xorowner)
        # vals construction is six register moves, not a free variable tuple.
        r.charge(6)
        for h in r.loop(6): r.write(cells,r.add(base,h),r.read(vals,h))
    r.phase='telescoping'
    residual=r.alloc(r.add(end_id,1))
    for j in r.loop(n):
        row=r.read(inp.triples,j)
        for h in r.loop(3):
            idx=r.read(row,h); r.write(residual,idx,r.xor(r.read(residual,idx),1))
    for h in r.loop(2):
        idx=r.read(inp.endpoint,h); r.write(residual,idx,r.xor(r.read(residual,idx),1))
    for idx in r.loop(r.add(end_id,1)):
        # Expected r0, each zi and d once; intermediate r1..rn cancel.
        zero=r.eq(idx,0); early=r.le(idx,n)
        expected=r.choose(zero,1,r.choose(early,0,1))
        r.require(r.eq(r.read(residual,idx),expected))
    r.phase='guards'
    for j in r.loop(6): r.require(r.eq(r.read(inp.guards,j),1))
    r.require(r.le(count,r.read(inp.caps,0)))
    needed=r.choose(r.eq(inp.target_chart,1),2,1)
    r.require(r.le(needed,r.read(inp.caps,1)))
    # Explicit actual-controller fixture, not the independent sampler clock.
    r.require(r.le(end_id,r.read(inp.caps,2)))
    r.require(r.le(r.read(inp.caps,2),r.read(inp.caps,3)))
    r.phase='budget'
    # Closed-form bound supplied below, derived by summing the fixed loop ledger.
    bound=r.add(r.mul(CORE_SLOPE,n),CORE_CONSTANT)
    total=r.add(r.read(inp.budget,1),r.read(inp.budget,2))
    total=r.add(total,r.mul(r.read(inp.budget,3),bound))
    total=r.add(total,r.read(inp.caps,3))
    r.require(r.le(total,r.read(inp.budget,0)))
    r.phase='output'
    # Header has source and destination chart IDs; original references and source
    # identities survive. Object allocation/field writes are charged explicitly.
    r.charge(9) # record allocation plus eight field writes
    output={'source_chart':inp.source_chart,'target_chart':inp.target_chart,
            'refs':refs,'sources':sources,'cells':cells,'residual':residual,
            'compile_bound':bound,'total_required':total}
    return output,dict(r.counts)

# Derived ledger constants; validated against exact per-phase counts below.
CORE_SLOPE=445
CORE_CONSTANT=597
PHASE_AFFINE={
    'header':(0,22),'retained_refs':(0,27),'sources':(8,11),
    'planes':(324,125),'template':(0,288),'assembly':(64,4),
    'telescoping':(49,45),'guards':(0,53),'budget':(0,13),'output':(0,9)}


def fixture(n,target=1):
    triples=tuple((i-1,n+i,i,3,5,0) for i in range(1,n+1))
    return Input(n,1-target,target,(17,23,31,47),tuple(range(n+1)),triples,
        (n,2*n+1,3,0),(1,)*6,(n+1,2,2*n+2,2*n+3),(10**9,100,200,2))


def main():
    reports=[]
    for n in (2,4,6,8,16,32):
        for target in (0,1):
            inp=fixture(n,target); out,ledger=compile_certificate(inp)
            assert out['refs']==list(inp.refs) and out['sources']==list(inp.source_ids)
            assert ledger=={p:a*n+b for p,(a,b) in PHASE_AFFINE.items()}
            assert sum(ledger.values())==CORE_SLOPE*n+CORE_CONSTANT
            reports.append({'n':n,'target':target,'operations':sum(ledger.values()),'ledger':ledger})
    # Mutation rejection: each relevant normalized dependency is actually read.
    inp=fixture(4); row=list(inp.triples);row[0]=(0,5,1,0,0,0)
    mutations=[replace(inp,source_chart=2),replace(inp,source_ids=(0,1,1,3,4)),
       replace(inp,triples=tuple(row)),replace(inp,endpoint=(4,8,3,0)),
       replace(inp,guards=(1,0,1,1,1,1)),replace(inp,caps=(5,1,9,11)),
       replace(inp,caps=(5,2,8,11)),replace(inp,budget=(10,100,200,2))]
    for bad in mutations:
        try: compile_certificate(bad)
        except Reject: pass
        else: raise AssertionError('bad certificate accepted')
    result={'status':'PASS','runs':reports,'negative_cases':len(mutations),
            'cost_unit':'explicit normalized word-RAM instruction, not Python instruction',
            'all_n_bound':'445n+597 on accepted normalized even-n inputs',
            'phase_affine_ledger':PHASE_AFFINE,
            'external_costs':'C_norm + C_phys, supplied premise verification not implemented'}
    path=Path(__file__).with_name('verification_crossing_compiler.json')
    path.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__': main()
