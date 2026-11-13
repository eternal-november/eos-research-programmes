#!/usr/bin/env python3
"""Independent set-based mathematical audit, no imports from research scripts."""
from itertools import combinations, product
from collections import deque
import json
from pathlib import Path

def powerset(s):
    s=tuple(s)
    return [frozenset(c) for n in range(len(s)+1) for c in combinations(s,n)]

def generate(states, columns, operations):
    columns=set(columns)
    while True:
        nxt=columns|{frozenset(x for x in states if op[x] in c) for op in operations for c in columns}
        if nxt==columns:return columns
        columns=nxt

def close(states, cols, subset):
    containing=[c for c in cols if subset<=c]
    return frozenset(x for x in states if all(x in c for c in containing))

def extents(states,cols):
    return {a for a in powerset(states) if close(states,cols,a)==a}

def rows(states,cols):
    groups={}
    for x in states:groups.setdefault(frozenset(c for c in cols if x in c),set()).add(x)
    return {frozenset(v) for v in groups.values()}

def faces(states,cols):return {s for s in powerset(states) if s and any(s<=c for c in cols)}

def rank(matrix):
    if not matrix:return 0
    a=[r[:] for r in matrix]; r=0
    for j in range(len(a[0])):
        piv=next((i for i in range(r,len(a)) if a[i][j]),None)
        if piv is None:continue
        a[r],a[piv]=a[piv],a[r]
        for i in range(len(a)):
            if i!=r and a[i][j]:a[i]=[u^v for u,v in zip(a[i],a[r])]
        r+=1
    return r

def homology(states,cols):
    f=faces(states,cols)
    simplices=[[s for s in f if len(s)==d+1] for d in range(len(states))]
    boundary_rank=[0]
    for d in range(1,len(states)):
        boundary_rank.append(rank([[int(t<s) for s in simplices[d]] for t in simplices[d-1]]))
    boundary_rank.append(0)
    return [len(simplices[d])-boundary_rank[d]-boundary_rank[d+1] for d in range(len(states))]

def canon(collection):return sorted([sorted(x) for x in collection],key=lambda x:(len(x),x))

def incidence_checks():
    st=range(4); seeds={frozenset((0,1)),frozenset((2,3)),frozenset((0,2)),frozenset((1,3))}
    T=(0,1,3,2);R=(0,0,2,2)
    out={}
    for name,ops,expected in [('local',[],(4,10,[1,1,0,0])),('cnot',[T],(6,12,[1,3,0,0])),('cnot_reset',[T,R],(8,12,[1,0,0,0]))]:
        cols=generate(st,seeds,ops)
        actual=(len(cols),len(extents(st,cols)),homology(st,cols))
        assert actual==expected,(name,actual)
        assert len(rows(st,cols))==4
        out[name]={'columns':canon(cols),'extents':canon(extents(st,cols)),'betti_F2':actual[2]}
    monoid={tuple(st)}
    while True:
        nxt=monoid|{tuple(op[f[x]] for x in st) for op in (T,R) for f in monoid}
        if nxt==monoid:break
        monoid=nxt
    assert len(monoid)==4
    out['native_transformation_monoid']=sorted(monoid)
    # Old transformations must also act on newly added seeds.
    st=range(3);swap=(0,2,1);new={frozenset({1})}
    weak=new;correct=generate(st,new,[swap])
    assert rows(st,weak)!=rows(st,correct)
    assert extents(st,weak)!=extents(st,correct)
    out['retained_operation_counterexample']={'states':list(st),'old_seeds':[],'new_seed':[1],'old_operation':swap,'added_operations':[],
      'weak_extents':canon(extents(st,weak)),'correct_extents':canon(extents(st,correct)),
      'weak_rows':canon(rows(st,weak)),'correct_rows':canon(rows(st,correct))}
    # One-pass completion does not equal mixed-word completion.
    st=range(4);a=(0,0,0,1);b=(0,0,3,0);seed={frozenset({1})}
    sequential=generate(st,generate(st,seed,[b]),[a]);mixed=generate(st,seed,[a,b])
    assert frozenset({2}) not in sequential and frozenset({2}) in mixed
    assert rows(st,sequential)!=rows(st,mixed)
    out['one_pass_counterexample']={'sequential_columns':canon(sequential),'mixed_columns':canon(mixed)}
    return out

def allocations(r,n):
    per_coordinate=[]
    for supply in r:
        per_coordinate.append([v for v in product(range(supply+1),repeat=n) if sum(v)<=supply])
    return [tuple(tuple(c[j] for c in cols) for j in range(n)) for cols in product(*per_coordinate)]

def mv(C,a):return tuple(sum(c*x for c,x in zip(row,a)) for row in C)
def below(a,b):return all(x<=y for aa,bb in zip(a,b) for x,y in zip(aa,bb))
def diff(a,b):return sum(abs(x-y) for aa,bb in zip(a,b) for x,y in zip(aa,bb))

def connected(lifts):
    if not lifts:return False
    seen={lifts[0]};queue=deque(seen)
    while queue:
        a=queue.popleft()
        for b in lifts:
            if b not in seen and diff(a,b)==1:seen.add(b);queue.append(b)
    return len(seen)==len(lifts)

def resource_checks():
    counts={'matrix_arity_pairs':0,'budgets':0,'lifting_categories':0};errors=[]
    for n in (2,3):
      for d in (1,2):
       for m in (1,2):
        for coeff in product(range(3),repeat=d*m):
          C=tuple(tuple(coeff[i*m+j] for j in range(m)) for i in range(d))
          cols=list(zip(*C));nonzero=[c for c in cols if any(c)]
          prediction=(all(sum(c)<=1 for c in cols), all(sum(c)<=1 for c in cols) and len(set(nonzero))==len(nonzero), all(sum(c)==1 for c in cols) and len(set(cols))==m)
          actual=[True,True,True]
          for r in product(range(3),repeat=m):
            if sum(r)>2:continue
            src=allocations(r,n);target=allocations(mv(C,r),n)
            image={a:tuple(mv(C,ai) for ai in a) for a in src}
            counts['budgets']+=1
            for t in target:
                lifts=[a for a in src if below(t,image[a])]
                actual[0]&=bool(lifts);actual[1]&=connected(lifts)
                counts['lifting_categories']+=1
            # A poset equivalence is exactly a bijective order isomorphism.
            actual[2]&=(len(set(image.values()))==len(src) and set(image.values())==set(target) and all(below(image[a],image[b])==below(a,b) for a in src for b in src))
          counts['matrix_arity_pairs']+=1
          if tuple(actual)!=prediction:errors.append({'matrix':C,'arity':n,'actual':actual,'predicted':prediction})
    assert not errors,errors
    return {'counts':counts,'errors':errors,'scope':'All 1x1,1x2,2x1,2x2 matrices in {0,1,2}; arities 2 and 3; budgets of norm at most 2; unit-step connectivity rather than the original comparability implementation.'}

def finite_refinement_checks():
    count=0;least_count=0
    for n in (1,2,3):
      st=range(n);ps=powerset(st)
      families=[set(f) for f in powerset(ps)]
      moore=[f for f in families if extents(st,f)==f]
      for op in product(st,repeat=n):
        stable_moore=[f for f in moore if generate(st,f,[op])==f]
        for seeds in families:
          gen=generate(st,seeds,[op]);M=extents(st,gen)
          # All enlarged-signature-admissible Moore families contain the repair.
          candidates=[f for f in stable_moore if seeds<=f]
          assert candidates and all(M<=f for f in candidates)
          least_count+=1
          old=extents(st,seeds)
          assert (old==M)==all(frozenset(x for x in st if op[x] in c) in old for c in seeds)
          row=rows(st,seeds);block={x:i for i,b in enumerate(row) for x in b}
          assert (row==rows(st,gen))==all(len({block[op[x]] for x in b})==1 for b in row)
          support=all(not inv or any(inv<=c for c in seeds) for inv in (frozenset(x for x in st if op[x] in c) for c in seeds))
          assert (faces(st,seeds)==faces(st,gen))==support
          count+=1
    return {'contexts_and_operations':count,'least_repair_checks':least_count,'exactness_comparisons':3*count,'errors':[]}

if __name__=='__main__':
    result={'incidence':incidence_checks(),'resource':resource_checks(),'finite_refinement':finite_refinement_checks()}
    target=Path(__file__).with_name('independent_checks.json')
    target.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
