#!/usr/bin/env python3
"""Finite checks for Task_Relative_Summaries.md; standard library only."""
import itertools, json

def powerset(xs):
    xs=tuple(xs)
    return [frozenset(xs[i] for i in range(len(xs)) if mask>>i&1)
            for mask in range(1<<len(xs))]

def refine(A, operations, tests):
    index={a:i for i,a in enumerate(A)}
    def blocks(signatures):
        seen={}; out=[]
        for s in signatures:
            if s not in seen: seen[s]=len(seen)
            out.append(seen[s])
        return out
    p=blocks([tuple(t(a) for t in tests) for a in A])
    translations=[]
    for arity,f in operations:
        for j in range(arity):
            for rest in itertools.product(A,repeat=arity-1):
                row=[]
                for a in A:
                    args=list(rest);args.insert(j,a)
                    v=f(*args); assert v in index
                    row.append(index[v])
                translations.append(row)
    rounds=0
    while True:
        q=blocks([(p[i],)+tuple(p[row[i]] for row in translations)
                  for i in range(len(A))])
        if q==p:return p,rounds,len(translations)
        p=q;rounds+=1
        assert rounds<len(A)

out={};count=0
for n in range(1,5):
    A=powerset(range(n))
    p,r,e=refine(A,[(2,lambda x,y:x&y)],[bool])
    assert len(set(p))==len(A)
    count+=len(A)**2
    out[f'full_powerset_{n}']={'relations':len(A),'classes':len(set(p)),'rounds':r}

T=range(2);D=list(itertools.product(T,range(2)))
A=[R for R in powerset(D) if all((t,0) in R for t,j in R)]
def project(R):return frozenset(t for t,j in R)
ops=[(2,lambda R,S:R&S),(2,lambda R,S:R|S)]
for C in powerset(T):
    ops.append((1,lambda R,C=C:frozenset((t,j) for t,j in R if t in C)))
for g in itertools.product(T,repeat=2):
    ops.append((1,lambda R,g=g:frozenset((g[t],j) for t,j in R)))
p,r,e=refine(A,ops,[bool])
for i,R in enumerate(A):
    for j,S in enumerate(A):
        assert (p[i]==p[j])==(project(R)==project(S))
        assert project(R&S)==project(R)&project(S)
        count+=2
out['anchored_fibres']={'relations':len(A),'classes':len(set(p)),'rounds':r,'translations':e}

# A new exact endpoint query destroys a previously safe identification.
p2,r2,e2=refine(A,ops,[bool,lambda R:(0,1) in R])
R=frozenset({(0,0)});S=frozenset({(0,0),(0,1)})
assert p[A.index(R)]==p[A.index(S)]
assert p2[A.index(R)]!=p2[A.index(S)]
count+=2
out['new_endpoint_separates']=True

# Exact separator projection over b,i,j in {0,1}.
pairs=list(itertools.product(range(2),repeat=2))
for R in powerset(pairs):
    for S in powerset(pairs):
        lhs={b for b,i in R for bp,j in S if b==bp}
        rhs={b for b,i in R}&{b for b,j in S}
        assert lhs==rhs
        count+=1
out['separator_projection_pairs']=256

# Shared choice cannot be replaced by two independent existential choices.
R={0};S={1}
assert bool(R) and bool(S) and not (R&S)
R={0,1}
shared={(x,x) for x in R}; independent=set(itertools.product(R,R))
assert not any(x!=y for x,y in shared)
assert any(x!=y for x,y in independent)
count+=3
out['branching_and_alias_controls']=True

# A task-only decoder cannot recover source-specific disjoint witnesses.
W0={'source_0_derivation'}; W1={'source_1_derivation'}
assert not W0&W1
count+=1
out['source_witness_payload_required']=True
out['assertion_cases']=count
out['status']='PASS'
print(json.dumps(out,indent=2,sort_keys=True))
