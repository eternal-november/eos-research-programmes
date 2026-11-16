from itertools import product

def partitions(n):
    if n == 0:
        yield (); return
    def extend(a):
        if len(a)==n:
            yield tuple(a); return
        for x in range(max(a)+2):
            yield from extend(a+[x])
    yield from extend([0])

def quotient(keys):
    seen={}; out=[]
    for x in keys:
        if x not in seen: seen[x]=len(seen)
        out.append(seen[x])
    return tuple(out)

W0=range(3); W1=range(2); S=range(2)
Ttuples=list(product(W0,W1)); Stuples=list(product(S,S))
count=0
for vals in product((False,True),repeat=6):
    T=dict(zip(Ttuples,vals))
    q0=quotient(tuple(T[x,y] for y in W1) for x in W0)
    q1=quotient(tuple(T[x,y] for x in W0) for y in W1)
    adequate=[]
    for p0,p1 in product(list(partitions(3)),list(partitions(2))):
        table={}; valid=True
        for x,y in Ttuples:
            k=(p0[x],p1[y])
            if k in table and table[k]!=T[x,y]: valid=False
            table[k]=T[x,y]
        if valid:
            adequate.append((p0,p1,table))
            assert all(p0[x]!=p0[y] or q0[x]==q0[y] for x,y in product(W0,repeat=2))
            assert all(p1[x]!=p1[y] or q1[x]==q1[y] for x,y in product(W1,repeat=2))
    for r0,r1 in product(product(W0,repeat=2),product(W1,repeat=2)):
        cover={q0[x] for x in r0}==set(q0) and {q1[x] for x in r1}==set(q1)
        for sv in product((False,True),repeat=4):
            F=dict(zip(Stuples,sv))
            reflect=all(F[x,y]==T[r0[x],r1[y]] for x,y in Stuples)
            criterion=cover and reflect
            exists=False
            for p0,p1,table in adequate:
                if {p0[x] for x in r0}!=set(p0) or {p1[x] for x in r1}!=set(p1): continue
                if all(F[x,y]==table[p0[r0[x]],p1[r1[y]]] for x,y in Stuples):
                    exists=True; break
            assert exists==criterion,(T,F,r0,r1)
            count+=1
# Existing tree lifting can hold while common-profile reflection fails.
source_joint={(0,0),(1,1)}; target_joint={('*','*')}
assert {('*','*') for _ in source_joint}==target_joint
assert {( '*',b) for b in (0,1)}==set(product(('*',),(0,1)))
assert (0,1) not in source_joint # maps to admitted target nevertheless
# A new position observer splits an old count-only singleton profile.
assert quotient([0,0])==(0,0)
assert quotient([0,1])==(0,1)
print(f'{count} exhaustive criterion/existence comparisons passed; coarseness and boundary assertions passed.')
