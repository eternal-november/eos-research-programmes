from itertools import combinations

def closure(rows):
    a=list(rows); n=len(a)
    for i in range(n):
        for j in range(n):
            if a[j] & 1<<i: a[j] |= a[i]
    return tuple(a)

def upward(P,S):
    out=0
    for i,V in enumerate(P):
        if S & 1<<i:out|=V
    return out

def upsets(P):
    return [S for S in range(1<<len(P)) if upward(P,S)==S]

def invert(us, f):
    out={}
    for B in sorted(us,key=int.bit_count):
        out[B]=f.get(B,0)-sum(w for A,w in out.items() if A&B==A)
    return out

def evalf(U,p):
    return sum(w for A,w in p.items() if A&U==A)

def all_posets(n):
    es=list(combinations(range(n),2))
    for z in range(1<<len(es)):
        P=[1<<i for i in range(n)]
        for j,(a,b) in enumerate(es):
            if z & 1<<j:P[a]|=1<<b
        if closure(P)==tuple(P): yield tuple(P)

case_count=probe_cells=added=single=0
maxdelta={}
for n in range(2,6):
    full=(1<<n)-1
    for Pnew in all_posets(n):
        us=upsets(Pnew)
        case_count+=1
        for a,b in combinations(range(n),2):
            if Pnew[a] & 1<<b:continue
            P=list(Pnew);P[a]|=1<<b;Pold=closure(P)
            old=set(upsets(Pold))
            new=set(us)-old
            retained=full ^ (Pnew[a] | sum(1<<i for i in range(n) if Pnew[i] & 1<<b))
            # Direct enumeration of upsets of the induced residual poset.
            expected={S|Pnew[a] for S in range(1<<n) if S&retained==S and upward(Pnew,S)&retained==S}
            assert new==expected
            # Actual concentration of raw signature mass, then encoded test.
            _rows={i:(i*11+2)%7 for i in range(1<<n)}
            was={B:sum(z for U,z in _rows.items() if upward(Pold,U)==B) for B in old}
            now={B:sum(z for U,z in _rows.items() if upward(Pnew,U)==B) for B in us}
            assert {B:sum(z for U,z in now.items() if upward(Pold,U)==B) for B in old}==was
            for U in us:
                assert evalf(U,now)==evalf(U,_rows)
                if U in old:assert evalf(U,was)==evalf(U,_rows)
                probe_cells+=1
            assert invert(us,{B:evalf(B,now) for B in us})==now
            for U in new:
                p=invert(us,{U:1})
                plus={B:max(0,w) for B,w in p.items()}
                minus={B:max(0,-w) for B,w in p.items()}
                assert {B for B in us if evalf(B,plus)!=evalf(B,minus)}=={U}
                single+=1
            maxdelta[n]=max(maxdelta.get(n,0),len(new))
            added+=1
    assert maxdelta[n]==2**(n-2)
print(f'weak_posets={case_count} safe_edge_changes={added} forward_checks={probe_cells} isolated_new_cells={single} maximum_by_size={maxdelta}')

assert [U for U in upsets((1,6,4)) if evalf(U,{0:1,5:1})!=evalf(U,{1:1,4:1})]==[0]
assert [U for U in upsets((1,2)) if evalf(U,{1:1})!=evalf(U,{3:1})]==[1]
assert not [U for U in upsets((3,2)) if evalf(U,{1:1})!=evalf(U,{3:1})]
