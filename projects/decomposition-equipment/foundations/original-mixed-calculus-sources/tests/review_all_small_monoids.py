"""Independent exhaustive review: labelled commutative monoids, identity 0.
No import from author's checker. Checks unary class-image criterion through order 4,
and graph-indexed kernels on empty/singleton/edgeless2/edge2 through order 3.
Finite regression only, not an unbounded proof.
"""
import itertools as it,json

def equivalences(n):
    for s in it.product(range(n),repeat=n):
        if s[0] or any(s[i]>1+max(s[:i]) for i in range(1,n)):continue
        yield tuple(frozenset(j for j in range(n) if s[j]==s[i]) for i in range(n))

def monoids(n):
    pairs=[(i,j) for i in range(1,n) for j in range(i,n)]
    for values in it.product(range(n),repeat=len(pairs)):
        t=[[0]*n for _ in range(n)]
        for i in range(n):t[0][i]=t[i][0]=i
        for (i,j),v in zip(pairs,values):t[i][j]=t[j][i]=v
        if all(t[t[a][b]][c]==t[a][t[b][c]] for a,b,c in it.product(range(n),repeat=3)):yield t

def contains(a,b):return all(a[i]<=b[i] for i in range(len(a)))
out={}; graphfamilies=0
for n in range(1,5):
    count=congs=passes=0
    for t in monoids(n):
        count+=1
        cs=[e for e in equivalences(n) if all(t[a][z] in e[t[b][z]] for a in range(n) for b in e[a] for z in range(n))]
        congs+=len(cs)
        units={a for a in range(n) if 0 in t[a]}
        for e in cs:
            fl=all({t[a][v] for v in e[u]}==e[t[a][u]] for a,u in it.product(range(n),repeat=2))
            H=e[0]
            orbit=H<=units and all(frozenset(t[a][h] for h in H)==e[a] for a in range(n))
            assert fl==orbit
            passes+=fl
        if n>3:continue
        # Hereditary graph congruences on four actual graphs: 0,P,D2,E2.
        for es in it.product(cs,repeat=4):
            if not (contains(es[0],es[1]) and contains(es[1],es[2]) and contains(es[1],es[3])):continue
            graphfamilies+=1
            fl=True
            # Nullary actual outer operation: no children to adjust.
            fl &= all(es[0][a]=={a} for a in range(n))
            # Every unary multiplication image and every binary partition shape.
            for g in range(4):
                shapes=[(g,)] + ([(0,0)] if g==0 else [(0,g),(g,0)])
                if g>=2:shapes.append((1,1))
                for shape in shapes:
                    for a in range(n):
                        for us in it.product(range(n),repeat=len(shape)):
                            target=a
                            for u in us:target=t[target][u]
                            image=set()
                            for vs in it.product(*(es[h][u] for h,u in zip(shape,us))):
                                v=a
                                for x in vs:v=t[v][x]
                                image.add(v)
                            fl &= image==set(es[g][target])
            H=es[1][0]
            predicted=all(es[0][a]=={a} for a in range(n)) and H<=units and all(es[g][a]==frozenset(t[a][h] for h in H) for g in (1,2,3) for a in range(n))
            assert fl==predicted,(t,es)
    out[str(n)]={'labelled_monoids':count,'congruences':congs,'unary_FL':passes}
out['graph_congruence_families']=graphfamilies
# Parallel actual partitions on two-vertex edgeless graph: identities cannot swap slots.
a=({0},{1});b=({1},{0});assert a!=b
assert tuple(set(U) for U in a)==a
out['partition_counterexample']='identity-profile forest retains actual ordered blocks'
print(json.dumps(out,indent=2))
