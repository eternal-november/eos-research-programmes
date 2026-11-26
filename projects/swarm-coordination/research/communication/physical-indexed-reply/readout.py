"""Exact one-cut reply on site-only readout, before or without acknowledgement."""
from itertools import product
from index import color

def problem(K,replies,feedback,ack):
    # replies[(word,index,issued port)] is a nonempty set of site-side outputs.
    X=sorted({x for x,j,g in replies})
    access={}
    for x in X:
        for j in range(K):
            p=(x,j,feedback[j])
            if p not in replies: continue
            for y in replies[p]:
                access.setdefault((x,y),set()).add((j,y) if ack else (j,))
    return access

def graph(K,replies,feedback,ack):
    access=problem(K,replies,feedback,ack)
    return {a:{b for b in access if any((a[0]^b[0])>>jview[0]&1
                                        for jview in access[a]&access[b])}
            for a in access}

def direct(K,replies,feedback,ack,R):
    access=problem(K,replies,feedback,ack)
    for row in product(range(R),repeat=len(access)):
        table={}
        for v,c in zip(access,row):
            for view in access[v]:
                key=view,c
                ans=(v[0]>>view[0])&1
                if key in table and table[key]!=ans:break
                table[key]=ans
            else:continue
            break
        else:return True
    return False

def controls():
    # A site reads an additional bit of its own word. The receiver does
    # not necessarily know the readout. Per-readout colorings each fit
    # in a bit, but those colors cannot be interpreted without the readout.
    D={(x,j,0):(x>>1,) for x,j in product(range(4),range(2))}
    assert color(graph(2,D,(0,0),True),2) is not None
    assert color(graph(2,D,(0,0),False),2) is None
    # Fixed two physical ports, undecoded feedback may occur on either.
    U={(x,j,j):(j,None) for x,j in product(range(4),range(2))}
    assert color(graph(2,U,(0,1),False),2) is None
    assert color(graph(2,{p:(p[2],) for p in U},(0,1),False),2) is not None
    # Deterministically exhaust all endpoint-recognition patterns for four
    # word/index sources (2 bits of data) with declared 2-way ambiguity.
    test=0
    for worlds in ((0,1),(0,3),(0,1,2),(0,1,2,3)):
        keys=tuple((x,j,j) for x,j in product(worlds,range(2)))
        for modes in product((0,1,2),repeat=len(keys)):
            D={p:((p[2],),(None,),(p[2],None))[m]
               for p,m in zip(keys,modes)}
            for ack,R in product((False,True),(1,2)):
                assert (color(graph(2,D,(0,1),ack),R) is not None)==direct(2,D,(0,1),ack,R)
                test+=1
    return test
