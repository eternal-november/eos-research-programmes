from coupled import *
def check(es,D,H,plan):
    tr=[]
    for w,path in zip(es,plan):
        b,i,r,settled=16,13,-1,False
        assert path[0][0]==0
        for tick, row in enumerate(path[:-1]):
            assert row[:6]==[tick,b,i,r,int(settled),int(w.receipt<=tick)]
            m,k=row[6:]
            next_relay=r
            if k==-2:
                assert r==-1 and i in (13,42) and w.receipt<=tick
                next_relay=i
            if m==-2:
                assert tick<D and tick>0 and radio[r,b] and not settled
                delivered=tick!=w.drop
                tr.append((w.cut,w.short,tick,b,r,delivered))
                settled |= delivered
            def step(z,e):
                z=0 if z==-3 else z
                if z<0:return e
                assert z in adj[e]
                return e if w.blocked(e,z,tick) else z
            b,i,r=step(m,b),step(k,i),next_relay
        assert path[-1]==[len(path)-1,b,i,r,settled]
        assert b==i==0 and settled and len(path)-1<=H
    return tr
es=[Env(short=0),Env(closure=0,drop=1)]
ans,plan=solver(es,3,10,{13,42},plan=True)
assert ans
p=check(es,3,10,plan)
assert tuple(plan[0][0][6:])==tuple(plan[1][0][6:])==(-1,42)
assert [v[3] for v in p]==[42,6]
print('Probe branch (send cut, tile, relay):',[(z[2],z[3],z[4]) for z in p])
es=[Env(0),Env(0,1,1)]
ans,plan=solver(es,3,13,{13,42},plan=True,forceB={0:42,1:-2})
assert ans
p=check(es,3,13,plan)
assert [(x[2],x[-1]) for x in p]==[(1,True),(1,False),(2,True)]
print('Forced initial send with a second disturbance:',[(x[2],x[-1]) for x in p])
