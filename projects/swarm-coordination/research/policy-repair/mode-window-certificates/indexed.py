from random import Random
from replay import common

class Heap:
    # Two-way index: one storage slot per live history, no unreaped tombstones.
    def __init__(self, vals):
        self.a=sorted((v,i) for i,v in enumerate(vals))
        self.p=[0]*len(vals); self.swaps=0
        for j,(_,i) in enumerate(self.a):self.p[i]=j
    def swap(self,i,j):
        x,y=self.a[i],self.a[j]
        self.a[i],self.a[j]=y,x
        self.p[x[1]],self.p[y[1]]=j,i
        self.swaps+=1
    def update(self,key,val):
        i=self.p[key]
        old=self.a[i]
        self.a[i]=(val,key)
        if self.a[i]<old:
            while i and self.a[i]<self.a[(i-1)//2]:
                parent=(i-1)//2
                self.swap(i,parent);i=parent
        else:
            while 2*i+1<len(self.a):
                js=range(2*i+1,min(2*i+3,len(self.a)))
                j=min(js,key=self.a.__getitem__)
                if self.a[i]<=self.a[j]:break
                self.swap(i,j);i=j
    def top(self):return self.a[0]

class Index:
    def __init__(self,h,r):
        self.lo=[Heap([-x[m][0] for x in h]) for m in range(r)]
        self.hi=[Heap([ x[m][1] for x in h]) for m in range(r)]
        self.r=r
    def update(self,i,m,l,u):
        self.lo[m].update(i,-l)
        self.hi[m].update(i,u)
    def verdict(self):
        used=set()
        for m in range(self.r):
            l,i=self.lo[m].top();u,j=self.hi[m].top()
            if -l<=u:return (m,-l),None
            used.update((i,j))
        return None,used

rng=Random(20261125);updates=0
for n in (2,4,16,128):
    for r in (1,2,3,8):
        h=[[tuple(sorted(rng.randrange(10) for _ in range(2))) for _ in range(r)] for _ in range(n)]
        x=Index(h,r)
        for _ in range(1024):
            m=rng.randrange(r); i=rng.randrange(n)
            l,u=(rng.randrange(10),rng.randrange(10))
            old=(x.lo[m].swaps,x.hi[m].swaps)
            h[i][m]=(l,u)
            x.update(i,m,l,u)
            assert all(k-o <= n.bit_length() for k,o in zip((x.lo[m].swaps,x.hi[m].swaps),old))
            guess,cert=x.verdict()
            physical=common(h,range(n),r)
            if physical:assert guess in physical and cert is None
            else:assert guess is None and len(cert)<=2*r and not common(h,cert,r)
            assert all(len(i.a)==n for i in x.lo+x.hi)
            updates+=1
print(updates,"indexed updates agree with full enumeration, no tombstone growth")
