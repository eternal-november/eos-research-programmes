"""Dynamic coefficient replay for guarded FIFO budgets; integer event model."""
from heapq import heappop, heappush
from collections import defaultdict
import json
from random import Random

class Prefix:
    # Sparse Fenwick sums in a fixed immutable-rank universe [1,T].
    def __init__(self,T):
        self.T=T; self.tree={}; self.n=0; self.total=0
    def update(self,i,x,add):
        self.n+=1 if add else -1
        self.total+=x
        assert self.n>=0 and self.total>=0
        while i<=self.T:
            value=self.tree.get(i,0)+x
            if value:self.tree[i]=value
            else:self.tree.pop(i,None)
            i+=i&-i
    def before(self,i):
        i-=1; value=0
        while i:value+=self.tree.get(i,0);i-=i&-i
        return value

class Index:
    def __init__(self,T,fanout,cap):
        self.T=T
        self.m=dict(fanout); self.cap=dict(cap)
        self.clock=0; self.rows={}
        self.edge={};self.out=defaultdict(set);self.inc=defaultdict(set)
        self.last=defaultdict(list)
        self.total=defaultdict(int)
        self.slack={}
        self.counts=defaultdict(int)
    def top(self,s):
        h=self.last[s]
        while h and -h[0] not in self.rows:
            heappop(h)
            self.counts["heap_purges"]+=1
        return -h[0] if h else None
    def append(self,s,e,b,kind=False,k=1):
        # k identifies the required recipient's position, now known.
        assert b>0 and (not kind or 1<=k<=self.m[e])
        if kind and self.total[s]+k*b>self.cap[s]:return None
        self.clock+=1; i=self.clock
        assert i<=self.T
        self.rows[i]=(s,e,b,kind,k)
        if (s,e) not in self.edge:
            self.edge[s,e]=Prefix(self.T)
            self.out[s].add(e);self.inc[e].add(s)
        self.edge[s,e].update(i,b,True)
        if kind:
            heappush(self.last[s],-i)
            self.slack[s]=self.cap[s]-self.total[s]-k*b
        self.total[s]+=self.m[e]*b
        self.counts["appended"]+=1
        return i
    def drop(self,i):
        s,e,b,kind,k=self.rows[i]
        old=self.top(s)
        del self.rows[i]
        self.total[s]-=self.m[e]*b
        f=self.edge[s,e];f.update(i,-b,False)
        if not f.n:
            del self.edge[s,e];self.out[s].remove(e);self.inc[e].remove(s)
        if old==i:
            self.slack.pop(s)
            j=self.top(s)
            if j is not None:
                _,_,size,_,pos=self.rows[j]
                self.counts["rewind_edges"]+=len(self.out[s])
                self.slack[s]=self.cap[s]-size*pos-sum(
                    self.m[v]*self.edge[s,v].before(j) for v in self.out[s])
        elif old is not None and i<old:self.slack[s]+=self.m[e]*b
        self.counts["dropped"]+=1
    def migrate(self,i,s):
        old,e,b,kind,k=self.rows[i]
        assert kind and old!=s
        # Distinct sender ledgers; check the prospective new queue before
        # retiring anything. Caller owns atomicity and authorizes this move.
        j=self.append(s,e,b,kind,k)
        if j is not None:self.drop(i)
        return j
    def expand(self,e):
        updates={}
        for s in self.inc[e]:
            self.counts["binding_arcs"]+=1
            j=self.top(s)
            if j is not None:
                self.counts["binding_prefix_queries"]+=1
                d=self.edge[s,e].before(j)
                if d:updates[s]=d
        if any(self.slack[s]<d for s,d in updates.items()):return False
        for s in self.inc[e]:
            f=self.edge[s,e]
            self.total[s]+=f.total
            self.counts["binding_total_updates"]+=1
        self.m[e]+=1
        for s,d in updates.items():self.slack[s]-=d
        return True

class Direct:
    def __init__(self,m,c):
        self.m=dict(m);self.cap=dict(c);self.rows={};self.clock=0
        self.visits=0
    def check(self, rows, fanout, charge_work=False):
        used=defaultdict(int);slack={}
        for s,e,b,p,k in rows:
            if charge_work:self.visits+=1
            if p:
                slack[s]=self.cap[s]-used[s]-k*b
                assert k<=fanout[e]
            used[s]+=fanout[e]*b
        return dict(slack)
    def append(self,s,e,b,p,k):
        row=(s,e,b,p,k)
        if p and self.check([*self.rows.values(),row],self.m)[s]<0:return None
        self.clock+=1;self.rows[self.clock]=row;return self.clock
    def drop(self,i):self.rows.pop(i)
    def migrate(self,i,s):
        old,e,b,kind,k=self.rows[i]
        assert kind and old!=s
        # Distinct sender ledgers; check the prospective new queue before
        # retiring anything. Caller owns atomicity and authorizes this move.
        j=self.append(s,e,b,kind,k)
        if j is not None:self.drop(i)
        return j
    def expand(self,e):
        a=self.m|{e:self.m[e]+1}
        ss=self.check(self.rows.values(),a,True)
        if min(ss.values(),default=0)<0:return False
        self.m=a;return True

def sound(a,b):
    assert a.rows==b.rows and a.m==b.m
    assert a.slack==b.check(b.rows.values(),b.m)
    assert min(a.slack.values(),default=0)>=0
    for s in a.cap:
        assert a.total[s]==sum(a.m[e]*n for v,e,n,_,_ in b.rows.values() if s==v)

def main():
    R=Random(275)
    checks=0;aggregate=defaultdict(int)
    for trial in range(90):
        S=range(12); E=range(15)
        fan={e:1 for e in E};cap={s:R.randrange(50,401) for s in S}
        a=Index(192,fan,cap); b=Direct(fan,cap)
        for _ in range(160):
            k=R.randrange(10)
            if k<5 or not a.rows:
                s,e,n,p=R.choice(S),R.choice(E),R.randrange(1,35),k in (0,1)
                row=(s,e,n,p,R.randint(1,a.m[e]) if p else 1)
                assert a.append(*row)==b.append(*row)
            elif k<7:
                i=R.choice(tuple(a.rows)); a.drop(i);b.drop(i)
            elif k<9:
                e=R.choice(E)
                assert a.expand(e)==b.expand(e)
            else:
                cand=[i for i,v in a.rows.items() if v[3]]
                if cand:
                    i=R.choice(cand);s=R.choice([v for v in S if v!=a.rows[i][0]])
                    a.counts["migration_tries"]+=1
                    yes=a.migrate(i,s); assert yes==b.migrate(i,s)
                    a.counts["migrations"]+=yes is not None
            sound(a,b);checks+=1
        for k,val in a.counts.items():aggregate[k]+=val
        aggregate["full_binding_scan_rows"]+=b.visits

    # A small cut rewind cannot be read from endpoint totals at the current
    # cut. After retiring the latest report, the earlier report stays live.
    # Same total per edge and same latest prefix; order before the
    # earlier report differs. Removing the latest reveals that dependency.
    def pair(e,f):
        a=Index(20,{0:1,1:1,2:1},{0:466})
        for row in ((0,e,60,False,1),(0,1,173,True,1),(0,f,60,False,1),
                    (0,1,173,True,1)):
            assert a.append(*row)
        return a
    x,y=pair(0,2),pair(2,0)
    assert x.slack==y.slack=={0:0}
    assert [x.edge[0,e].total for e in range(3)]==[y.edge[0,e].total for e in range(3)]
    for a in (x,y):
        a.drop(4)
        assert a.slack[0]==233
        assert a.expand(0)
    assert [x.slack[0],y.slack[0]]==[173,233]
    for _ in range(2):assert x.expand(0) and y.expand(0)
    assert not x.expand(0) and y.expand(0)
    print(json.dumps(dict(checks=checks,cost=dict(aggregate),rewind=[0,233,173,233],
                          fourth_growth=[False,True]),
                     sort_keys=True,indent=2))
if __name__=="__main__":main()
