from collections import deque
from functools import lru_cache
from itertools import product
from pathlib import Path
from project import data
import json,sys

here=Path(__file__).resolve().parent
root=Path(sys.argv[1]).resolve()
pose,edges,_=data(root)
adj={v:tuple(w for w,_ in a) for v,a in edges.items()}
rows=[tuple(map(int,l.split())) for l in (here/'contacts.tsv').read_text().splitlines()]
radio={(r,p):bool(v) for r,p,v in rows}
assert radio[-1,18] and not radio[13,18]
assert radio[-1,42] and not radio[-1,6] and radio[13,6]

class Env:
    # A former physical link (movement only) may close at a specified time.
    # Delay is the first cut the installer actually sees the named P receipt.
    # Drop suppresses exactly one Q dispatch before the broker call.
    def __init__(self,closure=None,receipt=1,drop=None,short=None):
        self.cut=closure;self.receipt=receipt;self.drop=drop;self.short=short
    def blocked(self,p,q,t):
        k=tuple(sorted((p,q)))
        return ((k==(13,42) and self.cut is not None and t>=self.cut) or
                (k==(2,3) and self.short is not None and t>=self.short))

def solver(envs, D, H, sites, plan=False, hide_traverse=False,scan=False,forceB=None):
    # Choose pair of synchronous commands from who is jointly authorized to
    # learn both move results plus P and Q acknowledgements at each next cut.
    # Time and shared receipts are ideal admitted controller inputs, not a
    # claim that the stock robot fleet can run this as one process.
    ops={}
    forceB={} if forceB is None else forceB
    @lru_cache(None)
    def dx(t,world,w):
        # optimistic future with present closures fixed, used only for pruning
        e=envs[world]
        q=deque([w]);d={w:0}
        while q:
            v=q.popleft()
            if v==0:return d[v]
            for u in adj[v]:
                if u not in d and not e.blocked(v,u,t):
                    d[u]=d[v]+1;q.append(u)
        return 200
    @lru_cache(None)
    def ok(t,worlds,b,i,r,paid,has):
        st=(t,worlds,b,i,r,paid,has)
        if paid and b==i==0:return True
        slack=H-t
        if slack<=0 or (not paid and t>=D):return False
        if any(dx(t,w,i)>slack or dx(t,w,b)+int(not paid)>slack for w in worlds):return False
        # 0 encoded as wait; tile 0 must remain a valid move so shift its name.
        move=lambda v: tuple(-3 if u==0 else u for u in adj[v])
        aa=(-1,)+move(b)
        if not paid and 0<t<D and radio.get((r,b),False):aa=(-2,)+aa
        cc=(-1,)+move(i)
        if r==-1 and has and i in sites:cc=(-2,)+cc
        endpoint={13:42,42:13,2:3,3:2}
        if scan:
            if b in endpoint:aa+=(-4,)
            if i in endpoint:cc+=(-4,)
        if t in forceB:aa=tuple(x for x in aa if x==forceB[t])
        for (a,c) in product(aa,cc):
            # Decode tile 0 using an explicit synthetic sentinel below.
            outs={}
            for w in worlds:
                e=envs[w]
                target=-1 if a in (-1,-2,-4) else (0 if a==-3 else a)
                goal=-1 if c in (-1,-2,-4) else (0 if c==-3 else c)
                v=b if target<0 or e.blocked(b,target,t) else target
                u=i if goal<0 or e.blocked(i,goal,t) else goal
                if hide_traverse and ((target>=0 and v!=target) or (goal>=0 and u!=goal)):
                    outs=None;break # no execution across an unproved edge
                rr=i if c==-2 else r
                hit=paid or (a==-2 and t!=e.drop and radio[r,b])
                key=(v,u,rr,hit,e.receipt<=t+1)
                # Scan and motion return different information; a scan
                # gives edge state at this cut, but no progress across it.
                kt=(key,e.blocked(b,endpoint[b],t) if a==-4 else None,
                         e.blocked(i,endpoint[i],t) if c==-4 else None)
                outs.setdefault(kt,[]).append(w)
            if outs is None:continue
            branches=[(t+1,tuple(ws),*key[0]) for key,ws in outs.items()]
            if all(ok(*ss) for ss in branches):
                if plan:ops[st]=(a,c,branches)
                return True
        return False
    start=(0,tuple(range(len(envs))),16,13,-1,False,False)
    v=ok(*start)
    if not plan:return v
    def peel(s,w):
        out=[]
        while s in ops:
            a,c,bs=ops[s];out.append([s[0],s[2],s[3],s[4],int(s[5]),int(s[-1]),a,c])
            s=next(y for y in bs if w in y[1])
        assert s[2:4]==(0,0) and s[5]
        return out+[list(s[0:1])+list(s[2:6])]
    return (v,[peel(start,w) for w in range(len(envs))] if v else [])

def main():
    fam={
        'exclusive-mouths':[Env(short=0),Env(closure=0)],
        'exclusive-and-lost-send':[Env(short=0),Env(closure=0,drop=1)],
        'exclusive-and-late-receipt':[Env(short=0,receipt=2),Env(closure=0,receipt=2,drop=1)],
        'silent-static':[Env(),Env(0)],
        'later-closure':[Env(),Env(2)],
        'later-closure-plus-one-lost-send':[Env(),Env(2,1,1)],
        'later-close-plus-receipt-delay':[Env(),Env(2,2)],
        'separate-mouth-or-overlap':[Env(),Env(2,1,1,2)],
    }
    ar=[(),(13,),(42,),(13,42)]
    cells={}
    for name,envs in fam.items():
        table={}
        for D,H in product(range(2,7),range(8,14)):
            if D>H:continue
            ans=[solver(envs,D,H,set(s)) for s in ar]
            blind=solver(envs,D,H,{13,42},hide_traverse=True)
            static=solver(envs,D,H,{13,42},hide_traverse=True,scan=True)
            full=all(solver([e],D,H,{13,42}) for e in envs)
            assert not ans[0] or all(ans)
            assert not (ans[1] or ans[2]) or ans[3]
            assert not blind or ans[3]
            assert not ans[3] or full
            assert not static or full
            table[str(D)+':'+str(H)]=[int(i) for i in [*ans,blind,static,full]]
        cells[name]=table
        print(name,sum(v[3] for v in table.values()),sum(v[-1] and not v[3] for v in table.values()),
              sum(v[3] and not v[4] for v in table.values()),flush=True)
    for f,table in cells.items():
      print(f, {k:v for k,v in table.items() if v[3]>v[0] or v[-1]>v[3] or v[3]>v[4]})
    (here/'results.json').write_text(json.dumps(cells,indent=2)+'\n')
if __name__=='__main__':main()
