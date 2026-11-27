"""Exact pointwise certificate audit after local source changes."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from random import Random
import subprocess
import sys,json

ALL=frozenset(product((0,1),repeat=2))

class Certificate:
    def __init__(self,parents,masks,single,edge,accept):
        self.par=parents
        self.children=[[] for _ in parents]
        for i,p in enumerate(parents):
            if i:self.children[p].append(i)
        self.mask=list(masks)
        self.single=list(single)
        self.edge=list(edge)
        self.allowed=list(accept)
        self.cache={}
        self.changed=[]
        for i in reversed(range(len(parents))):self.build(i)
        self.changed.clear()
    def build(self,i):
        table={}
        for x in (0,1):
            options=[]
            for j in self.children[i]:
                options.append([(z,v-self.edge[j]*x*y) for (y,z),v in self.cache[j].items()
                                if (x,y) in self.allowed[j]])
            for kids in product(*options):
                f=self.mask[i] if x else 0
                w=-self.single[i]*x
                for z,cost in kids:f|=z;w+=cost
                key=x,f
                if key not in table or w>table[key]:table[key]=w
        self.cache[i]=table
        self.changed.append(i)
    def patch(self,index,mask=None,support=None):
        # A separately qualified edit names the actual changed factor.
        # Edge relation lives at its parent, not in the child's table.
        edits=set()
        if mask is not None:
            edits.add(index);self.mask[index]=mask
        if support is not None:
            assert index!=0
            edits.add(self.par[index]);self.allowed[index]=support
        assert edits
        scope=set()
        for i in edits:
            while i is not None:scope.add(i);i=self.par[i]
        self.changed.clear()
        for i in sorted(scope,reverse=True):self.build(i)
        assert set(self.changed)==scope
        return len(scope)
    def margin(self,score,offset=F(0)):
        if not self.cache[0]:
            return None
        return max(F(score(z))+c-offset for (_,z),c in self.cache[0].items())
    def brute(self,score,offset=F(0)):
        res=[]
        for X in product((0,1),repeat=len(self.par)):
            if any((X[p],X[i]) not in self.allowed[i] for i,p in enumerate(self.par) if i):
                continue
            f=0;cost=offset
            for i,x in enumerate(X):
                if x:f|=self.mask[i]
                cost+=self.single[i]*x
                if i:cost+=self.edge[i]*x*X[self.par[i]]
            res.append(score(f)-cost)
        return max(res,default=None)

def native_pair(radio):
    # The warehouse functions and encoder come from the previously
    # checked linked fixture, not from a solver's expected outcomes.
    from joined import load_warehouse,body
    w=load_warehouse()
    old=w.native("buffer",True,True,3,12)
    new=w.native("buffer",False,False,3,12)
    assert old["settled"] and len(old["native_old"])==1
    assert not new["settled"] and new["native_old"]==[]
    result=dict(ep=4,result=old["native_old"][0])
    assert result["result"]["objName"]=="order1"
    tape=subprocess.Popen([str(radio)],text=True,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    def ask(x):
        tape.stdin.write(x+"\n");tape.stdin.flush()
        return tape.stdout.readline().strip()
    def consume(expected,require_case,do_send,provider):
        assert ask("reset 200")=="ok"
        returned=ask(f"send 13 {provider} {body(result,173)}")=="1 173 173" if do_send else False
        return bool(returned and (not require_case or result["ep"]==expected))
    trace=[(0,int(not consume(4,True,True,"P"))),
           (0,int(not consume(4,True,True,"Q"))),
           (1,int(not consume(5,True,False,"P"))),
           (1,int(not consume(5,False,True,"Q"))),
           (1,int(not consume(5,True,True,"Q")))]
    assert trace==[(0,0),(0,0),(1,1),(1,0),(1,1)]  # missing station/report bits
    tape.stdin.close();assert tape.wait()==0
    return trace

def main():
    trace=native_pair(Path(sys.argv[2]).resolve())
    # Factored continuation returns a dual upper-payoff certificate.
    # Missing station implies missing named current report => risk is
    # dominated by the report-failure indicator only.
    eq=frozenset({(0,0),(0,1),(1,1)})
    c=Certificate((None,0),(1,1),(F(0),F(1)),(0,0),(ALL,eq))
    f=lambda z:bool(z&1)
    assert c.margin(f)==0
    assert c.patch(1,support=eq)==1 and c.margin(f)==0
    assert c.patch(1,support=eq|{trace[3]})==1 and c.margin(f)==1
    assert c.patch(1,support=eq)==1 and c.margin(f)==0
    # Authored competing set of coherent laws, kept separate from
    # native frequencies. When support expands, two quarter marginals
    # can live on disjoint histories, reaching the cap violation.
    old=[(0,0)]*3+[(1,1)]
    bad=[(0,0)]*2+[(0,1),(1,0)]
    assert [sum(x[i] for x in old) for i in (0,1)]==[sum(x[i] for x in bad) for i in (0,1)]==[1,1]
    assert F(sum(any(x) for x in old),4)==F(1,4)
    assert F(sum(any(x) for x in bad),4)==F(1,2)

    rng=Random(227);checks=0
    for n in (3,5,7,9):
      for k in range(30):
        par=[None]+[(i-1)//2 for i in range(1,n)]
        m=[rng.randrange(8) for _ in par]
        weights=[F(rng.randint(-6,7),16) for _ in par]
        ew=[F(rng.randint(-6,7),16) for _ in par]
        c=Certificate(par,m,weights,ew,[ALL]*n)
        for p in range(8):
          score=lambda flag: bool(flag&(4 if flag&1 else 2))
          idx=rng.randrange(n); y=rng.randrange(1,n)
          support=frozenset(x for x in ALL if rng.randrange(2))
          c.patch(idx,mask=rng.randrange(8))
          c.patch(y,support=support)
          assert c.margin(score)==c.brute(score)
          checks+=1
    large=[]
    for n in (31,127,511,2047):
      par=[None]+[(i-1)//2 for i in range(1,n)]
      c=Certificate(par,[1]*n,[F(1)]*n,[F(0)]*n,[ALL]*n)
      work=c.patch(n-1,mask=0)
      assert work==((n+1).bit_length()-1)
      assert c.margin(lambda flag:bool(flag))==0
      large.append([n,work])
    # No source revision/diff means an unchecked leaf can become the
    # unique bad point. Runtime effect expansion may be discovered only
    # via an interface audit, not assumed from the prior cache.
    n=31
    par=[None]+[(i-1)//2 for i in range(1,n)]
    leaves=range(n//2,n)
    limited=frozenset((x,0) for x in (0,1))
    s=[ALL if i not in leaves else limited for i in range(n)]
    c=Certificate(par,[int(i in leaves) for i in range(n)],[0]*n,[0]*n,s)
    assert c.margin(lambda h:bool(h))==0
    for i in leaves:
        c.patch(i,support=ALL)
        assert c.margin(lambda h:bool(h))==1
        c.patch(i,support=limited)
        assert c.margin(lambda h:bool(h))==0
    print(json.dumps(dict(native=trace,direct_checks=checks,balanced_rebuilds=large,
                     unqualified_diff_witnesses=len(leaves),certificate_residual=[0,1,0]),sort_keys=True,indent=2))
if __name__=="__main__":main()
