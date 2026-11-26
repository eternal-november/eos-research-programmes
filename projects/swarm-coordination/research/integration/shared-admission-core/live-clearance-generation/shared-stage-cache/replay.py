"""Generated visibility from actual callbacks and old native plant snapshots."""
import json
import subprocess
import sys
from collections import Counter
from functools import cache
from itertools import combinations, product
from pathlib import Path
import isolated as iso

# Standalone developmental test: realize #636's already published incidence as a
# logical forwarding topology. A fault acts on an old packet, not a report mask.
PATHS=((0,4),(1,3,4),(1,2),(0,1),(2,4),(0,2,3))
Q=tuple(range(len(PATHS)))
STAGES=tuple(range(5))
WORDS=tuple(product(range(2), repeat=6))
MODES=((),)+tuple((i,) for i in STAGES)+tuple(combinations(STAGES,2))
native=iso.load_native(Path(sys.argv[1])/"native_source.py")
A=native.Action
p=subprocess.Popen([sys.argv[2]],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True,bufsize=1)

def ask(*fields):
    p.stdin.write(" ".join(map(str,fields))+"\n")
    p.stdin.flush()
    return p.stdout.readline().split()

class Plant:
    def __init__(self):
        self.w=iso.make(native,False)
        self.c,self.side=self.w.agents
        self.c.dir=native.Direction.RIGHT
        self.side.x,self.side.y,self.side.dir=1,3,native.Direction.RIGHT
        self.w._recalc_grid()

    def step(self,carrier=A.NOOP,side=A.NOOP):
        native.step(self.w,(carrier.value,side.value))

    def clear(self):
        return not bool(self.w.grid[0,0,2])

    def position(self):
        return self.c.x,self.c.y

    def go(self,b):
        if self.clear()!=b:
            self.step(A.FORWARD)
            self.step(A.RIGHT)
            self.step(A.RIGHT)
        assert self.clear()==b and self.position()==((3,0) if b else (2,0))
        return int(self.clear())

def native_fixture(wanted,truth,old,cut):
    assert ask("reset")==["ok"]
    for s in old:
        assert ask("send",0,f"S{s}","Unused","old!",0)==["-","4","0"]
    g=Plant()
    stale=tuple(g.go(b) for b in wanted)
    assert stale==wanted
    truth=g.go(truth) # latch a single named source sample
    observed=list(stale)
    refreshed=set()
    graph=[]
    for j,route in enumerate(PATHS):
        value=str(truth)
        for s in route:
            ans,tx,rx=ask("send",cut,f"S{s}",f"D{s}",value,1)
            graph.append((j,s,ans,int(tx),int(rx)))
            if ans=="-":break
            assert ans==value
            value=ans
        else:
            refreshed.add(j)
            observed[j]=int(value)
    assert g.clear()==truth
    # Other work proceeds using a path and a physical cell outside the resource.
    assert ask("send",cut,"Side","Far","u",1)==["u","1","1"]
    g.step(side=A.FORWARD)
    assert (g.side.x,g.side.y)==(2,3)
    assert g.clear()==truth
    return g, (truth,tuple(observed),tuple(int(j in refreshed) for j in Q)),graph

def choices(worlds,cols,tags):
    """Exact same-information, explicit-world, finite unit-cost decision tree."""
    def read(row,i):
        return (row[1][i],row[2][i]) if tags else row[1][i]
    @cache
    def solve(indices,available,depth):
        v={worlds[i][0] for i in indices}
        if len(v)==1:return "clear" if v=={1} else "occupied"
        if depth==0:return None
        for j in available:
            nxt=tuple(i for i in available if i!=j)
            groups={}
            for i in indices:groups.setdefault(read(worlds[i],j),[]).append(i)
            if len(groups)<2:continue
            sub={a:solve(tuple(ix),nxt,depth-1) for a,ix in groups.items()}
            if all(x is not None for x in sub.values()):
                return j,sub
        return None
    def table(S):
        out={}
        for row in worlds:
            key=tuple(read(row,j) for j in S)
            if key in out and out[key]!=row[0]:return None
            out[key]=row[0]
        return out
    for k in range(len(cols)+1):
        best_fixed=next((S for S in combinations(cols,k) if table(S) is not None),None)
        if best_fixed is not None:break
    for k in range(len(cols)+1):
        tree=solve(tuple(range(len(worlds))),cols,k)
        if tree is not None:return best_fixed,k,tree
    return best_fixed,None,None

def eval_tree(tree,rec,tags):
    billed=0
    while isinstance(tree,tuple):
        j,sub=tree
        o=(rec[1][j],rec[2][j]) if tags else rec[1][j]
        billed+=1
        tree=sub[o]
    return tree=="clear",billed

rows={}
graphs={}
for cut,mode in product((4,5),MODES):
    recs=set()
    for wanted,b in product(WORDS,(0,1)):
        g,rec,graph=native_fixture(wanted,b,mode,cut)
        recs.add(rec)
        if (wanted,b)==((0,)*6,1):
            graphs[cut,mode]=graph
    rows[cut,mode]=recs
    expected=tuple(int(cut==5 or not set(r)&set(mode)) for r in PATHS)
    assert {r[2] for r in recs}=={expected}
    assert len(recs)==2**(1+6-sum(expected))

out={}
for cut,limit,tags in product((4,5),(1,2),(False,True)):
    ws=tuple(sorted(set.union(*(r for (c,m),r in rows.items() if c==cut and len(m)<=limit))))
    S,k,tree=choices(ws,Q,tags)
    key=f"{cut}/at-most-{limit}/{'qualified' if tags else 'bare'}"
    out[key]={"possibilities":len(ws),"fixed":S,"adaptive":k}
    if cut==4 and limit==1 and not tags:
        primary=tree
        assert (len(S),k)==(6,5)
    if cut==4 and limit==1 and tags:
        tagged=tree
        assert (S,k)==((0,2),2)
    if cut==5:
        assert (len(S),k)==(1,1)
    if cut==4 and limit==2 and not tags:
        assert S is None and k is None
        same=next((a,b) for a,b in product(ws,ws) if a[0]<b[0] and a[1]==b[1])
        out[key]["opposite_truth_same_bare_cache"]=same

# Consume the same protected certificate after the billed serial read process.
# No carrier action occurs from latch through commit; side work already ran.
rows_for_deadline=set.union(*(rows[4,m] for m in MODES[:6]))
stats=Counter()
for arm,(mode,wanted,b) in product(("adaptive","fixed-six","qualified"),
                                  product(MODES[:6],WORDS,(0,1))):
    plant,rec,_=native_fixture(wanted,b,mode,4)
    if arm=="fixed-six":
        # A real six-read fixed acquisition is correct, but misses
        # the 5-query deadline. No operation is sent at a forbidden cut.
        readings=tuple(rec[1][i] for i in Q)
        possible={x[0] for x in rows_for_deadline if x[1]==readings}
        assert len(possible)==1
        decision=possible.pop()
        cost=len(readings)
    elif arm=="qualified":
        for cost,j in enumerate((0,2),1):
            decision,valid=rec[1][j],rec[2][j]
            if valid:break
        assert valid
    else:
        decision,cost=eval_tree(primary,rec,False)
    assert decision==b
    stats[f"{arm}/cost_{cost}"]+=1
    if cost<=5:
        assert plant.clear()==decision # evaluator, not policy
        dst="Direct" if decision else "Bypass"
        assert ask("send",4+cost,"Old",dst,"j",1)==["j","1","1"]
        stats[f"{arm}/timely"]+=1
        if b: assert plant.go(0)==0
    else:
        stats[f"{arm}/late"]+=1
# Falsifier for the common-cut hold, even with every report genuine
# and no communications loss: the identical old view is not a current view.
plant,rec,_=native_fixture((0,)*6,1,(),4)
assert eval_tree(tagged,rec,True)[0]
plant.go(0)
assert not plant.clear()
assert ask("send",5,"Old","Direct","j",1)==["j","1","1"]
p.stdin.close()
assert p.wait()==0
print(json.dumps({"generated":2*len(MODES)*len(WORDS)*2,
                  "optimizers":out,"execution":stats,"reentry_falsifier":True,
                  "inclusive_boundary_native_witness":{
                    "live":graphs[4,(0,)],"expired":graphs[5,(0,)]}},sort_keys=True))
