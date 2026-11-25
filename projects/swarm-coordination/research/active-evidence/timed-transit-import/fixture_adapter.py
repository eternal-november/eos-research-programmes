"""Load planar data as explicit directed occupancy, not radio reachability."""
from macro import *
from mission import Fixture,synth,execute
from reference import reference
from collections import deque
import json

def dir_id(a,b):
    return "/".join(map(str,(*a,*b)))

def node(a):
    return ":".join(map(str,a))

def compile_config(A,pins,ds,microworlds,common):
    K,H=chains(A,set(pins))
    C=H+[tuple(reversed(p)) for p in H]
    d=dict(common)
    d["arcs"]=[];data=[]
    for p in C:
        if any((a,b) not in ds for a,b in zip(p,p[1:])):continue
        id=">".join(map(node,p))
        assert p[0]!=p[-1]
        length=sum(ds[a,b] for a,b in zip(p,p[1:]))
        e={"id":id,"src":node(p[0]),"dst":node(p[-1]),
           "dur":length,"cost":length,"local_visibility":p[0] in pins,
           "physical_trace":[[list(a),list(b),ds[a,b]] for a,b in zip(p,p[1:])]}
        d["arcs"].append(e)
    worlds=[]
    for w,raw in microworlds:
        v=dict(w);v["launch_bans"]={};v["entry_down"]={}
        assert set(raw)<=set(ds)
        for e in d["arcs"]:
            hops=e["physical_trace"]
            p=tuple(tuple(u) for u,_,_ in hops)+(tuple(hops[-1][1]),)
            D,W=forbidden(p,ds,raw)
            assert D==e["dur"]
            if W:v["launch_bans"][e["id"]]=[list(b) for b in W]
            if (p[0],p[1]) in raw:v["entry_down"][e["id"]]=raw[p[0],p[1]]
        worlds.append(v)
    d["worlds"]=worlds
    return d

class TransitFixture(Fixture):
    def __init__(self,d):
        super().__init__(d)
        for w in self.worlds:
            for k in ("launch_bans","entry_down"):
                assert set(w.get(k,{}))<=self.arcs.keys()
                for v in w.get(k,{}).values():
                    assert all(type(a) is int and type(b) is int and 0<=a<b for a,b in v)
    def can_visit(self,i,arc,t,d):
        assert d==self.arcs[arc]["dur"]
        return super().can_visit(i,arc,t,d) and can_enter(t,
                          self.worlds[i].get("launch_bans",{}).get(arc,()))
    def observe(self,i,s):
        # Reading the corresponding physical first door is not an oracle
        # for the rest of the travel interval or all constituent tiles.
        visible=tuple(a for a,b in self.arcs.items() if b["src"]==s.loc
                      and b.get("local_visibility",False)
                      and self.exists_during(i,"entry_down",a,s.tick,s.tick+1))
        return (s.tick,s.loc,visible,s.evidence,s.held,s.charge,s.receipts,
                s.busy_until>s.tick,s.failed,s.rounds)

def cycle(A):
    c=None
    # Shortest undirected simple cycle, ties by sorted endpoints. This
    # predeclared development graph is not a blinded or held-out choice.
    for u,b in sorted((a,b) for a in A for b in A[a] if a<b):
        Q=[u];prev={u:None}
        for a in Q:
            if a==b:break
            for v in sorted(A[a]):
                if {a,v}=={u,b} or v in prev:continue
                Q.append(v);prev[v]=a
        if b not in prev:continue
        P=[b]
        while P[-1]!=u:P.append(prev[P[-1]])
        if len(P)<8:continue
        k=(len(P),tuple(reversed(P)))
        if c is None or k<c:c=k
    assert c is not None
    return c[1]

def semantics(extra_cut=None):
    A=development_cells()
    P=cycle(A)
    xs={p:set() for p in P}
    for a,b in zip(P,(*P[1:],P[0])):
        xs[a].add(b);xs[b].add(a)
    length=len(P);assert length>=6
    S,G=P[0],P[length//2];L,R=P[1],P[-1]
    C={"start":node(S),"base":node(G),"start_epoch":0,"egress_due":14,
       "battery":35,"round_d":1,"send_cost":1,"round_limit":1,"all_in_round":True,
       "command_nodes":[node(L),node(R),node(S)],"ack":True,
       "reports":[{"id":"A","deadline":10},{"id":"B","deadline":10}],
       "slots":[{"id":"0","stock":["A"]},{"id":"1","stock":["A","B"]},{"id":"2","stock":["B"]}],
       "probes":[{"id":"left","node":node(L),"dur":1,"cost":1,"fields":["closed","failed"],"divert":["1"]},
                 {"id":"right","node":node(R),"dur":1,"cost":1,"fields":["closed","failed"]}]}
    # Public topology only. These closure, radio and timing inputs are
    # authored source parameters, not obtained from the cave dataset.
    W=[]
    for arm,loss,edge in [("L","0",(P[2],P[3])),("R","2",(P[-2],P[-3]))]:
        # Closed reach directions only in the timed mission envelope;
        # do not infer that the measured tile mesh has one-way ducts.
        W.append(({"slots_down":{loss:[[0,40]]},"signals":{"closed":arm,"failed":loss}},
                   {edge:[(0,35)]}))
    if extra_cut is not None:
        a,b=P[-2],P[-3]
        W[0][1].setdefault((a,b),[]).append(extra_cut)
    D={(a,b):1 for a in xs for b in xs[a]}
    pins={S,G,L,R}
    spec=compile_config(xs,pins,D,W,C)
    return spec,D,W

class PointwiseTransit(TransitFixture):
    def __init__(self,d,ds,raw):
        self.ds,self.raw=ds,[u for w,u in raw]
        super().__init__(d)
    def can_visit(self,i,arc,t,d):
        assert d==self.arcs[arc]["dur"]
        hops=self.arcs[arc]["physical_trace"]
        path=tuple(tuple(u) for u,_,_ in hops)+(tuple(hops[-1][1]),)
        return Fixture.can_visit(self,i,arc,t,d) and physical(path,self.ds,self.raw[i],t)

def evaluate(d,dur,raw,H,B,trace=False):
    d["egress_due"]=H
    for r in d["reports"]:r["deadline"]=B
    f=TransitFixture(d)
    p=synth(f,extract=trace)
    ref=reference(PointwiseTransit(d,dur,raw))
    assert bool(p)==ref,(H,B)
    if p and trace:
        out=[]
        for i,w in enumerate(f.worlds):
            rows=execute(f,i,p)
            t=next(z.tick for _,_,_,z in rows if z.loc==d["base"])
            A=dict(rows[-1][-1].delivered)
            out.append((t,A))
        return out
    return p

def run():
    count=0
    for fault in [None,(4,5),(5,6),(6,7)]:
        d,dur,raw=semantics(fault)
        for H in [6,7,8,9]:
            for B in [2,3,4]:
                if B<=H:
                    evaluate(d,dur,raw,H,B)
                    count+=1
    d,dur,raw=semantics()
    H,B=next((H,B) for H in range(4,10) for B in range(2,min(6,H+1))
                     if evaluate(d,dur,raw,H,B))
    out=evaluate(d,dur,raw,H,B,trace=True)
    with open("development-mission.json","w",encoding="utf8") as file:
        json.dump(d,file,indent=2);file.write("\n")
    print("graph-derived development fixture",len(d["arcs"]),"directed arcs")
    print("exact earliest egress, then report deadline",(H,B),"actual effects",out)
    print(count,"compound mission comparisons to pointwise action/observation reference")
if __name__=="__main__":run()
