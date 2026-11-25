"""Finite source adapter for civil inspection sorties.

All quantities are indexed integer epochs declared by the fixture. The
plant emits only permitted local observations. Spec is common; worlds and
physical stock are not inputs to deployed actions. This is not a radio
propagation or rigid-body model.
"""
from collections import defaultdict
from dataclasses import dataclass, replace
from functools import cache
from itertools import combinations,product
import json

@dataclass(frozen=True)
class State:
    tick:int
    loc:str
    evidence:tuple=()
    held:tuple=()        # dedicated/shared feeds held by probe operating effect
    charge:int=0
    receipts:tuple=()    # receiver-exposed report acks only
    delivered:tuple=()   # actual (report, delivery epoch); evaluator truth
    busy_until:int=-1
    booked:tuple=()      # simulated pending physical commits
    failed:bool=False
    rounds:int=0

class Fixture:
    def __init__(self,d):
        self.d=d
        self.arcs={a["id"]:a for a in d["arcs"]}
        self.probes={a["id"]:a for a in d["probes"]}
        self.slots={a["id"]:a for a in d["slots"]}
        self.reports={x["id"]:x for x in d["reports"]}
        self.worlds=d["worlds"]
        assert self.worlds and self.reports and self.slots
        assert len(d["arcs"])==len(self.arcs) and len(d["probes"])==len(self.probes)
        assert len(d["slots"])==len(self.slots) and len(d["reports"])==len(self.reports)
        assert d["start"]!=d["base"] and d["round_d"]>=1 and d["battery"]>=0
        self.resources=set(d.get("resources",[]))
        self.capacity=d.get("shared_capacity",{})
        assert all(type(c) is int and c>=0 for c in self.capacity.values())
        nodes={d["start"],d["base"]}
        for a in self.arcs.values():nodes.update((a["src"],a["dst"]))
        assert set(d["command_nodes"])<=nodes
        fields={k for p in self.probes.values() for k in p["fields"]}
        domains={"arcs_down":self.arcs.keys(), "slots_down":self.slots.keys(),
            "radio_down":set(self.slots)|{"ack"}, "probes_down":self.probes.keys(),
            "coupled_resources_down":self.resources}
        for w in self.worlds:
            for key,known in domains.items():
                assert set(w.get(key,{}))<=known,(key,w)
                for a,b in [ab for L in w.get(key,{}).values() for ab in L]:
                    assert type(a) is int and type(b) is int and 0<=a<b
            assert set(w.get("absent_stock",{}))<=self.reports.keys()
            assert all(set(A)<=self.slots.keys() for A in w.get("absent_stock",{}).values())
            assert set(w.get("signals",{}))<=fields
            for v in w.get("signals",{}).values():
                if isinstance(v,list):
                    assert all(type(t) is int and t>=0 and not isinstance(z,(list,dict)) for t,z in v)
                    assert [t for t,_ in v]==sorted({t for t,_ in v})
                else:assert not isinstance(v,dict)
        for a in self.arcs.values():
            assert a["dur"]>=1 and a["cost"]>=0 and a["src"]!=a["dst"]
            assert set(a.get("need_delivered",[]))<=self.reports.keys()
            assert set(a.get("need_receipts",[]))<=self.reports.keys()
        for x in [*self.arcs.values(),*self.probes.values(),*self.slots.values()]:
            assert set(x.get("needs",[]))<=self.resources
        for p in self.probes.values():
            assert p["dur"]>=1 and p["cost"]>=0 and p["node"] in nodes
            assert all(s in self.slots for s in p.get("divert",[]))
        for s in self.slots.values():
            assert set(s.get("band_use",{}))<=self.capacity.keys()
            assert all(type(c) is int and c>0 for c in s.get("band_use",{}).values())
            assert len(set(s["stock"]))==len(s["stock"])
            assert all(r in self.reports for r in s["stock"])
        assert all(r["deadline"]<=d["egress_due"] for r in self.reports.values())
        assert self.d["start_epoch"]<=min(r["deadline"] for r in self.reports.values())

    @classmethod
    def load(cls,p):
        with open(p,encoding="utf8") as f:return cls(json.load(f))

    @cache
    def exists_during(self,i,kind,id,a,b):
        assert a<b
        return all(end<=a or b<=start for start,end in self.worlds[i].get(kind,{}).get(id,[]))

    def can_visit(self,i,a,t,d):
        return self.exists_during(i,"arcs_down",a,t,t+d) and all(
            self.exists_during(i,"coupled_resources_down",x,t,t+d)
            for x in self.arcs[a].get("needs",[]))

    def initial(self,i):
        return State(self.d["start_epoch"],self.d["start"],charge=self.d["battery"],
                     evidence=tuple(tuple(x) for x in self.worlds[i].get("initial_observation",[])))

    def observe(self,i,s):
        # A current local edge sight is not evidence for future traversal or
        # report delivery. Busy effects expose no decisions until completion.
        visible=tuple(a for a,b in self.arcs.items() if b["src"]==s.loc and
            b.get("local_visibility",False) and self.can_visit(i,a,s.tick,1))
        return (s.tick,s.loc,visible,s.evidence,s.held,s.charge,s.receipts,
                s.busy_until>s.tick,s.failed,s.rounds)

    def dispatch_reserves(self,S):
        use=defaultdict(int)
        for sid in S:
            for bank,v in self.slots[sid].get("band_use",{}).items():
                use[bank]+=v
        return all(v<=self.capacity[bank] for bank,v in use.items())

    def choices(self,s):
        if s.failed:return ()
        if s.busy_until>s.tick:return (("advance",),)
        if s.loc==self.d["base"]:return (("wait",),)
        actions=[("wait",)]
        for name,a in self.arcs.items():
            if a["src"]==s.loc and a["cost"]<=s.charge:actions.append(("move",name))
        prior={k for k,*_ in s.evidence if isinstance(k,str)}
        for name,a in self.probes.items():
            if a["node"]==s.loc and name not in prior and a["cost"]<=s.charge:
                actions.append(("read",name))
        # Do not infer remote possession from menu. Sending a report already
        # received is redundant, not a way to learn hidden stock.
        if s.loc in self.d["command_nodes"] and self.d["send_cost"]<=s.charge and s.rounds<self.d.get("round_limit",10**6):
            first=len(self.reports) if self.d.get("all_in_round",False) else 1
            for n in range(first,min(len(self.reports),self.d.get("dispatch_limit",len(self.reports)))+1):
                for R in combinations(self.reports,n):
                    for S in product(self.slots,repeat=n):
                        if len(set(S))==n and self.dispatch_reserves(S):
                            actions.append(("send",tuple(zip(R,S))))
        return tuple(actions)

    def truth_read(self,i,name,t):
        w=self.worlds[i];p=self.probes[name]
        def val(field):
            v=w.get("signals",{}).get(field,None)
            if isinstance(v,list):
                x=[value for start,value in v if start<=t]
                return x[-1] if x else None
            return v
        return tuple(val(kind) for kind in p["fields"])

    def step(self,i,s,action):
        assert action in self.choices(s)
        w=self.worlds[i];mode=action[0];tick=s.tick
        if mode=="advance":
            t=tick+1
            if t<s.busy_until:return replace(s,tick=t)
            mode,id,started=s.booked
            return self.complete(i,replace(s,tick=t,busy_until=-1,booked=()),mode,id,started)
        if mode=="wait":return replace(s,tick=tick+1)
        id=action[1]
        if mode=="move":a=self.arcs[id];d=a["dur"];cost=a["cost"]
        elif mode=="read":a=self.probes[id];d=a["dur"];cost=a["cost"]
        else:d=self.d["round_d"];cost=self.d["send_cost"]
        held=tuple(sorted(set(s.held)|{id})) if mode=="read" and self.probes[id].get("divert",[]) else s.held
        # Pay for the attempt irrevocably at launch. Begin a nonpreemptible
        # commitment; the source effects at completion are trace-checked.
        ns=replace(s,tick=tick+1,held=held,charge=s.charge-cost,rounds=s.rounds+int(mode=="send"))
        if d>1:return replace(ns,busy_until=tick+d,booked=(mode,id,tick))
        return self.complete(i,ns,mode,id,tick)

    def complete(self,i,s,mode,id,start):
        t=s.tick
        if mode=="move":
            if not self.can_visit(i,id,start,t-start):return replace(s,failed=True)
            if not set(self.arcs[id].get("need_delivered",[]))<=dict(s.delivered).keys():
                return replace(s,failed=True)
            if not set(self.arcs[id].get("need_receipts",[]))<=dict(s.receipts).keys():
                return replace(s,failed=True)
            loc=self.arcs[id]["dst"]
            release={k for k in s.held if self.probes[k]["node"]==s.loc
                       and self.probes[k].get("release_on_departure",False)}
            # Physical release specifically defined by this source model.
            return replace(s,loc=loc,held=tuple(sorted(set(s.held)-release)))
        if mode=="read":
            ready=self.exists_during(i,"probes_down",id,start,t) and all(
                 self.exists_during(i,"coupled_resources_down",x,start,t)
                 for x in self.probes[id].get("needs",[]))
            # Every reading is tagged by its real acquisition cut.
            return replace(s,evidence=s.evidence+((id,t,*self.truth_read(i,id,t)) if ready
                                                else (id,t,"missing"),))
        assert mode=="send"
        got=set(dict(s.delivered))
        newly=[]
        for r,slot in id:
            # Authentic payload is already present at start (upstream
            # retained custody). Link path, power and slot persist to commit.
            if r in got:continue
            if r not in self.slots[slot]["stock"]:continue
            if slot in self.worlds[i].get("absent_stock",{}).get(r,[]):continue
            if any(slot in self.probes[k].get("divert",[]) for k in s.held):continue
            if not self.exists_during(i,"slots_down",slot,start,t):continue
            if not self.exists_during(i,"radio_down",slot,start,t):continue
            if any(not self.exists_during(i,"coupled_resources_down",x,start,t)
                   for x in self.slots[slot].get("needs",[])):continue
            newly.append((r,t))
        ack=tuple((r,t) for r,t in newly if self.d.get("ack",False)
                   and self.exists_during(i,"radio_down","ack",start,t))
        return replace(s,delivered=tuple(sorted([*s.delivered,*newly])),
                       receipts=tuple(sorted([*s.receipts,*ack])))

    def done(self,s):
        a=dict(s.delivered)
        return (not s.failed and s.tick<=self.d["egress_due"] and s.loc==self.d["base"]
                and all(k in a and a[k]<=x["deadline"] for k,x in self.reports.items()))

def refine(previous,observations):
    m={}
    return tuple(m.setdefault((k,z),len(m)) for k,z in zip(previous,observations))

def synth(f,report_planner=None,extract=False):
    ids=tuple(range(len(f.worlds)))
    init=tuple(f.initial(i) for i in ids);eq=(0,)*len(ids)
    trace={}
    @cache
    def go(S,O):
        t=S[0].tick
        assert all(s.tick==t for s in S)
        if any(s.failed for s in S):return False
        if any(r not in dict(s.delivered) and t>=D["deadline"] for s in S for r,D in f.reports.items()):
            return False
        if t==f.d["egress_due"]:return all(f.done(s) for s in S)
        C=refine(O,[f.observe(i,s) for i,s in zip(ids,S)])
        choices=[]
        for k in range(max(C)+1):
            clan=[(i,s) for i,s,g in zip(ids,S,C) if g==k]
            base=set.intersection(*(set(f.choices(s)) for i,s in clan))
            if report_planner:base=report_planner(f,clan,base)
            choices.append(tuple(sorted(base)))
        for joint in product(*choices):
            T=tuple(f.step(i,s,joint[k]) for i,s,k in zip(ids,S,C))
            if go(T,C):
                if extract:trace[S,O]=C,joint,T
                return True
        return False
    if not go(init,eq):return None
    if not extract:return True
    history=[() for i in ids];policy={}
    S=init;C=eq
    for t in range(f.d["start_epoch"],f.d["egress_due"]):
        G,A,T=trace[S,C]
        for i,s,g in zip(ids,S,G):
            key=history[i]+(f.observe(i,s),)
            assert policy.setdefault(key,A[g])==A[g]
            history[i]=key+(A[g],)
        S,C=T,G
    return policy

def execute(f,i,policy):
    history=();s=f.initial(i);out=[]
    while s.tick<f.d["egress_due"]:
        obs=f.observe(i,s);key=history+(obs,)
        a=policy[key];z=f.step(i,s,a)
        out.append((s.tick,obs,a,z))
        history=key+(a,);s=z
    assert f.done(s),(i,s)
    return out
