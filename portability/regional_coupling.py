"""Conservative regional coupling with explicit work, heat and fault bounds.

Exact local source equations and finite checks, not a complete Byzantine family.
No global winning theorem or permanently correct programmable pump is imported.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass, replace
from fractions import Fraction as Q
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import subprocess
import sys
import types

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[2]
BASE="edce1a21e4dacf2be677900ded765c337d41023c"
FIELD_BASE="215ecb755312f580cbd8c283b419f0958518766f"
PREFIX="theories-and-designs/byzantine-control/"
if sys.flags.optimize or sys.version_info[:2]!=(3,12):
    raise RuntimeError("Unoptimized Python 3.12 required")


def need(condition,message):
    if not condition:raise ValueError(message)


def exact(x):
    need(type(x) in (int,Q),"Exact finite int/Fraction required")
    return Q(x)


def positive_integer(x,name):
    need(type(x) is int and x>0,"Positive integer required: "+name)
    return x


def frozen(commit,path):
    return subprocess.check_output(["git","show",commit+":"+PREFIX+path],
                                   cwd=REPO).decode("utf-8-sig").replace("\r\n","\n")


def digest_text(text):
    return sha256(text.encode("utf-8")).hexdigest()


def inputs():
    names=("portability/threshold_incidence_model.py","portability/constructors.py",
        "portability/threshold_field_source_results.json",
        "portability/threshold_field_source.py","portability/THRESHOLD-FIELD-SOURCE.md",
        "local-control/port_source_results.json","local-control/port_source_model.py",
        "local-control/PORT-SOURCE.md","local-control/PORT-RESOURCES.md",
        "portability/FLOW-COMPOSITION.md")
    field_names={"portability/threshold_field_source_results.json",
                 "portability/threshold_field_source.py","portability/THRESHOLD-FIELD-SOURCE.md"}
    commits={name:FIELD_BASE if name in field_names else BASE for name in names}
    texts={name:frozen(commits[name],name) for name in names}
    field=json.loads(texts["portability/threshold_field_source_results.json"])
    previous_field=json.loads(frozen(BASE,"portability/threshold_field_source_results.json"))
    preserved=(("mechanics","total_reaction"),("thermal","side_effect_bound_with_old_normalization"),
               ("thermal","new_world_raw_rating"),("thermal","world_flow_ratio_to_old_M"),
               ("resources","unchanged_total_host_stock"))
    for section,key in preserved:
        need(field["point"][section][key]==previous_field["point"][section][key],
             "Changed consumed field quantity: "+key)
    old_resources=previous_field["point"]["resources"];new_resources=field["point"]["resources"]
    resource_changes={key:dict(before=old_resources.get(key),after=new_resources.get(key))
                      for key in sorted(set(old_resources)|set(new_resources))
                      if old_resources.get(key)!=new_resources.get(key)}
    for name,h in field["sources_sha256_lf"].items():
        text=frozen(FIELD_BASE,"portability/"+name)
        need(digest_text(text)==h,"Stale field-source input: "+name)
    for name,h in field["frozen_inputs_sha256_lf"].items():
        need(digest_text(frozen(field["source_base"],name))==h,
             "Stale transitive field input: "+name)
    world_record=json.loads(texts["local-control/port_source_results.json"])
    for name,h in world_record.get("sources",{}).items():
        need(digest_text(frozen(BASE,"local-control/"+name))==h,"Stale world input: "+name)
    world=world_record["parameters"]["world"]
    M=int(world["raw_world_flow_bound"]);m=int(world["fixed_regional_population"])
    need(m==12*(6+M)+2 and M==2**98,"Unexpected actual world scale")
    native_side=Q(field["point"]["thermal"]["side_effect_bound_with_old_normalization"])
    native_world_cap=Q(world["complete_absolute_world_work_ceiling"])+Q(field["point"]["thermal"]["new_world_raw_rating"])
    native_world_ratio=native_world_cap*Q(20,7)/M
    need(native_world_ratio==Q(field["point"]["thermal"]["world_flow_ratio_to_old_M"])<1,
         "Native source no longer fits the retained M export envelope")
    reaction=Q(field["point"]["mechanics"]["total_reaction"])
    old_w=Q(2**20+22*2**16,16)
    new_w=Q(2**20)+22*(Q(2**16)+reaction)
    new_w/=16
    need(native_side==Q(1,100)+Q(1,200)*new_w/old_w,
         "Native side-effect point not rederived")
    # Load only the frozen graph constructor and its actual executable dependency.
    cm=types.ModuleType("_regional_frozen_constructors")
    cm.__file__=str(HERE/"constructors.py");sys.modules[cm.__name__]=cm
    exec(compile(texts["portability/constructors.py"],cm.__file__,"exec"),cm.__dict__)
    previous=sys.modules.get("constructors");sys.modules["constructors"]=cm
    im=types.ModuleType("_regional_frozen_incidence")
    im.__file__=str(HERE/"threshold_incidence_model.py");sys.modules[im.__name__]=im
    try:
        exec(compile(texts["portability/threshold_incidence_model.py"],im.__file__,"exec"),im.__dict__)
    finally:
        if previous is None:sys.modules.pop("constructors",None)
        else:sys.modules["constructors"]=previous
    return dict(m=m,M=M,tau=Q(world["plant_time_per_hardware_quantum"]),
                native_side=native_side,reaction=reaction,
                native_world_cap=native_world_cap,native_world_ratio=native_world_ratio,
                source_hashes={name:digest_text(text) for name,text in texts.items()},
                source_commits=commits,field_snapshot_base=FIELD_BASE,
                preserved_field_consumers=[list(pair) for pair in preserved],
                field_resource_binding_changed=bool(resource_changes),field_resource_changes=resource_changes,
                field_transitive_hashes=field["frozen_inputs_sha256_lf"],
                field_transitive_base=field["source_base"]),im.region_edges


@dataclass(frozen=True,order=True)
class Port:
    row:int
    column:int
    coordinate:int

    def validate(self,columns):
        need(type(self.row) is int and self.row in (0,1),"Invalid physical row")
        need(type(self.column) is int and 0<=self.column<columns,"Invalid physical column")
        need(type(self.coordinate) is int and self.coordinate in (0,1),"Invalid coordinate")


@dataclass(frozen=True)
class Coupler:
    name:str
    columns:int
    pairs:tuple[tuple[Port,Port],...]
    directed:bool
    m:int
    kappa:Q=Q(1,50)
    thermal_coefficient:Q=Q(1,2500)
    stock_capacity:Q=Q(2**100)
    thermal_capacity:Q=Q(2**100)
    world_work_cap:Q=Q(2**96)
    external_inlet_cap:Q=Q(15*2**96)
    bath_coefficient:Q=Q(2**100)
    stock_leak:Q=Q(1,16)
    recovered_fraction:Q=Q(1,2)
    thermal_loss_effort:Q=Q(1,1000)
    mode_work:Q=Q(1)

    def validate(self):
        positive_integer(self.columns,"columns")
        need(self.columns>=3,"At least six protected regions required")
        positive_integer(self.m,"cohort")
        need(type(self.directed) is bool,"Direction flag must be Boolean")
        need(type(self.pairs) is tuple and bool(self.pairs),"Finite physical pairs required")
        ports=[]
        for pair in self.pairs:
            need(type(pair) is tuple and len(pair)==2,"Malformed physical pair")
            for port in pair:
                need(type(port) is Port,"Physical Port required")
                port.validate(self.columns);ports.append(port)
        need(len(set(ports))==len(ports),"Aliased physical endpoint")
        for value in (self.kappa,self.thermal_coefficient,self.stock_capacity,
                      self.thermal_capacity,self.world_work_cap,self.external_inlet_cap,
                      self.bath_coefficient,self.stock_leak,self.thermal_loss_effort,self.mode_work):
            need(exact(value)>0,"Positive physical parameter required")
        need(Q(0)<=exact(self.recovered_fraction)<=1,"Invalid recovery fraction")
        need(self.thermal_capacity==self.stock_capacity,"Selected Y-coordinate capacity mismatch")
        need(self.bath_coefficient==self.external_inlet_cap+self.world_work_cap,
             "Selected bath must cover complete positive inlet bound")

    @property
    def ports(self):
        return tuple(p for pair in self.pairs for p in pair)

    @property
    def endpoint_cap(self):
        return self.m*self.kappa


@dataclass(frozen=True)
class State:
    stock:Q
    theta:Q
    mode:int  # 0 passive, 1 active, 2 open, 3 invalid-wire/open fallback.
    requests:tuple[Q,...]


def bounded_scale(cap,value):
    return Q(1) if value<=cap else cap/value


def flow(c,state,efforts,external_inlet=Q(0)):
    c.validate()
    S=exact(state.stock);theta=exact(state.theta);a=exact(external_inlet)
    need(0<=S<=c.stock_capacity and theta>=0,"Physical stock/heat domain")
    need(type(state.mode) is int and 0<=state.mode<4,"Two-bit mode state required")
    need(type(state.requests) is tuple and len(state.requests)==len(c.pairs),
         "Fixed request storage required")
    need(set(efforts)==set(c.ports),"Missing or uninstalled effort port")
    x={p:exact(v) for p,v in efforts.items()}
    requests=tuple(exact(v) for v in state.requests)
    need(0<=a<=c.external_inlet_cap,"External work exceeds actual inlet")
    main=[];thermal=[]
    for request,(source,target) in zip(requests,c.pairs):
        delta=x[source]-x[target]
        if state.mode==0:
            main.append(c.m*c.kappa*(max(Q(0),delta) if c.directed else delta))
        elif state.mode==1:
            main.append(min(Q(1),S)*max(-c.endpoint_cap,min(c.endpoint_cap,request)))
        else:
            main.append(Q(0))
        thermal.append(c.m*c.thermal_coefficient*min(theta,Q(2))
                       if state.mode in (0,1) else Q(0))
    # Complete endpoint and gross-work caps count actual branch magnitudes,
    # before cancellation of opposed transport and thermal flows.
    absolute={p:Q(0) for p in c.ports}
    for q,t,pair in zip(main,thermal,c.pairs):
        for port in pair:absolute[port]+=abs(q)+abs(t)
    gross=sum(abs(x[p])*absolute[p] for p in c.ports)
    alpha=min(bounded_scale(c.endpoint_cap,max(absolute.values())),
              bounded_scale(c.world_work_cap,gross))
    main=tuple(alpha*q for q in main);thermal=tuple(alpha*t for t in thermal)
    contributions={p:Q(0) for p in c.ports}
    absolute={p:Q(0) for p in c.ports}
    main_power=[];thermal_power=[]
    for q,t,(source,target) in zip(main,thermal,c.pairs):
        contributions[source]-=q+t;contributions[target]+=q+t
        absolute[source]+=abs(q)+abs(t);absolute[target]+=abs(q)+abs(t)
        main_power.append((x[source]-x[target])*q)
        thermal_power.append((x[source]-x[target])*t)
    downhill=sum(max(Q(0),p) for p in main_power)
    uphill=sum(max(Q(0),-p) for p in main_power)
    if state.mode==0:
        need(uphill==0,"Passive source created uphill transport")
        stock_transfer=Q(0);transport_heat=downhill
    elif state.mode==1:
        stock_transfer=c.recovered_fraction*downhill-uphill
        transport_heat=(1-c.recovered_fraction)*downhill
    else:
        stock_transfer=transport_heat=Q(0)
    leak=c.stock_leak*S
    raw_stock=a+stock_transfer-leak
    overflow=max(Q(0),raw_stock) if S==c.stock_capacity else Q(0)
    stock_dot=raw_stock-overflow
    bath=c.bath_coefficient*theta
    thermal_loss=c.thermal_loss_effort*sum(abs(t) for t in thermal)
    heat_dot=transport_heat+sum(thermal_power)+leak+overflow-bath-thermal_loss
    world_power=sum(x[p]*contributions[p] for p in c.ports)
    gross=sum(abs(x[p])*absolute[p] for p in c.ports)
    Y=S+c.thermal_capacity*theta
    Ydot=stock_dot+heat_dot
    need(sum(contributions.values())==0,"Created protected quantity")
    need(world_power+Ydot==a-bath-thermal_loss,"Conjugate work identity failed")
    need(max(absolute.values())<=c.endpoint_cap and gross<=c.world_work_cap,
         "Complete physical cap failed")
    need(S!=0 or stock_dot>=0,"Negative stock at zero")
    need(S!=c.stock_capacity or stock_dot<=0,"Upper stock escape")
    need(theta!=0 or heat_dot>=0,"Negative heat at zero")
    P=c.external_inlet_cap+c.world_work_cap
    need(Ydot<=P-bath-thermal_loss,"Positive inlet bound spent twice")
    need(Ydot<=2*P-P*Y/c.stock_capacity,"Combined-energy comparison failed")
    return dict(main=main,thermal=thermal,scale=alpha,contributions=contributions,
        endpoint_absolute=absolute,gross_world_work=gross,world_power=world_power,
        generated_transport_heat=transport_heat,uphill_work=uphill,
        stock_dot=stock_dot,heat_dot=heat_dot,Y=Y,Ydot=Ydot,
        overflow=overflow,bath=bath,thermal_waste=thermal_loss,
        external_inlet=a)


def mode_request(c,state,mode,requests):
    """A finite paid request; invalid/unfunded attempts retain a real outcome."""
    c.validate()
    S=exact(state.stock);theta=exact(state.theta)
    need(0<=S<=c.stock_capacity and theta>=0,"Request outside physical state domain")
    need(type(state.mode) is int and 0<=state.mode<4 and type(state.requests) is tuple
         and len(state.requests)==len(c.pairs) and all(type(x) in (int,Q) for x in state.requests),
         "Request starts outside installed control-state domain")
    valid=(type(mode) is int and 0<=mode<4 and type(requests) is tuple
           and len(requests)==len(c.pairs) and
           all(type(x) in (int,Q) for x in requests))
    spend=min(S,c.mode_work)
    new_stock=S-spend;new_theta=theta+spend/c.thermal_capacity
    if valid and S>=c.mode_work:
        out=State(new_stock,new_theta,mode,tuple(map(exact,requests)))
        outcome="accepted"
    else:
        out=State(new_stock,new_theta,state.mode,state.requests)
        outcome="rejected-or-unfunded"
    need(out.stock+c.thermal_capacity*out.theta==S+c.thermal_capacity*theta,
         "A mode update created energy")
    return out,outcome


def system(columns,m,edge_constructor):
    positive_integer(columns,"columns")
    edges=edge_constructor(columns)
    zones=[]
    for k,(source,target) in enumerate(edges):
        pairs=tuple((Port(*source,j),Port(*target,j)) for j in (0,1))
        zones.append(Coupler("edge."+str(k),columns,pairs,True,m))
    for row in (0,1):
        for column in range(columns):
            zones.append(Coupler(f"inside.{row}.{column}",columns,
                ((Port(row,column,0),Port(row,column,1)),),False,m))
    need(len({z.name for z in zones})==len(zones),"Aliased physical coupling zones")
    for z in zones:z.validate()
    return tuple(zones)


def world_certificate(inp):
    m=inp["m"];M=inp["M"];W=M+6
    prototype=Coupler("world-interface",3,((Port(0,0,0),Port(1,0,0)),
                                          (Port(0,0,1),Port(1,0,1))),True,m)
    prototype.validate()
    kappa=prototype.kappa;thermal_coefficient=prototype.thermal_coefficient
    upper=Q(21,25)*(1-Q(6,m))-Q(W,m)
    lower=Q(9,25)+Q(W,m)
    service=Q(3,10)*(1-Q(6,m))-Q(W,m)
    thermal_extra=5*2*thermal_coefficient
    normal_side=inp["native_side"]+thermal_extra
    obsolete_side=inp["native_side"]+5*2*Q(1,2000)
    need(normal_side<Q(1,50) and obsolete_side>Q(1,50),
         "Thermal coefficient correction lost")
    normal_upper=Q(61,100)+Q(1,100)+Q(1,50)+5*kappa*Q(1,100)
    normal_lower=Q(59,100)-Q(1,100)-Q(1,50)-5*kappa*Q(1,100)
    robust_coupling=5*kappa
    robust_upper=Q(61,100)+Q(1,100)+Q(1,50)+robust_coupling
    robust_lower=Q(59,100)-Q(1,100)-Q(1,50)-robust_coupling
    raw_speed=Q(61,100)+1+Q(W,m)+Q(1,100)+Q(1,50)+robust_coupling
    formed_speed=raw_speed-Q(1,10)
    normal_speed=Q(61,100)+Q(9,10)+Q(W,m)+5*kappa*Q(3,10)+Q(1,100)+Q(1,50)
    need(upper>robust_upper and lower<robust_lower,"Faulted-coupler collars failed")
    need(service-robust_coupling>Q(1,10),"Conservative net service failed")
    need(raw_speed<2 and 2*raw_speed<4,"Initial/raw row slew exceeds4")
    tube=2*inp["tau"]*50000
    need(tube<Q(1,20),"Initial tube consumes safety reserve")
    return dict(m=m,M=M,node_loss_export_weight=W,upper=upper,lower=lower,
        actual_effector_service_lower=service,native_host_side=inp["native_side"],
        native_world_cap=inp["native_world_cap"],native_world_ratio=inp["native_world_ratio"],
        kappa=kappa,thermal_coefficient=thermal_coefficient,new_thermal_side=thermal_extra,
        total_normal_side=normal_side,side_slack=Q(1,50)-normal_side,
        obsolete_coefficient_total=obsolete_side,
        obsolete_coefficient_excess=obsolete_side-Q(1,50),
        normal_upper_requirement=normal_upper,normal_lower_requirement=normal_lower,
        normal_upper_margin=upper-normal_upper,normal_lower_margin=normal_lower-lower,
        robust_complete_coupling_bound=robust_coupling,
        robust_host_side_bound=Q(1,50),
        robust_upper_requirement=robust_upper,robust_lower_requirement=robust_lower,
        robust_upper_margin=upper-robust_upper,robust_lower_margin=robust_lower-lower,
        conservative_net_service_lower=service-robust_coupling,
        raw_coordinate_slew=raw_speed,raw_XY_slew=2*raw_speed,
        formed_coordinate_slew=formed_speed,normal_coordinate_slew=normal_speed,
        initial_50000q_displacement=tube,
        controller_collar_and_node_export_suppliers="conditional, not inferred from token labels",
        thermal_paths_inside_robust_endpoint_cap=True)


def active_comparison(m):
    maximum_uphill=Q(21,10000)*m
    maximum_downhill=Q(39,10000)*m
    # x_source=.35,x_target=.65 witnesses required active pump work.
    q=m*Q(1,50)*Q(35,100)
    work=(Q(65,100)-Q(35,100))*q
    need(work==maximum_uphill,"Active pump-work comparison")
    return dict(uphill_per_coordinate=maximum_uphill,
                downhill_per_coordinate=maximum_downhill,
                different_plant_law=True,unchanged_resource_dominance_claimed=False)


def checks(inp,edge_constructor):
    m=inp["m"]
    edge=Coupler("test",3,((Port(0,0,0),Port(1,0,0)),
                         (Port(0,0,1),Port(1,0,1))),True,m)
    edge.validate();cap=edge.endpoint_cap
    effort_cases=((Q(3,5),Q(2,5)),(Q(2,5),Q(3,5)),(Q(1,2),Q(1,2)),
                  (Q(35,100),Q(65,100)),(Q(-3),Q(9)),(Q(1000),Q(1000)))
    states=0;outside=0
    for (a,b),(c,d) in product(effort_cases,repeat=2):
        x=dict(zip(edge.ports,(a,b,c,d)))
        for mode,S,theta,charge in product(range(4),(Q(0),Q(1,2),Q(1),edge.stock_capacity),
                                          (Q(0),Q(1),Q(2),Q(3)),(Q(0),edge.external_inlet_cap)):
            st=State(S,theta,mode,(cap,-cap))
            r=flow(edge,st,x,charge);states+=1
            if any(v<Q(35,100) or v>Q(65,100) for v in x.values()):outside+=1
            if mode==0 and theta<=2 and all(Q(35,100)<=v<=Q(65,100) for v in x.values()):
                need(r["scale"]==1,"Normal on-box law was silently clipped")
                for q,(source,target) in zip(r["main"],edge.pairs):
                    need(q==m*edge.kappa*max(Q(0),x[source]-x[target]),"Nominal diode mismatch")
            if mode==1 and S==0:
                need(not any(r["main"]),"Empty work store drove active transport")
    # Normal coefficient/flow bounds are symbolic; corner checks challenge the encoding.
    # Use the actual conservative bound: 2*.006m + 2*1.3*m*a*2.
    nominal_gross=2*Q(3,500)*m+2*Q(13,10)*m*edge.thermal_coefficient*2
    nominal_endpoint=Q(3,500)*m+2*m*edge.thermal_coefficient
    need(nominal_gross<edge.world_work_cap and nominal_endpoint<cap,"Nominal cap headroom failed")
    # Wrong incidence creates quantity and breaks the two-port work identity.
    q=Q(m,250)
    wrong_ports={edge.ports[0]:q,edge.ports[1]:q}
    wrong_quantity=sum(wrong_ports.values())
    wrong_power=Q(3,5)*wrong_ports[edge.ports[0]]+Q(2,5)*wrong_ports[edge.ports[1]]
    expected_heat=Q(1,5)*q
    need(wrong_quantity==2*q and wrong_power+expected_heat>0,
         "Wrong physical incidence did not expose quantity/work creation")
    # Gross work cannot be computed after cancelling opposite physical branches.
    x={p:Q(1000) for p in edge.ports}
    theta=Q(1);thermal=m*edge.thermal_coefficient
    st=State(Q(1),theta,1,(-thermal,-thermal))
    r=flow(edge,st,x)
    naive_gross=sum(abs(x[p]*r["contributions"][p]) for p in edge.ports)
    need(naive_gross==0 and r["gross_world_work"]>0 and r["scale"]<1,
         "Cancelled-branch gross-work countercase missing")
    cancellation_gross=r["gross_world_work"]
    cancellation_scale=r["scale"]
    # Active uphill flow and thermal pumping require their actual energy source.
    x={edge.ports[0]:Q(2,5),edge.ports[1]:Q(3,5),
       edge.ports[2]:Q(2,5),edge.ports[3]:Q(3,5)}
    wished_flow=cap/4
    empty=flow(edge,State(Q(0),Q(0),1,(wished_flow,wished_flow)),x)
    need(not any(empty["main"]) and not any(empty["thermal"]),"Empty source supplied work")
    need(2*wished_flow<edge.world_work_cap and wished_flow<cap,
         "Absent-funding witness also violates a separate physical cap")
    unpriced_uphill=2*(Q(1,5)*wished_flow)
    need(unpriced_uphill>0,"Unfunded active-law witness absent")
    # Two components may not each spend the same original reserve.
    start=State(Q(3,2),Q(0),0,(Q(0),Q(0)))
    first,o1=mode_request(edge,start,1,(cap,cap))
    second,o2=mode_request(edge,first,2,(Q(0),Q(0)))
    need(o1=="accepted" and o2=="rejected-or-unfunded" and second.stock==0,
         "Shared-stock request sequence incorrect")
    need(2*edge.mode_work>start.stock,"Duplicate reserve witness absent")
    # Missing cooling fails its own local invariant despite bounded zero world flow.
    stopped=State(edge.stock_capacity,Q(2),2,(Q(0),Q(0)))
    baseline=flow(edge,stopped,{p:Q(1,2) for p in edge.ports},edge.external_inlet_cap)
    uncooled_heat=baseline["heat_dot"]+baseline["bath"]
    need(uncooled_heat>0,"Absent-bath boundary disappeared")
    uncooled_time=edge.thermal_capacity/edge.external_inlet_cap
    # Open mode, full S, constant inlet: with the bath removed theta grows
    # from the admitted initial value1 to2 in this time, then exceeds2.
    need(uncooled_time>0,"No actual uncooled continuation")
    malformed=[]
    for label,call in (
        ("alias",lambda:replace(edge,pairs=((edge.ports[0],edge.ports[0]),)).validate()),
        ("missing_effort",lambda:flow(edge,start,{},0)),
        ("negative_stock",lambda:flow(edge,replace(start,stock=Q(-1)),x)),
        ("over_inlet",lambda:flow(edge,start,x,edge.external_inlet_cap+1)),
        ("floating_coefficient",lambda:replace(edge,kappa=.02).validate()),
        ("Boolean_cohort",lambda:replace(edge,m=True).validate())):
        try:call()
        except ValueError:malformed.append(label)
        else:raise AssertionError("Malformed source accepted: "+label)
    invalid,outcome=mode_request(edge,start,True,(Q(0),Q(0)))
    need(outcome=="rejected-or-unfunded" and invalid.mode==start.mode,"Malformed request acquired authority")
    graph_checks=[]
    for n in (3,4,7,16,64):
        zones=system(n,m,edge_constructor)
        ports={Port(row,column,j) for row in (0,1) for column in range(n) for j in (0,1)}
        incidence={p:0 for p in ports};net={p:Q(0) for p in ports}
        x={p:Q(3,5) if p.row==0 else Q(2,5) for p in ports}
        all_heat=Q(0);all_power=Q(0);rungs=[]
        for z in zones:
            for port in z.ports:incidence[port]+=1
            st=State(Q(0),Q(0),0,tuple(Q(0) for _ in z.pairs))
            r=flow(z,st,{p:x[p] for p in z.ports})
            for port,value in r["contributions"].items():net[port]+=value
            all_heat+=r["heat_dot"];all_power+=r["world_power"]
            if z.directed and z.pairs[0][0].column==z.pairs[0][1].column:
                rungs.append((z,r))
        need(max(incidence.values())<=5 and len(rungs)==n,"Actual local coupling incidence failed")
        need(sum(net.values())==0 and all_power+all_heat==0,"Composed physical ledger failed")
        z,r=rungs[0]
        zero=State(Q(0),Q(0),0,(Q(0),Q(0)))
        not_open,unfunded=mode_request(z,zero,2,(Q(0),Q(0)))
        need(unfunded=="rejected-or-unfunded" and not_open==zero,
             "Zero stock paid for an opening")
        common=State(Q(1),Q(0),0,(Q(0),Q(0)))
        kept,kept_status=mode_request(z,common,0,(Q(0),Q(0)))
        opened_state,open_status=mode_request(z,common,2,(Q(0),Q(0)))
        need(kept_status==open_status=="accepted" and kept.stock==opened_state.stock==0
             and kept.theta==opened_state.theta==1/z.thermal_capacity,
             "Matched ablation did not pay equal actual work/heat")
        continued=flow(z,kept,{p:x[p] for p in z.ports})
        opened=flow(z,opened_state,{p:x[p] for p in z.ports})
        need(not any(opened["contributions"].values()) and opened["heat_dot"]==-1,
             "Open branch lost its paid initial heat/bath evolution")
        need(r["main"]==(Q(m,250),Q(m,250)) and r["heat_dot"]==Q(m,625),"Initial rung witness wrong")
        need(continued["main"]==r["main"] and continued["generated_transport_heat"]==Q(m,625),
             "Paid initial state changed normal transport")
        graph_checks.append(dict(regions=2*n,zones=len(zones),incident_zone_max=max(incidence.values()),
            active_rungs=len(rungs),total_generated_heat=all_heat,
            removed_transport_flow_per_coordinate=Q(m,250),
            removed_generated_transport_heat=Q(m,625),
            paid_ablation=dict(common_pre_stock=common.stock,common_pre_theta=common.theta,
                each_request_cost=z.mode_work,common_post_stock=kept.stock,common_post_theta=kept.theta,
                passive_mode=kept.mode,open_mode=opened_state.mode,
                passive_thermal_flows=continued["thermal"],
                passive_net_heat_derivative=continued["heat_dot"],open_net_heat_derivative=opened["heat_dot"],
                heat_derivative_difference=continued["heat_dot"]-opened["heat_dot"],
                zero_stock_open_request_rejected=True),
            installed_work_capacity=len(zones)*edge.stock_capacity,
            installed_thermal_capacity=len(zones)*edge.thermal_capacity,
            actual_initial_coupler_energy=0))
    # A fixed-duration bound uses the unchanged .05 initial reserve and the
    # raw slew<2, not a shrinking safety set or a chosen favorable controller.
    Tplant=Q(1,100);Tq=Tplant/inp["tau"];difference=Q(1,5)-4*Tplant
    need(difference==Q(4,25) and 2*Tplant<Q(1,20),"Fixed initial witness tube failed")
    rate=m*edge.kappa*difference
    heat=2*m*edge.kappa*difference*difference
    total_per_Rm=(heat*Tq)/(2*m)
    need(total_per_Rm==Q(256,5),"Linear actual dissipation scaling changed")
    # One cause: actual lost source service and a separate neighboring export.
    lost_region=(0,0);export_region=(1,0);export=Q(inp["M"],4)
    physical_manifest={"lost_controller":(lost_region,0),"extra_world_port":Port(*export_region,0)}
    actual_service_loss=Q(3,5)
    weights={lost_region:actual_service_loss,export_region:export}
    need(weights[lost_region]+weights[export_region]==actual_service_loss+export,
         "Lost service cancelled an off-body export")
    need(Q(1,2)*export<2**96,"Indexed export witness exceeds body WORLD work")
    return dict(flow_states_checked=states,outside_box_states_checked=outside,
        normal_gross_work_upper=nominal_gross,normal_endpoint_flow_upper=nominal_endpoint,
        quantity_and_conjugate_work_identities=True,
        source_zero_and_upper_boundaries_checked=True,
        countercases=dict(wrong_port_created_quantity=wrong_quantity,
            wrong_port_energy_discrepancy=wrong_power+expected_heat,
            naive_cancelled_gross_work=naive_gross,actual_gross_work=cancellation_gross,
            required_common_scale=cancellation_scale,
            cancellation_witness_scope="separate outside-box raw-cap test; not a positive initialized run",
            absent_funding_uphill_work=unpriced_uphill,
            duplicate_store_requests_spend=2*edge.mode_work,duplicate_store_actual=start.stock,
            absent_bath_outward_heat=uncooled_heat,
            absent_bath_time_from_admitted_theta1_to2=uncooled_time,
            malformed_inputs_rejected=malformed,malformed_request_has_total_rejection=True),
        graph_cases=graph_checks,
        ablation=dict(initial_upper_row=Q(3,5),initial_lower_row=Q(2,5),
            original_initial_reserve=Q(1,20),plant_duration=Tplant,hardware_duration=Tq,
            minimum_rung_difference=difference,minimum_rung_flow=rate,
            minimum_two_coordinate_rung_dissipation=heat,
            total_rung_dissipation_lower_per_Rm=total_per_Rm,
            one_open_rung_is_paid_local_variation=True,matched_pre_action_stock=1,
            matched_post_action_theta=1/edge.thermal_capacity,
            generated_heat_not_net_heat_derivative=True,all_open_rungs_not_a_claimed_fault_history=True),
        incident_accounting=dict(physical_manifest=repr(physical_manifest),
            lost_source_region=list(lost_region),export_region=list(export_region),
            actual_lost_service=actual_service_loss,actual_additional_export=export,
            separate_b_and_export_retained=True,
            common_physical_cause_admission="parent raw reach map still required; no M allowance per edge"))


def serial(value):
    if isinstance(value,Q):return str(value)
    if isinstance(value,Port):return [value.row,value.column,value.coordinate]
    if isinstance(value,dict):return {str(k):serial(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):return [serial(v) for v in value]
    return value


def generate():
    inp,edges=inputs()
    certificate=world_certificate(inp)
    local=checks(inp,edges)
    actual=system(3,inp["m"],edges)[0]
    need(actual.kappa==certificate["kappa"] and actual.thermal_coefficient==certificate["thermal_coefficient"],
         "World certificate and actual coupler parameters differ")
    return serial(dict(status="derived candidate coupling source with independent bounded review and matched paid ablation",
        scope="finite actual ports, flow/energy/material bounds and conditional world interface; no full family",
        frozen_base=BASE,frozen_inputs_sha256_lf=inp["source_hashes"],
        frozen_input_commits=inp["source_commits"],field_snapshot_base=inp["field_snapshot_base"],
        preserved_field_consumers=inp["preserved_field_consumers"],
        field_resource_binding_changed=inp["field_resource_binding_changed"],
        field_resource_changes=inp["field_resource_changes"],
        field_source_transitive_base=inp["field_transitive_base"],
        field_source_transitive_hashes=inp["field_transitive_hashes"],
        world=certificate,active_law_comparison=active_comparison(inp["m"]),checks=local,
        raw_component=dict(kappa=actual.kappa,thermal_coefficient=actual.thermal_coefficient,
            work_reserve_capacity=actual.stock_capacity,thermal_capacity=actual.thermal_capacity,
            world_absolute_work_cap=actual.world_work_cap,other_inlet_cap=actual.external_inlet_cap,
            bath_coefficient=actual.bath_coefficient,recoverable_fraction=actual.recovered_fraction,
            stock_leak_rate=actual.stock_leak,thermal_waste_effort=actual.thermal_loss_effort,
            nominal_scaling_initial_work_and_heat=0,endpoint_cap_is_material_not_nominal=True),
        sources_sha256_lf={name:sha256((HERE/name).read_bytes().replace(b"\r\n",b"\n")).hexdigest()
                          for name in ("regional_coupling.py","REGIONAL-COUPLING.md")},
        python_version=sys.version,
        remaining=["source realization/admission of all complete coupler caps and bath/inlet envelope",
                   "same-history node loss/export and seven-slot information maps",
                   "coupling-to-host placement and no added private/maintenance ingress",
                   "full inventories and actual source-to-core assembly",
                   "positive recurring density, independent verification and frozen transfer"],
        positive_density_proved=False,full_family=False,program_completion=False))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    g=parser.add_mutually_exclusive_group(required=True)
    g.add_argument("--write",action="store_true")
    g.add_argument("--check",action="store_true")
    args=parser.parse_args();result=generate()
    path=HERE/"regional_coupling_results.json"
    if args.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n",encoding="utf-8",newline="\n")
    else:need(json.loads(path.read_text(encoding="utf-8"))==result,"Coupling record differs")
    print("PASS actual regional coupling and conditional world/energy checks; full family remains open")


if __name__=="__main__":
    main()
