"""Static local incidence for the candidate threshold family.

The constructor binds actual local ordinals and rank-one producer types. It
checks static geometry/support only, not source timing, recurrence or mission.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
from constructors import natural, require

HERE=Path(__file__).resolve().parent
OFFSETS=tuple(range(-20,0))+tuple(range(1,21))


def check_population(m):
    natural(m,'Regional cohort',positive=True)
    require(m>=82 and m%2==0,'Cohort must be even and at least82')


def neighbors(m,i):
    check_population(m);natural(i,'Host index')
    require(i<m,'Host outside cohort')
    return tuple((i+s)%m for s in OFFSETS)


def head_type(i):
    natural(i,'Host index')
    return (i%4)//2  # XXYY, not the baseline parity assignment.


def plant_group(m,receiver,row):
    require(row in (0,1) and type(row) is int,'Unknown plant row')
    selected=tuple(j for j in neighbors(m,receiver) if head_type(j)==row)
    require(len(selected)>=15,'Insufficient actual providers of the requested row')
    return selected[:15]


def maintenance_group(m,receiver,target_ordinal):
    natural(target_ordinal,'Target ordinal')
    require(target_ordinal<len(OFFSETS),'Target ordinal outside installed interface')
    targets=neighbors(m,receiver);target=targets[target_ordinal]
    selected=tuple(j for j in targets if target in neighbors(m,j))
    require(len(selected)>=15,'Insufficient common actual observers')
    group=selected[:15]
    # Each tuple names physical provider and its own local ordinal for target.
    return target,tuple((j,neighbors(m,j).index(target)) for j in group)


def input_slots(m,kind,host,origins,receiver,providers):
    check_population(m)
    actual_neighbors=set(neighbors(m,receiver))
    require(len(providers)==15 and all(type(j) is int and j in actual_neighbors for j in providers),
            'Provider outside actual local incidence')
    require(len(set(providers))==len(providers) and receiver not in providers,
            'Aliased provider list or self-provider')
    if kind=='shared_calibration':
        require(host is None and not origins,'Shared dependency has no fictitious local owner')
        return frozenset(k for k,j in enumerate(providers) if j%40==0)
    natural(host,'Incident host')
    require(host<m,'Incident host outside cohort')
    if kind=='digital':
        require(not origins,'Digital incident has unexpected paired origins')
        if receiver==host:return frozenset({0})
        return frozenset({providers.index(host)}) if host in providers else frozenset()
    if kind=='paired_island':
        require(len(origins)==2 and len(set(origins))==2 and
                all(type(o) is int and o in neighbors(m,host) for o in origins),
                'Pair must contain two actual neighboring origins')
        if receiver==host:
            # Primary is a different physical compartment, not an island copy.
            return frozenset(k for k,j in enumerate(providers) if k>0 and j in origins)
        return frozenset({providers.index(host)}) if host in providers else frozenset()
    require(False,'Unspecified source incident class: '+str(kind))


def region_edges(columns):
    natural(columns,'Region columns',positive=True)
    require(columns>=3,'At least six protected regions are required')
    edges=set()
    for row in (0,1):
        for j in range(columns-1):
            a,b=(row,j),(row,j+1)
            edges.add((a,b) if j%2 else (b,a))
    for j in range(columns):edges.add(((0,j),(1,j)))
    for j in range(0,columns-1,3):edges.add(((0,j),(1,j+1)))
    return tuple(sorted(edges))


def two_hop_packing(columns):
    vertices={(r,j) for r in (0,1) for j in range(columns)}
    adj={v:set() for v in vertices}
    for a,b in region_edges(columns):adj[a].add(b);adj[b].add(a)
    remaining=set(vertices);chosen=[]
    while remaining:
        v=min(remaining);chosen.append(v)
        ball={v}|adj[v]|set().union(*(adj[x] for x in adj[v]))
        remaining-=ball
    return tuple(chosen),adj


def generate():
    m_large=12*(6+2**98)+2
    populations=(82,84,86,128,m_large)
    reports=[];routes=0;groups=0
    for m in populations:
        cases=range(m) if m<1000 else sorted(set(range(82))|set(range(m-41,m)))
        type_min=[40,40];common_min=40;shared_max=0
        for i in cases:
            ns=neighbors(m,i)
            for row in (0,1):
                type_min[row]=min(type_min[row],sum(head_type(j)==row for j in ns))
                ps=plant_group(m,i,row);groups+=1
                require(len(ps)==15 and i not in ps,'Bad plant group')
                shared_max=max(shared_max,len(input_slots(m,'shared_calibration',None,(),i,ps)))
            for a,s in enumerate(OFFSETS):
                target,pairs=maintenance_group(m,i,a)
                all_common=[j for j in ns if target in neighbors(m,j)]
                require(len(all_common)==39-abs(s),'Common-observer cardinality changed')
                common_min=min(common_min,len(all_common))
                for provider,local in pairs:
                    require(neighbors(m,provider)[local]==target,'Physical target transport failed')
                    routes+=1
                ps=tuple(j for j,b in pairs);groups+=1
                require(len(input_slots(m,'digital',i,(),i,ps))==1,'Primary weight changed')
                require(len(input_slots(m,'paired_island',i,(ps[1],ps[2]),i,ps))==2,
                        'Paired cause was silently counted once')
                shared_max=max(shared_max,len(input_slots(m,'shared_calibration',None,(),i,ps)))
        require(min(type_min)>=18 and common_min>=19 and shared_max<=2,'Static class margin failed')
        reports.append(dict(m=str(m),receiver_cases=len(cases),row_provider_min=type_min,
                            common_observer_min=common_min,shared_dependency_max_slots=shared_max))
    graph_reports=[]
    for columns in (3,4,7,16,31,64):
        packing,adj=two_hop_packing(columns);vertices=set(adj)
        seen={min(vertices)};todo=list(seen)
        while todo:
            v=todo.pop()
            for n in adj[v]-seen:seen.add(n);todo.append(n)
        require(seen==vertices and max(map(len,adj.values()))<=4,'Graph is disconnected or not locally bounded')
        require(17*len(packing)>=len(vertices),'Distance-two packing count failed')
        for a,b in combinations(packing,2):
            require(b not in adj[a] and not (adj[a]&adj[b]),'Packing neighborhoods overlap')
        graph_reports.append(dict(regions=len(vertices),directed_edges=len(region_edges(columns)),
                                  degree_max=max(map(len,adj.values())),packing_size=len(packing)))
    # Actual local source supports, not a generic domain-count substitution.
    providers=plant_group(86,0,0)
    pair=input_slots(86,'paired_island',0,(providers[1],providers[2]),0,providers)
    direct=[input_slots(86,'digital',providers[k],(),0,providers) for k in range(3,8)]
    union=set(pair).union(*direct)
    require(len(union)==7,'One paired and five singleton incident supports changed')
    paired_providers=plant_group(86,0,1)
    first_pair=input_slots(86,'paired_island',0,(paired_providers[1],paired_providers[2]),0,paired_providers)
    second_pair=input_slots(86,'paired_island',0,(paired_providers[3],paired_providers[4]),0,paired_providers)
    four=[input_slots(86,'digital',paired_providers[k],(),0,paired_providers) for k in range(5,9)]
    two_pairs=set(first_pair)|set(second_pair)
    two_pairs.update(set().union(*four))
    require(len(two_pairs)==8,'Two paired plus four singleton support obstruction changed')
    return dict(scope='static incidence and regional skeleton; source realization, local-density history and mission remain open',
                source_rows={'X':[1,0],'XY':[1,1]},
                producer_keys='keys0/1 are repeated observations of one installed rank-one type; receiver backend maps select the row',
                region_cohorts=reports,physical_route_equalities=routes,consumer_groups_checked=groups,
                graph_skeleton=graph_reports,paired_plus_five_support=sorted(union),
                two_pairs_plus_four_support=sorted(two_pairs),
                two_pairs_plus_four_group=dict(population=86,receiver=0,row=1,providers=list(paired_providers)),
                six_unweighted_tokens_do_not_bound_slot_support_by_seven=True,
                source_shared_calibration_realization='open; footprint test is not a constructed global calibration service',
                sources_sha256_lf={name:sha256((HERE/name).read_bytes().replace(b'\r\n',b'\n')).hexdigest()
                                  for name in ('threshold_incidence_model.py','THRESHOLD-INCIDENCE.md','constructors.py')},
                program_completion=False,positive_scaling_realized=False)


def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true');a=p.parse_args()
    result=generate();path=HERE/'threshold_incidence_results.json'
    if a.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:require(json.loads(path.read_text(encoding='utf-8'))==result,'Incidence record differs')
    print('PASS static threshold-family incidence; positive source/scaling remains open')


if __name__=='__main__':main()
