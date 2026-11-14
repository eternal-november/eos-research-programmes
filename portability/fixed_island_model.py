"""Candidate fixed input-island graph; static support, not source admission."""
from __future__ import annotations
import argparse
from collections import deque
from dataclasses import dataclass
from hashlib import sha256
import json
from pathlib import Path
from constructors import natural,require
from threshold_incidence_model import check_population,neighbors,plant_group,maintenance_group

HERE=Path(__file__).resolve().parent


@dataclass(frozen=True)
class Incident:
    kind: str
    receiver: int
    origin: int|None=None


@dataclass(frozen=True)
class Group:
    population: int
    receiver: int
    kind: str
    index: int


def group_providers(group):
    require(isinstance(group,Group),'Untyped consumer group')
    check_population(group.population);natural(group.receiver,'Consumer')
    require(group.receiver<group.population,'Consumer outside cohort')
    if group.kind=='plant':
        return plant_group(group.population,group.receiver,group.index)
    require(group.kind=='maintenance','Unknown consumer group kind')
    return tuple(j for j,_ in maintenance_group(group.population,group.receiver,group.index)[1])


def installed_pair(population,receiver):
    # Fixed once at design time from physical incidence; no history/health input.
    group=plant_group(population,receiver,1)
    return group[1],group[2]


def validate_incident(population,event):
    require(isinstance(event,Incident),'Untyped incident')
    natural(event.receiver,'Incident receiver')
    require(event.receiver<population,'Incident receiver outside cohort')
    require(event.kind in ('digital','auxiliary','fixed_pair'),'Unmodeled incident kind')
    if event.kind=='auxiliary':
        require(type(event.origin) is int and event.origin in neighbors(population,event.receiver),
                'Auxiliary incident lacks actual origin endpoint')
    else:
        require(event.origin is None,'A fixed domain cannot choose new origins at acquisition')


def slots(group,event):
    providers=group_providers(group)
    population=group.population;receiver=group.receiver
    validate_incident(population,event)
    if event.receiver!=receiver:
        return frozenset({providers.index(event.receiver)}) if event.receiver in providers else frozenset()
    if event.kind=='digital':
        return frozenset({0})
    origins=(event.origin,) if event.kind=='auxiliary' else installed_pair(population,receiver)
    return frozenset(k for k,j in enumerate(providers) if k>0 and j in origins)


def projected_support(group,events):
    group_providers(group)  # Validate even when no events occur.
    events=tuple(events)
    support=frozenset().union(*(slots(group,e) for e in events))
    local_pairs=sum(e.kind=='fixed_pair' and e.receiver==group.receiver for e in events)
    bound=len(events) if local_pairs==0 else len(events)-local_pairs+2
    require(len(support)<=min(15,bound),'Constructed support exceeded proved bound')
    return support,bound


def all_domains(population):
    check_population(population)
    for receiver in range(population):
        yield Incident('digital',receiver)
        yield Incident('fixed_pair',receiver)
        for origin in neighbors(population,receiver):
            yield Incident('auxiliary',receiver,origin)


def exhaustive_mask_bound(group,budget):
    group_providers(group);natural(budget,'Diagnostic cause budget')
    population=group.population
    # Every real domain is mapped before equal static footprints are merged.
    # This quotient preserves union/cardinality only, not energy or history.
    masks={sum(1<<k for k in slots(group,e)) for e in all_domains(population)}
    reached={0:0};todo=deque([0])
    while todo:
        mask=todo.popleft();cost=reached[mask]
        if cost==budget:continue
        for extra in masks:
            combined=mask|extra
            if combined not in reached:
                reached[combined]=cost+1;todo.append(combined)
    maximum=max(mask.bit_count() for mask in reached)
    require(maximum<=budget+1,'Finite reachable-support check failed')
    return dict(physical_domains=population*42,distinct_masks=len(masks),reachable_masks=len(reached),
                maximum_affected_slots=maximum,budget=budget)


def generate():
    reports=[]
    for population,receiver,row in ((82,0,1),(86,85,1),(86,0,0)):
        group=Group(population,receiver,'plant',row)
        reports.append(dict(population=population,receiver=receiver,row=row,
            installed_pair=list(installed_pair(population,receiver)),
            **exhaustive_mask_bound(group,6)))
    huge=12*(6+2**98)+2;maps=0
    for population in (82,86,huge):
        for receiver in (0,1,population-2,population-1):
            pair=installed_pair(population,receiver)
            require(len(set(pair))==2 and all(j in neighbors(population,receiver) for j in pair),'Invalid physical pair')
            groups=[Group(population,receiver,'plant',row) for row in (0,1)]
            groups.extend(Group(population,receiver,'maintenance',a) for a in range(40))
            for group in groups:
                providers=group_providers(group)
                events=[Incident('fixed_pair',receiver)]*3+[Incident('auxiliary',receiver,providers[3]),
                        Incident('digital',providers[4]),Incident('auxiliary',providers[5],receiver)]
                support,bound=projected_support(group,events)
                require(bound==5 and len(support)<=5,'Repeated same island gained new static reach')
                maps+=1
    group=Group(86,0,'plant',1);providers=group_providers(group)
    witness=[Incident('fixed_pair',0)]+[Incident('digital',providers[k]) for k in range(3,8)]
    support,bound=projected_support(group,witness)
    require(len(support)==7 and bound==7,'Positive sharp six-token support changed')
    failures=0
    for event in (Incident('fixed_pair',0,providers[3]),Incident('auxiliary',0,0),
                  Incident('shared_calibration',0),Incident('physical_fixture',0),Incident('digital',True)):
        try:slots(group,event)
        except (ValueError,TypeError):failures+=1
        else:raise AssertionError('Out-of-class or malformed domain was silently admitted')
    for bad in (Group(False,-1,'plant',0),Group(0,-1,'plant',0),Group(86,0,'plant',True),
                Group(86,0,'maintenance',40),Group(86,0,'unknown',0)):
        for check in (lambda:projected_support(bad,[]),lambda:exhaustive_mask_bound(bad,0)):
            try:check()
            except (ValueError,TypeError):failures+=1
            else:raise AssertionError('Empty-case context escaped validation')
    try:exhaustive_mask_bound(group,True)
    except (ValueError,TypeError):failures+=1
    else:raise AssertionError('Boolean budget accepted')
    require(projected_support(group,[])==(frozenset(),0),'Valid empty support rejected')
    files=('fixed_island_model.py','FIXED-ISLANDS.md','threshold_incidence_model.py','constructors.py')
    return dict(scope='candidate static input-domain construction; physical/temporal source admission remains open',
        family='one fixed paired island per receiver, every singleton auxiliary path and direct primary/execution domain',
        bound='min(15,k) without a local pair; min(15,k-l+2) with l>=1 local-pair token occurrences',
        exhaustive=reports,seam_and_maintenance_group_cases=maps,
        six_token_sharp_support=sorted(support),repeated_island_keeps_fixed_reach=True,
        rejected_out_of_class_or_malformed=failures,
        omitted=['actual island power/reset/private execution realization','physical fixture and target-common status faults',
                 'nonlocal calibration source','region/straddling incidence','raw arrival/occupancy/retained-cause histories',
                 'recurrent source support and mission'],
        sources_sha256_lf={name:sha256((HERE/name).read_bytes().replace(b'\r\n',b'\n')).hexdigest() for name in files},
        source_admitted=False,program_completion=False)


def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true');a=p.parse_args()
    result=generate();path=HERE/'fixed_island_results.json'
    if a.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:require(json.loads(path.read_text(encoding='utf-8'))==result,'Fixed-island record differs')
    print('PASS fixed-island static support; full source admission remains open')


if __name__=='__main__':main()
