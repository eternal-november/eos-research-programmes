#!/usr/bin/env python3
"""Exact finite corroboration, not a theorem prover or physical implementation.

Only run_local is the representative implementation: it branches at local coin
instructions and never calls the analytic chain/support enumerators. Exhaustive
branch exploration is a verifier strategy, not a global sampler given to owners.
All probabilities are fractions. No third-party modules, network or randomness.
"""
from collections import Counter
from dataclasses import dataclass, replace
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import ast
import inspect
import json

CHECKS = 0

def check(p, why):
    global CHECKS
    CHECKS += 1
    if not p:
        raise AssertionError(why)


def bits(n):
    return product((0, 1), repeat=n)


def parity(xs):
    v = 0
    for x in xs:
        v ^= x
    return v


# Analytic reference functions, not called by the local representative interpreter.
def chain(x, defect=None):
    r, zs = x[0], x[1:]
    rs = [r]
    for i, z in enumerate(zs, 1):
        r ^= z
        if defect and i == defect[0]:
            r ^= defect[1]
        rs.append(r)
    return (tuple(zs), tuple(rs), r)


def probe(rec, i):
    zs, rs, d = rec
    return (rs[i-1], zs[i-1], rs[i]) if i else (rs[-1], d)


def mission(rec):
    zs, rs, d = rec
    return (rs[0] ^ parity(zs), d)


def law(values):
    c = Counter(values)
    return {x: F(k, c.total()) for x, k in c.items()}


@dataclass(frozen=True)
class State:
    weight: F
    seam: int
    initial: int
    sources: tuple = ()
    outputs: tuple = ()
    events: tuple = ()


def draw(states, eid):
    """Local fair source instruction; a source name can be minted only once."""
    out = []
    for s, env in states:
        check(eid not in dict(s.sources), 'source event resampled')
        for v in (0, 1):
            out.append((replace(s, weight=s.weight/2,
                                sources=s.sources+((eid, v),),
                                events=s.events+(('draw', eid, v),)), env+(v,)))
    return out


def run_local(n, chart):
    """Execute owner-local transitions. A tile sees only a and fresh local bits.

    Trace is write-only verifier instrumentation, never an owner's input. env is
    discarded at each tile, and only one parity bit is passed to the next tile.
    Row parity computes only after actual two-bit delivery; column owner 2 sees
    b, v, not a or u. Coin IDs are stable across charts, not physical source IDs.
    """
    initial = State(F(1), 0, 0)
    states = [replace(s, seam=e[0], initial=e[0])
              for s, e in draw([(initial, ())], 'rep:r0')]
    for i in range(1, n+1, 2):
        result = []
        for old in states:
            a = old.seam
            if i == n:  # odd final cell
                for s, (u,) in draw([(old, ())], f'rep:z{i}'):
                    b = a ^ u
                    result.append(replace(s, seam=b, outputs=s.outputs+((i,u,b),),
                        events=s.events+(('xor', i, a, u, b),)))
                continue
            for su, (u,) in draw([(old, ())], f'rep:z{i}'):
                if chart == 'column':
                    b = a ^ u
                    su = replace(su, events=su.events+(('xor',i,a,u,b),('send-b',i,b)))
                    for s, (v,) in draw([(su, ())], f'rep:z{i+1}'):
                        # Owner 2 transition takes delivered b and local v only.
                        c = b ^ v
                        result.append(replace(s, seam=c,
                            outputs=s.outputs+((i,u,b),(i+1,v,c)),
                            events=s.events+(('xor',i+1,b,v,c),)))
                elif chart == 'row':
                    for s, (v,) in draw([(su, ())], f'rep:z{i+1}'):
                        delivery = (u,v)
                        b = a ^ delivery[0]
                        c = b ^ delivery[1]
                        result.append(replace(s, seam=c,
                            outputs=s.outputs+((i,u,b),(i+1,v,c)),
                            events=s.events+(('send-uv',i,*delivery),
                                ('xor',i,a,delivery[0],b),('xor',i+1,b,delivery[1],c))))
                else:
                    raise ValueError(chart)
        states = result
    return states


def record(s):
    return (tuple(o[1] for o in s.outputs),
            (s.initial,)+tuple(o[2] for o in s.outputs), s.seam)


def fine(s):
    """Common semantic record: named sources, XOR wires, output occurrences.
    Transport-specific message records remain in chart side ledgers, not erased
    from a claimed resource equivalence. This is graph/exchange, not ordered C5.
    """
    return (s.sources, tuple(sorted(e for e in s.events if e[0]=='xor')), s.outputs)


def grouping(f, chart):
    sources, wires, outputs = f
    grouped=[]
    for pos in range(0,len(outputs),2):
        cell=outputs[pos:pos+2]
        if len(cell)==1:
            i,u,b=cell[0]; grouped.append(((('z',i,u),('r',i,b)),))
        else:
            i,u,b=cell[0]; j,v,c=cell[1]
            if chart=='column':
                grouped.append(((('z',i,u),('r',i,b)),(('z',j,v),('r',j,c))))
            else:
                grouped.append(((('z',i,u),('z',j,v)),(('r',i,b),('r',j,c))))
    return (sources, tuple(grouped))


def ungroup(g):
    sources, groups=g
    occurrences=tuple(sorted((o for tile in groups for owner in tile for o in owner),
                             key=lambda o:2*o[1]-(o[0]=='z')))
    return sources, occurrences


def subspaces(dim):
    seen={frozenset({0})}; todo=list(seen)
    while todo:
        s=todo.pop()
        for v in range(1,1<<dim):
            if v not in s:
                t=frozenset(s | {x^v for x in s})
                if t not in seen:
                    seen.add(t); todo.append(t)
    return seen


def intbits(v,dim):
    return tuple((v>>i)&1 for i in range(dim))


def compatible(records,n):
    full=[chain(x) for x in bits(n+1)]
    return all(set(map(lambda r:probe(r,i), records)) ==
               set(map(lambda r:probe(r,i), full)) for i in range(n+1))


def verify_local():
    report=[]
    for n in range(1,9):
        col,row=run_local(n,'column'),run_local(n,'row')
        cc={s.sources:s for s in col}; rr={s.sources:s for s in row}
        check(cc.keys()==rr.keys(),'persistent source assignment sets')
        check(len(col)==2**(n+1),'independent local draws')
        for s in col:
            t=rr[s.sources]
            check(fine(s)==fine(t),'pointwise fine records')
            check(ungroup(grouping(fine(s),'column'))==ungroup(grouping(fine(t),'row')),
                  'grouping coherence preserving source IDs and occurrences')
            check(record(s)==chain(tuple(v for _,v in s.sources)), 'analytic chain oracle')
            check(len(s.sources)==n+1 and len(set(dict(s.sources)))==n+1,'event identity')
            check(s.weight==F(1,2**(n+1)) and s.weight>0,'positive preparation')
            check(sum(e[0]=='send-b' for e in s.events)==n//2,'column messages')
            check(sum(e[0]=='send-uv' for e in t.events)==n//2,'row messages')
        check(sum(s.weight for s in col)==1,'normalization')
        check(law(mission(record(s)) for s in col)=={(0,0):F(1,2),(1,1):F(1,2)},'chart Q')
        report.append({'n':n,'branches_per_chart':len(col),'source_events':n+1,
                       'column_internal_message_bits':n//2,'row_internal_message_bits':2*(n//2)})
    example=run_local(2,'row')[0]
    grouped=grouping(fine(example),'row')
    naive=tuple(o for tile in grouped[1] for owner in tile for o in owner)
    check(naive!=ungroup(grouped)[1],'owner concatenation is not valid chronological coarsening')
    check(tuple((o[0],o[1]) for o in ungroup(grouped)[1])==(('z',1),('r',1),('z',2),('r',2)),
          'stable indexed merge restores original occurrence order')
    a=[{1,2},{3,4}]; b=[{1,3},{2,4}]
    check(all(len(x&y)==1 for x in a for y in b),'crossing atoms')
    check(not all(x<=y or y<=x or not x&y for x in a for y in b),'not laminar')
    return report


def verify_subspaces():
    out=[]
    for n in (2,3,4):
        allspaces=subspaces(n+1); count=proper=0
        for t in allspaces:
            recs=[chain(intbits(v,n+1)) for v in t]
            if not compatible(recs,n): continue
            count+=1; proper+=len(t)<2**(n+1)
            c=Counter(mission(r) for r in recs)
            check(c==Counter({(0,0):len(t)//2,(1,1):len(t)//2}),'equal fibers on compatible T')
            # All four external coordinate tests, including zero-probability ones.
            for y in bits(2):
                check(sum(F(mission(r)==y,len(t)) for r in recs)==F(y in ((0,0),(1,1)),2),
                      'q_T pushes preparation and pulls indicator tests')
        check(proper>0,'not only V checked')
        out.append({'n':n,'all_subspaces':len(allspaces),'compatible':count,'proper_compatible':proper})
    for n in range(2,8):
        independent=[chain(x) for x in bits(n+1)]
        correlated=[chain(x) for x in bits(n+1) if x[1]==x[2]]
        check(compatible(correlated,n),'physical correlated source compatible')
        check(law(map(mission,independent))==law(map(mission,correlated)),'correlated Q')
        check(law(r[0][0]^r[0][1] for r in independent)!=(law(r[0][0]^r[0][1] for r in correlated)),
              'extra query not licensed')
    return out


@dataclass(frozen=True)
class Certificate:
    evidence_version: int
    physical_ids: tuple
    uncertainty: str
    delta: F
    stationarity: bool
    isolation: bool
    fresh_spacing: int
    H: int
    D: int
    capture_ready: int
    compute_ticks: int
    gate_ticks: int
    selected_slot: int
    remaining: int
    check_cost: int
    service: int
    chart: str='column'


def transport(c, target, *, message_capacity, replay=False, replay_cost=0):
    # Explicit finite fixture costs, not purported measured hardware latencies.
    if not(c.stationarity and c.isolation): return None,'physical guard'
    if c.fresh_spacing<c.H+c.D: return None,'freshness'
    if c.capture_ready+c.compute_ticks+c.gate_ticks>c.selected_slot: return None,'selected-slot latency'
    if replay and message_capacity<(2 if target=='row' else 1): return None,'message capacity'
    total=c.check_cost+c.service+(replay_cost if replay else 0)
    if c.remaining<total: return None,'budget'
    return replace(c,chart=target), 'accepted'


def span(samples):
    out={0}
    for v in samples: out|={x^v for x in tuple(out)}
    return out


def encode(xs):
    return sum(v<<i for i,v in enumerate(xs))


def verify_guards_repairs():
    c=Certificate(7,('block:service','clock:1','gate:1','pulse:L','drain:1'),
        'physical K from original acquisition, not singleton V',F(1,32),True,True,13,8,5,1,4,1,7,30,8,20)
    t,why=transport(c,'row',message_capacity=0)
    check(t is not None,'certificate-only transport adds no physical message requirement')
    check(replace(t,chart='column')==c,'all physical/evidence/confidence fields unchanged')
    cases=[(replace(c,stationarity=False),'physical guard'),(replace(c,isolation=False),'physical guard'),
           (replace(c,fresh_spacing=12),'freshness'),(replace(c,selected_slot=5),'selected-slot latency'),
           (replace(c,remaining=27),'budget')]
    for bad,expected in cases:
        check(transport(bad,'row',message_capacity=2)[1]==expected,'invalidation guard')
    check(transport(c,'row',message_capacity=1,replay=True)[1]=='message capacity','changed permission checked')
    check(transport(c,'row',message_capacity=2,replay=True,replay_cost=3)[1]=='budget','repair cost can exhaust opportunity')
    check(transport(replace(c,remaining=31),'row',message_capacity=2,replay=True,replay_cost=3)[1]=='accepted','charged message repair')
    # Every deterministic strategy b=f(a,v), hence every independent randomized
    # mixture, agrees with hidden a+u on exactly half of source assignments.
    for table in bits(4):
        success=sum(table[2*a+v]==a^u for a,u,v in bits(3))
        check(F(success,8)==F(1,2),'missing u no exact common implementation')
    check(all((a^u)==a^u for a,u,v in bits(3)),'restored u delivery repair')
    defects=0
    for n in range(2,8):
        good=[chain(x) for x in bits(n+1)]
        for k in range(1,n+1):
            bad=[chain(x[:-1],(k,x[-1])) for x in bits(n+2)]
            for i in range(n+1):
                if i!=k: check(law(probe(r,i) for r in good)==law(probe(r,i) for r in bad),'retained evidence unchanged')
            check(law(probe(r,k) for r in good)!=law(probe(r,k) for r in bad),'deleted evidence mattered')
            check(law(p^d for p,d in map(mission,bad))=={0:F(1,2),1:F(1,2)},'defect risk')
            defects+=1
    good_support={encode((a,u,a^u)) for a,u in bits(2)}
    bad_support=set(range(8)); m=4
    accept_good=sum(span(xs)==good_support for xs in product(good_support,repeat=m))
    accept_bad=sum(span(xs)==good_support for xs in product(bad_support,repeat=m))
    pg=F(accept_good,4**m); pb=F(accept_bad,8**m)
    check(pg==F(105,128),'reacquisition good source exact acceptance')
    check(pb==F(105,2048) and pb<=F(1,2**m),'bad source may false accept only off confidence event')
    check(1-pg<F(2**3,2**m),'support learning dimension ceiling union bound')
    # Costed evidence repair: m fresh reservations plus span check, version update;
    # a new experiment gets its own allowance, unlike mere chart transport.
    repair_design_samples=7  # k<=3 plus ceil(log2(1/(1/16)))
    repair_cost=repair_design_samples*(c.H+c.D)+2
    check(c.remaining-repair_cost<c.service,'unaffordable evidence repair refused, not universal NO')
    repaired=replace(c,evidence_version=8,delta=c.delta+F(1,16),remaining=150-repair_cost)
    check(repaired.remaining>=c.check_cost+c.service and repaired.delta==F(3,32),'funded repair with confidence accounting')
    return {'defect_filters_checked':defects,'missing_message_deterministic_strategies':16,
            'repair_samples':m,'good_repair_acceptance':str(pg),'defect_false_acceptance':str(pb),
            'repair_design_samples':repair_design_samples,'repair_cost_fixture':repair_cost,'note':'finite fixture costs; physical guards supplied, not empirically proved'}


def verify_delay_relaxation():
    # Two candidate endpoint values: selected d=r2, unselected h=r2 as well.
    # All-evidence maximal space has h=r2; chain-only lifted relaxation allows
    # independent h. Both are actual possible linear block relations. The local
    # representative deliberately has no output h, so only Q is transported.
    selected=[chain(x) for x in bits(3)]
    full=[(r,r[2]) for r in selected]
    relaxed=[(r,h) for r in selected for h in (0,1)]
    check(set(r for r,h in full)==set(selected),'projection in this simple fixture')
    check(set(full)<set(relaxed),'omitted delay constraint not silently realized')
    check(law((r[2],h) for r,h in full)!=(law((r[2],h) for r,h in relaxed)),'unselected delay output differs')
    check(law(mission(r) for r,h in full)==law(mission(r) for r,h in relaxed),'selected Q survives relaxation')
    return {'all_evidence_full_records':len(full),'chain_only_lifted_records':len(relaxed),
            'claim':'selected Q only; no claim of all-delay output realization or general projection equality'}



def controller(initial, captured, chart, *, capacity, deadline, allow_u=True):
    """Deterministic modules consume actual captures, never representative coins.

    A supplied sensor bank captures all early zi at time 0, available at time 1;
    its O(n) buffer is charged in the fixture. Static wiring routes each local
    pair only to its owner. Each XOR and each message takes one tick; row sends
    a two-bit word in one tick only if capacity >=2. Intertile parity costs one
    tick, final gate setup one tick. No hidden access to the source/whole record.
    """
    stream=iter(captured); a=initial; now=1; messages=[]; outputs=[]
    pairs=[]
    while True:
        try: u=next(stream)
        except StopIteration: break
        v=next(stream); pairs.append((u,v))
    # pairs is the explicitly charged sensor buffer, not a sampled global law.
    for j,(u,v) in enumerate(pairs):
        if chart=='column':
            if capacity<1: return None,'capacity'
            b=a^u; now+=1
            messages.append(('internal',j,(b,))); now+=1
            c=b^v; now+=1
        else:
            if capacity<2: return None,'capacity'
            if not allow_u: return None,'missing timely u path'
            delivered=(u,v); messages.append(('internal',j,delivered)); now+=1
            b=a^delivered[0]; now+=1
            c=b^delivered[1]; now+=1
        outputs.extend((b,c)); a=c
        if j+1<len(pairs):
            messages.append(('seam',j,(c,))); now+=1
    now+=1  # selected pulse gate setup
    if now>deadline: return None,'deadline'
    return {'p':a,'time':now,'messages':tuple(messages),'outputs':tuple(outputs),
            'sensor_buffer_bits':1+2*len(pairs)},'accepted'


def verify_physical_controllers():
    rows=[]
    for n in (2,4,6,8):
        deadline=2*n+1
        tested=0
        for x in bits(n+1):
            col,_=controller(x[0],x[1:],'column',capacity=1,deadline=deadline)
            row,_=controller(x[0],x[1:],'row',capacity=2,deadline=deadline)
            expected=x[0]^parity(x[1:])
            check(col['p']==row['p']==expected,'actual-input accumulator identity')
            check(col['outputs']==row['outputs']==chain(x)[1][1:],'actual controller fine outputs')
            for d in (0,1):
                check((col['p']^d)==(row['p']^d),'same actual physical interlock hazard, any d')
            check(col['time']==row['time']==deadline,'fixture schedule')
            check(sum(len(m[2]) for m in col['messages'])==n-1,'column real delivered bits')
            check(sum(len(m[2]) for m in row['messages'])==3*n//2-1,'row real delivered bits')
            check(col['sensor_buffer_bits']==n+1,'physical capture storage charged')
            if x[1]==x[2]:
                check(row['p']==chain(x)[2],'correlated actual stream valid without fresh coin hypothesis')
            tested+=1
        check(controller(0,(0,)*n,'row',capacity=1,deadline=deadline)[1]=='capacity','physical row capacity guard')
        check(controller(0,(0,)*n,'row',capacity=2,deadline=deadline-1)[1]=='deadline','physical replay deadline guard')
        check(controller(0,(0,)*n,'row',capacity=2,deadline=deadline,allow_u=False)[1]=='missing timely u path',
              'restricted implementation invalidated, no universal impossibility')
        rows.append({'n':n,'actual_streams':tested,'deadline_ticks':deadline,
                     'column_message_bits':n-1,'row_message_bits':3*n//2-1,'capture_buffer_bits':n+1})
    # Explicit delayed stationary linear-filter realization of defect records.
    # Each output mask uses one fixed lag; at its capture tick it addresses the
    # same block-start innovation vector, not an independently redrawn copy.
    physical_cases=0
    for n in range(2,8):
        D=2*n+2; H=D+1; start=17
        for k in range(1,n+1):
            masks=[(0,1)]+[(0,1<<i) for i in range(1,n+1)]
            for i in range(1,n+1):
                mask=(1<<(i+1))-1
                if i>=k: mask^=1<<(n+1)
                masks.append((i,mask))
            masks.append((D,((1<<(n+1))-1)^(1<<(n+1))))
            records=[]
            for innovation in range(1<<(n+2)):
                vals=[]
                for lag,mask in masks:
                    capture=start+lag
                    check(capture-lag==start,'stationary lag resolves persistent block innovation')
                    vals.append((innovation&mask).bit_count()%2)
                rec=(tuple(vals[1:n+1]),(vals[0],)+tuple(vals[n+1:2*n+1]),vals[-1])
                check(rec==chain(intbits(innovation,n+2)[:-1],(k,(innovation>>(n+1))&1)),
                      'actual finite-memory filter mask equals defect witness')
                records.append(rec)
            check(law(p^d for p,d in map(mission,records))=={0:F(1,2),1:F(1,2)},'physical filter risk')
            block1=set(range(start-D,start+H))
            block2=set(range(start+H,start+2*H+D))
            check(not block1&block2,'H+D start spacing gives disjoint innovation windows')
            physical_cases+=1
    return {'controller_fixtures':rows,'stationary_delayed_defect_filters':physical_cases,
            'scope':'timing constants supplied fixture; no universal hardware/no-policy theorem'}


def scheduled_tile(a,u,v,chart):
    """The draft's seven-tick source/XOR shared-handoff template.
    Coin arguments enumerate local source outcomes; each is installed only at
    its named draw step. No XOR can read a source until its delivery occurs.
    """
    source={}; reg={'in':a}; events=[]; source_phases={1:'ready',2:'ready'}
    owners={'source1':'C1','xor1':'C1','source2':'C2','xor2':'C2'} if chart=='column' else {
        'source1':'R1','source2':'R1','xor1':'R2','xor2':'R2'}
    source[1]=u; source_phases[1]='held'; events.append(('draw',1,u))
    check(source_phases[1]=='held','delivery source held')
    reg['u']=source[1]; source_phases[1]='spent'; events.append(('copy',1,u))
    check(set(reg)=={'in','u'},'XOR1 exact delivered view')
    reg['b']=reg['in']^reg.pop('u'); events.append(('xor',1,reg['b']))
    source[2]=v; source_phases[2]='held'; events.append(('draw',2,v))
    check(source_phases[2]=='held','second delivery source held')
    reg['v']=source[2]; source_phases[2]='spent'; events.append(('copy',2,v))
    reg['c']=reg['b']^reg.pop('v'); events.append(('xor',2,reg['c']))
    reg['next']=reg['c']; events.append(('seam',reg['c']))
    check(source_phases=={1:'spent',2:'spent'},'all sources consumed once')
    check(len(events)==7,'canonical tile ticks')
    # Same b slot, one writer/reader; column crosses ownership by access policy.
    permission=(('b','xor1','write'),('b','xor2','read'))
    return (u,reg['b'],v,reg['c']),tuple(events),permission,owners


def verify_canonical_schedule_compiler():
    for a in (0,1):
        column=Counter(); row=Counter()
        for u,v in bits(2):
            c=scheduled_tile(a,u,v,'column'); r=scheduled_tile(a,u,v,'row')
            check(c[:3]==r[:3],'canonical same semantic schedule/resources')
            column[c[0]]+=F(1,4); row[r[0]]+=F(1,4)
        check(column==row and sum(column.values())==1,'canonical normalized kernels')
    xor_support={encode((a,u,a^u)) for a,u in bits(2)}
    diagonal={0,3}; accepted_bases=0
    # All ordered lists of <=3 triple rows and <=2 endpoint rows; reject merely
    # equation-satisfying but incomplete sampled spans (including all-zero data).
    for length in range(4):
        for basis in product(range(8),repeat=length):
            accept=span(basis)==xor_support
            if accept: accepted_bases+=1
            check(not accept or all(v in xor_support for v in basis),'full plane basis check')
    check(span((0,))!=xor_support,'zero rank cannot certify full plane')
    check(span((3,))==diagonal,'endpoint exact span')
    for n in range(2,10,2):
        # Distinct named registers, z and endpoint, cancel as GF2 row vectors.
        residual=set()
        for i in range(1,n+1): residual^={f'r{i-1}',f'z{i}',f'r{i}'}
        residual^={f'r{n}','d'}
        check(residual=={'r0','d'}|{f'z{i}' for i in range(1,n+1)},'telescoping certificate')
        check(2+7*(n//2)+1==7*(n//2)+3,'canonical total tick count')
    return {'local_boundary_outcomes':8,'ordered_triple_bases_accepted':accepted_bases,
            'canonical_witness_ticks':'7m+3','scope':'template/register/mask checks, not certification of claimed word-operation bound'}

def main():
    # Static dependency check excludes a hidden analytic/global support sampler
    # from the local program. This supplements, rather than proves, locality.
    tree=ast.parse(inspect.getsource(run_local))
    names={node.func.id for node in ast.walk(tree) if isinstance(node,ast.Call) and isinstance(node.func,ast.Name)}
    check(not names & {'chain','bits','subspaces','intbits'},'no global sampler in local interpreter')
    report={'scope':'Finite exact corroboration; no proof of unbounded theorem or supplied physical premises.',
            'local_interpreter':verify_local(),'compatible_subspaces':verify_subspaces(),
            'guards_and_repairs':verify_guards_repairs(),'physical_controllers':verify_physical_controllers(),
            'optional_delay':verify_delay_relaxation(),'canonical_template_compiler':verify_canonical_schedule_compiler()}
    report['assertions_passed']=CHECKS
    report['verifier_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    report['status']='PASS'
    dest=Path(__file__).with_name('verification_crossing_certificate.json')
    dest.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__': main()
