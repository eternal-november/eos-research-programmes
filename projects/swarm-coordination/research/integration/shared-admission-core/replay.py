"""Compose an explicitly modeled spatial-to-radio bridge; replay both plants."""
from collections import Counter, defaultdict
from dataclasses import replace
from itertools import product
import json, subprocess, sys
from core import Event, Fragment, Use, admitted, check, join, view

C=9
EARLY=15
LATE=30
LOCAL='coord'
NAMES=('early-local','early-remote','early-receive-alias','defer')
TX=lambda src: ('tx',src)
RX=lambda dst: ('rx',dst)
F=lambda *v:frozenset(v)
DUE={'prefix':0,'relocation':19,'delivery':18,'unrelated':3}
ROUTES={'early-local':(EARLY,'P','Base','local'),
        'early-remote':(EARLY,'Q','Second','remote'),
        'early-receive-alias':(EARLY,'Q','Base','remote'),
        'defer':(LATE,'P','Base','local')}

def event(t,k,**kw):return Event(t,k,**kw)
def meter(src,dst,size,rx=True):
    return (Use(TX(src),size,5,24),Use(RX(dst),size,5,24,rx))

def encode(space,opt,erased,path,authority,reveal,deadline,prior):
    cleared=space['real_y_relocation']
    spatial=[event(cleared,0,drop=F('bay-occupied'),
                   paid=('relocation',) if space['actual_due_paid'] else ())]
    radio=[event(0,0,uses=meter('P','Base',2),paid=('prefix',)),
           event(3,0,uses=meter('Independent','Far',1),
                 paid=('unrelated',) if space['independent_paid'] else ())]
    if opt:
        radio.append(event(9,0,uses=meter('P','Base',3,not erased)))
    if prior:
        # Distinct route: same outstanding workflow already applied.
        radio.append(event(8,0,uses=meter('Independent','Far',2),paid=('delivery',)))
    reception=(C if reveal&1 else EARLY+1)
    readings=[(reception,LOCAL,('site',cleared<=C,path,authority))]
    ongoing=(C if reveal&2 else EARLY+1)
    accounting=[(ongoing,LOCAL,('meter',opt,erased if opt else False,prior))]
    facts={'up:'+x for x in ('local','remote') if path!=x}
    facts.update('auth:'+LOCAL+':'+x for x in ('local','remote') if authority!=x)
    options={'retain':()}
    for n,(t,s,d,route) in ROUTES.items():
        # The local facility is usable only after the carrier and its load
        # finish relocating. This coupling is authored, not a warehouse RF model.
        options[n]=(event(t,1,need=F('up:'+route,'auth:'+LOCAL+':'+route),
                         absent=F('bay-occupied') if route=='local' else F(),
                         uses=meter(s,d,2),paid=('delivery',)),)
    # Here the paired instance is authored. In the separate common-cause
    # control below a single manifest is joined to multiple latent rows.
    key=(space['side'],space['case'],opt,erased,path,authority,reveal,prior)
    left=Fragment(key,tuple(readings),F('bay-occupied'),tuple(spatial))
    right=Fragment(key,tuple(accounting),frozenset(facts),tuple(radio))
    return join([left],[right],options)[0]

def direct(p,a):
    space,opt,erased,path,authority,reveal,deadline,prior = p
    if space['real_y_relocation']>19 or not space['actual_due_paid'] or not space['independent_paid']:
        return False
    if a=='retain':
        return bool(prior)
    t,s,d,r=ROUTES[a]
    if t>deadline or r in (path,authority) or prior:
        return False
    if r=='local' and space['real_y_relocation']>t:
        return False
    tx=int(s=='P')*(2*int(t<=24)+3*opt)
    rx=int(d=='Base')*(2*int(t<=24)+3*(opt and not erased))
    return max(tx,rx)+2<=5

def rows(cases,deadline):
    return [(p,encode(*p)) for s,opt,erased,path,authority,reveal,prior in product(
            cases,(0,1),(0,1),('none','local','remote'),
            ('none','local','remote'),(0,1,2,3),(0,1))
            if opt or not erased
            for p in [(s,opt,erased,path,authority,reveal,deadline,prior)]]

def main():
    cases=json.load(open(sys.argv[1]))
    # Witness spatial events as recorded by the separate live source producer,
    # not recreated by the checker from fallback policy labels.
    assert sorted({s['real_y_relocation'] for s in cases}) == [6,18,19]
    # Discard future truth as a controller input. The authorized current
    # evidence is its own flag; 'manager' may know more at the same cut.
    summary=[]
    for deadline in (18,30):
        items=rows(cases,deadline)
        clauses=defaultdict(list)
        work=Counter()
        due=DUE|{'delivery':deadline}
        ns=NAMES+('retain',)
        for p,row in items:
            clauses[view(row,LOCAL,C)].append(p)
            for a in ns:
                verdict=check(row,a,C,due,work)
                assert verdict==direct(p,a),(p,a,verdict)
        obs=admitted([r for _,r in items],LOCAL,C,due,ns)
        expected={o:tuple(a for a in ns if all(direct(p,a) for p in ps))
                  for o,ps in clauses.items()}
        assert obs==expected
        assert not obs[()]
        assert len(set.intersection(*(set(x) for x in obs.values()))) == 0
        summary.append({'deadline':deadline,'whole_rows':len(items),
                        'option_comparisons':len(items)*len(ns),
                        'receipt_classes':len(obs),'oracle_work':dict(work),
                        'solvable_classes':sum(bool(x) for x in obs.values())})
    # Replay all physical alternatives, including ones rejected by the general
    # gate. This distinguishes legal receipt, native result and design claim.
    reqs=[r for r in product((EARLY,LATE), (0,1),(0,1),(0,1),(0,1),(0,1),(0,1))
          if r[3] or not r[4]]
    reqs += [(-1,0,0,0,0,1,0),(-1,0,0,0,0,0,0)]
    cmd=''.join(' '.join(str(int(v)) for v in x)+'\n' for x in reqs)
    native=subprocess.run([sys.argv[2]],input=cmd,capture_output=True,text=True,check=True)
    results=[]
    for req,actual in zip(reqs,native.stdout.splitlines(),strict=True):
        t,sh_tx,sh_rx,opt,erase,prior,block=req
        prefix,optional,last,work,tx0,rx0,tx1,rx1=map(int,actual.split())
        assert prefix==work==1 and optional==int(opt and not erase)
        expected= int(sh_tx)*(2*int(t<=24)+3*opt)
        receive= int(sh_rx)*(2*int(t<=24)+3*(opt and not erase))
        assert tx0==int(sh_tx)*(2+3*opt) and rx0==int(sh_rx)*(2+3*(opt and not erase))
        assert last==prior+int(t>=0 and not block and max(expected,receive)+2<=5), (req,actual)
        results.append([req,list(map(int,actual.split()))])
    # Marginally possible ready+up is not a possible joint favorable row;
    # adding a resolver that distinguishes the rows still cannot fix physics.
    s6=next(s for s in cases if s['real_y_relocation']==6)
    s18=next(s for s in cases if s['real_y_relocation']==18)
    a=encode(s6,0,0,'local','remote',0,18,0)
    b=encode(s18,0,0,'none','remote',0,18,0)
    counterfeit=replace(a,facts=b.facts)
    assert check(counterfeit,'early-local',C,DUE)
    assert not check(a,'early-local',C,DUE) and not check(b,'early-local',C,DUE)
    # Same early report can be safe when a failed optional spent TX but not
    # RX, and unsafe when it reached Base. Loss of that distinction forbids
    # admission under the robust controller, not physically under both rows.
    admitted_when_distinguished=encode(s6,1,1,'none','none',3,18,0)
    not_admitted=encode(s6,1,0,'none','none',3,18,0)
    q='early-receive-alias'
    assert check(admitted_when_distinguished,q,C,DUE)
    assert not check(not_admitted,q,C,DUE)
    left=encode(s6,1,1,'none','none',1,18,0)
    right=encode(s6,1,0,'none','none',1,18,0)
    assert view(left,LOCAL,C)==view(right,LOCAL,C)
    assert q not in next(iter(admitted([left,right],LOCAL,C,DUE,NAMES).values()))
    # A decision made against a positive receipt at the cut is not safe if
    # the matching permission can subsequently be withdrawn before use.
    auth=encode(s6,0,0,'remote','none',3,18,0)
    stale=replace(auth,events=auth.events+(event(14,0,drop=F('auth:coord:local')),))
    assert view(auth,LOCAL,C)==view(stale,LOCAL,C)
    assert check(auth,'early-local',C,DUE)
    assert not check(stale,'early-local',C,DUE)
    assert admitted([auth,stale],LOCAL,C,DUE,NAMES+('retain',))=={view(auth,LOCAL,C):()}
    # Feed the selected command (not just all candidates) into the native
    # radio receiver. A conservative refusal does not synthesize progress.
    triples=[
        (s6,0,0,'remote','none',3,18,0),
        (s18,0,0,'none','none',3,18,0),
        (s6,1,1,'none','none',3,18,1),
        (s6,1,0,'remote','none',3,18,0),
        (s18,1,0,'remote','none',3,30,0)]
    selected=[]
    for target in triples:
        due=DUE|{'delivery':target[-2]}
        row=encode(*target)
        # A single actual hidden row is used only to replay the output.
        # Synthesis sees its local view within the entire declared universe.
        rule=admitted([r for _,r in rows(cases,target[-2])],LOCAL,C,due,NAMES+('retain',))
        possible=rule[view(row,LOCAL,C)]
        a=next(iter(possible),None)
        if a is None or a=='retain':
            req=(-1,0,0,target[1],target[2],target[-1],0)
        else:
            t,src,dst,p=ROUTES[a]
            req=(t,int(src=='P'),int(dst=='Base'),target[1],target[2],target[-1],int(target[3]==p))
        st=subprocess.run([sys.argv[2]],input=' '.join(map(str,req))+'\n',
                          capture_output=True,text=True,check=True)
        native_result=list(map(int,st.stdout.split()))
        assert len(native_result)==8
        assert native_result[0]==native_result[3]==1 and target[0]['independent_paid']
        assert native_result[2]==int(a is not None) # all selected reports paid once
        selected.append([a,list(req),native_result])
    assert [s[0] for s in selected]==['early-local','early-remote','retain',None,'defer']
    correlation=joined_reason(s6,s18)
    print(json.dumps(dict(benchmarks=summary,native=results,
          correlation=correlation,selected_native=selected,
          source_spatial_cases=len(cases),counterfeit_depends_on_splice=True),indent=2))
def joined_reason(s6,s18):
    # A deliberately authored cross-port burden, not an effect derived from
    # either native source. A single shared condition shifts the burden:
    # late physical clearance needs a local setup transfer; immediate
    # clearance coincides with a live radio setup debit instead.
    port=('shared-control-port','Base')
    debit=(Use(port,2,5,24),)
    movable=(Use(port,2,5,24),)
    plant=[
        Fragment(('early',),(),F('bay-occupied'),
                 (event(6,0,drop=F('bay-occupied'),paid=('relocation',)),)),
        Fragment(('late',),(),F('bay-occupied'),
                 (event(12,0,uses=debit),
                  event(18,0,drop=F('bay-occupied'),paid=('relocation',))))]
    assert [x.events[-1].at for x in plant]==[s6['real_y_relocation'],s18['real_y_relocation']]
    rf=[
        Fragment(('early',),(),F('auth:Q'),(event(10,0,uses=debit),)),
        Fragment(('late',),(),F('auth:Q'),())]
    opts={'report':(event(15,1,need=F('auth:Q'),uses=movable,paid=('delivery',)),)}
    dues={'relocation':19,'delivery':18}
    try:
        join(plant,rf[:1],opts)
    except ValueError as failure:
        assert str(failure)=='unaccounted joint-history binding'
    else:
        raise AssertionError('unmatched source binding passed as unreachable')
    lawful=join(plant,rf,opts)
    mixed=join([replace(x,binding=()) for x in plant],
               [replace(x,binding=()) for x in rf],opts)
    yes=admitted(lawful,LOCAL,C,dues,tuple(opts))
    no=admitted(mixed,LOCAL,C,dues,tuple(opts))
    assert yes=={():('report',)} and no=={():()}
    assert sum(check(x,'report',C,dues) for x in mixed)==3
    return {'joint_rows':len(lawful),'product_rows':len(mixed),
            'proper_joint_admits':True,'unqualified_product_admits':False,
            'binding_is_given_not_inferred':True,'unmatched_binding_rejected':True}

if __name__=='__main__':main()
