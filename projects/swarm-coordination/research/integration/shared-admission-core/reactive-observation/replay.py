from collections import defaultdict
from itertools import product
from hashlib import sha1
from pathlib import Path
import json, subprocess, sys

root,cp=map(Path,sys.argv[1:3])
warehouse_args=sys.argv[3:]
raw=(cp/'core.py').read_bytes()
assert sha1(f"blob {len(raw)}\0".encode()+raw).hexdigest()=="687bf1250c6725992b6de696d0781d7948b4a89e"
sys.path.insert(0,str(cp))
from core import Event, Fragment, Use, admitted, check, join, view
from selector import planes

F=frozenset
DUE={'prefix':0,'unrelated':3,'clearance':19,'report':18,'carry-on':17}
A=('local','remote')
C=13
TX=lambda s: ('tx',s)
RX=lambda s: ('rx',s)
def u(k,n): return Use(k,n,5,24)
def evt(t,order=0,**kw):return Event(t,order,**kw)

def native(params):
    cmd=''.join(' '.join(map(str,p))+'\n' for p in params)
    proc=subprocess.run([str(root/'radio')],input=cmd,text=True,check=True,capture_output=True)
    return [tuple(map(int,line.split())) for line in proc.stdout.splitlines()]

def encode(key,s,probe,profile,erasure,output):
    txa,rxa,optional,late=profile
    req_erase,rep_erase=erasure
    req,reply,spent1,spent2,known,_,first,unrelated,carry=output
    sw=(evt(s['physical_relocation'],paid=('clearance',),drop=F(('bay-live',))),)
    rf=[evt(0,uses=(u(TX('P'),2),u(RX('Base'),2)),
                paid=('prefix',) if first else ()),
        evt(3,uses=(u(TX('Independent'),1),u(RX('Far'),1)),
                paid=('unrelated',) if unrelated else ()),
        evt(17,uses=(u(TX('Independent'),1),u(RX('Far'),1)),
                paid=('carry-on',) if carry else ())]
    if optional:
        rf.append(evt(9,uses=(u(TX('P'),3),)))
    if spent1:
        tags=[u(TX('ProbeSender'),spent1)]
        if req:tags.append(u(RX('ProbeOwner'),1))
        rf.append(evt(10,uses=tuple(tags)))
    if not late and spent2:
        tags=[u(TX('P' if txa else 'ReceiptSender'),spent2)]
        if reply:tags.append(u(RX('Base' if rxa else 'Control'),2))
        rf.append(evt(12,uses=tuple(tags)))
    # An after-commit reply is not consumed by this mission. Native control
    # includes it separately; there are no checked consumers after tick 15.
    obs=((12,'decision',('clearance',known)),) if known>=0 else ()
    # The fixture's reciprocal grant places responsibility at the remote
    # port only while the local berth is occupied. The local negative
    # fact must still hold at emission; a report is not completion proof.
    opts={
      'local':(evt(15,absent=F(('bay-live',)),
                   uses=(u(TX('P'),2),u(RX('Base'),2)),paid=('report',)),),
      'remote':(evt(15,need=F(('bay-live',)),
                   uses=(u(TX('Q'),2),u(RX('Second'),2)),paid=('report',)),)
    }
    return join([Fragment(key,(),F(('bay-live',)),sw)],
                [Fragment(key,obs,F(),tuple(rf))],opts)[0]

def reference(base_time,probe,profile,erasure):
    txa,rxa,optional,late=profile
    erq,erp=erasure
    req=bool(probe and not erq)
    time=base_time+int(probe==2 and req and base_time>10)
    assert time not in (11,12,13,14,15)
    tx=2+3*optional
    rx=2
    sent=req and not late and (not txa or tx+2<=5)
    recv=sent and not erp
    clear=time<15
    if sent and txa:tx+=2
    if recv and rxa:rx+=2
    choices=[]
    if time<=19:
        if clear and tx+2<=5 and rx+2<=5:choices.append('local')
        if not clear:choices.append('remote')
    return time, int(clear) if recv else -1, tuple(choices)

def main():
    plain=json.loads((root/'plain.json').read_text())
    held=json.loads((root/'held.json').read_text())
    table={(t,(z['side'],z['case'])):z for t,series in ((0,plain),(1,held)) for z in series}
    keys=tuple((s['side'],s['case']) for s in plain)
    for k in keys:
        b,h=table[0,k],table[1,k]
        assert b['physical_relocation']==b['real_y_relocation']
        assert h['host_idle']==1
        assert b['cut12']==(b['physical_relocation']<=12)
        assert h['cut12']==(h['physical_relocation']<=12)
        assert h['physical_relocation']==b['real_y_relocation']+int(b['real_y_relocation']>10)
    cases=[]
    pref=[]
    for k,probe,profile,erasure in product(keys,range(3),tuple(product(range(2),repeat=4)),tuple(product(range(2),repeat=2))):
        b=table[0,k]['physical_relocation']
        txa,rxa,opt,late=profile
        erq,erp=erasure
        params=(probe,erq,erp,late,txa,rxa,int(b<15),int(b>=15),opt,-1)
        cases.append((k,probe,profile,erasure,params))
        pref.append(params)
    run=native(pref)
    assert len(run)==len(cases)
    indexed={}
    routechecks=[]
    call=[]
    for (key,probe,profile,erasure,params),output in zip(cases,run,strict=True):
        req,reply,s1,s2,obs,report,first,other,carry=output
        assert first==other==carry==1 and not report
        assert req==int(probe>0 and not erasure[0])
        assert s1==int(probe>0)
        t,hint,safe=reference(table[0,key]['physical_relocation'],probe,profile,erasure)
        s=table[int(probe==2 and req),key]
        assert s['physical_relocation']==t
        assert obs==hint
        row=encode((key,probe,profile,erasure),s,probe,profile,erasure,output)
        assert tuple(a for a in A if check(row,a,C,DUE))==safe
        indexed[key,probe,profile,erasure]=(row,hint,safe)
        for i,a in enumerate(A):
            call.append((*params[:-1],i))
            routechecks.append((a in safe,t<=19,hint,req,s1))
    routes=native(call)
    assert len(routes)==len(routechecks)
    for out,(safe,clearance,hint,req,s1) in zip(routes,routechecks,strict=True):
        assert out[0]==req and out[2]==s1 and out[4]==hint
        assert (bool(out[5]) and clearance)==safe, (out,safe,clearance,hint)
        assert out[6:]==(1,1,1)

    # At stage one none of the hidden warehouse cases or realized erasures
    # are revealed. A known contract gives a set of possible erasure modes.
    # The action is useful iff every resulting local receipt class has some
    # second action with which all its whole histories meet their obligations.
    assert planes({0:[]},'decision',C,DUE,A)=={}
    counts=defaultdict(int)
    witnesses={}
    erasures=(((0,0),),((0,0),(0,1)),((0,0),(1,0)),((0,0),(1,1)))
    # Separate different old tails without revealing which of early/late is active.
    populations={
        'slack-one':['post-conflict','pre-conflict'],
        'tight':['post-conflict','late-proof'],
        'already-clear':['post-conflict','post-disjoint'],
        'remote-only':['pre-conflict','late-proof'],
        'all':[s['case'] for s in plain]}
    for (fam,modes),profile,loss,probe in product(populations.items(),tuple(product(range(2),repeat=4)),erasures,range(3)):
        rs=[indexed[k,probe,profile,e] for k in keys if k[1] in modes for e in loss]
        robust=probe in planes({probe:[x[0] for x in rs]},'decision',C,DUE,A)
        # Full local-table enumeration independent of the admission engine.
        hs=sorted({x[1] for x in rs})
        fixed=any(all(action in x[2] for x in rs) for action in A)
        policies=sum(all(pol[hs.index(x[1])] in x[2] for x in rs)
                     for pol in product(A,repeat=len(hs)))
        assert robust==bool(policies)
        counts['world_family_options']+=1
        counts['robust_two_cut_options']+=int(robust)
        counts['strictly_acquiring']+=int(robust and not fixed)
        if not any(profile) and len(loss)==1:
            witnesses[f'{fam}/{probe}']={'robust':robust,'fixed':fixed,'policy_count':policies}
    # Two erasure supports with identical possible outcomes for each local
    # test taken on its own, but different joint status; observable silence
    # can select a route only with a physically justified joint exclusion.
    profile=(0,0,0,0)
    def losses(per_clear):
        return [indexed[k,1,profile,e] for k in keys
                if k[1] in ('post-conflict','late-proof')
                for e in per_clear[table[0,k]['physical_relocation']<15]]
    narrow=losses({True:((0,0),),False:((0,0),(0,1))})
    permissive=losses({True:((0,0),(0,1)),False:((0,0),(0,1))})
    def build(rs):
        return admitted([x[0] for x in rs],'decision',C,DUE,A)
    tight=build(narrow)
    loose=build(permissive)
    assert tight[()]==('remote',) and loose[()]==()
    assert all(tight.values()) and not all(loose.values())
    # Send the selected policy output for each hidden source trace. This
    # native execution starts from the same prefix profile; only receipt
    # view and chosen probe are available to the policy, never key.
    selected=[]
    for k,erasure in product(keys,((0,0),(0,1))):
        is_clear=table[0,k]['physical_relocation']<15
        if k[1] not in ('post-conflict','late-proof') or (is_clear and erasure[1]):
            continue
        row,hint,safe=indexed[k,1,profile,erasure]
        possible=tight[view(row,'decision',C)]
        assert len(possible)==1
        answer=A.index(possible[0])
        selected.append(((1,*erasure,0,0,0,int(is_clear),int(not is_clear),0,answer),
                         hint,possible[0]))
    reproduced=native([x[0] for x in selected])
    assert len(reproduced)==len(selected)
    for out,(_,hint,name) in zip(reproduced,selected):
        assert out[4]==hint and out[5:]==(1,1,1,1)
        assert name==('local' if hint==1 else 'remote')
    exchanges=[]
    for k,probe,erp,support in (
            ((0,'post-conflict'),1,0,tight), ((0,'late-proof'),1,1,tight),
            ((0,'late-proof'),2,0,build([indexed[(side,case),2,profile,(0,0)]
                                       for side in range(2)
                                       for case in ('post-conflict','late-proof')]))):
        # Drive the real endpoint process through both decision barriers,
        # keeping a single live radio ledger. After the request callback,
        # run the selected native spatial source, then use its sampled
        # snapshot, not its future completion tick, for the payload.
        with subprocess.Popen([str(root/'radio')],stdin=subprocess.PIPE,
                             stdout=subprocess.PIPE,text=True) as proc:
            proc.stdin.write(f'{probe} 0 {erp} 0 0 0 -1 0 0 -1\n')
            proc.stdin.flush()
            tag,request,charge=proc.stdout.readline().split()
            assert tag=='query' and request==charge=='1'
            hosted=int(probe==2 and request=='1')
            replayed=json.loads(subprocess.run([sys.executable,'-B',
                str(Path(__file__).parent/'spatial.py'),*warehouse_args,str(hosted)],
                text=True,capture_output=True,check=True).stdout)
            spatial=next(s for s in replayed if (s['side'],s['case'])==k)
            assert spatial==table[hosted,k]
            read=bool(spatial['cut12'])
            proc.stdin.write(f'{int(read)} {int(not read)}\n')
            proc.stdin.flush()
            tag,raw=proc.stdout.readline().split()
            assert tag=='view'
            obs=int(raw)
            seen=() if obs<0 else ((12,('clearance',obs)),)
            # Refuse the unguaranteed whole prefix in the negative control.
            chosen=support[seen] if all(support.values()) else ()
            api=A.index(chosen[0]) if chosen else -1
            proc.stdin.write(f'{api}\n')
            proc.stdin.flush()
            actual=tuple(map(int,proc.stdout.readline().split()))
            proc.stdin.close()
            assert proc.wait(timeout=10)==0
        assert actual[4]==obs and actual[5]==int(bool(chosen)) and actual[6:]==(1,1,1)
        exchanges.append([k,hosted,read,obs,list(chosen),spatial['physical_relocation'],actual[5]])
    assert [x[4] for x in exchanges]==[['local'],['remote'],[]]
    assert witnesses['tight/0']=={'robust':False,'fixed':False,'policy_count':0}
    assert witnesses['tight/1']=={'robust':True,'fixed':False,'policy_count':1}
    assert witnesses['tight/2']=={'robust':False,'fixed':False,'policy_count':0}
    assert witnesses['slack-one/2']=={'robust':True,'fixed':False,'policy_count':1}
    print(json.dumps(dict(raw_profiles=len(cases),native_completions=len(routes),staged_native_exchanges=exchanges,
                          warehouse_controls=len(plain)+len(held),families=dict(counts),
                          correlated_erasure=dict(silence_route=tight[()],unrestricted_silence_route=loose[()],
                                                  selected_native=len(selected)),
                          no_erasures_zero_aliases_witnesses=witnesses),indent=2,sort_keys=True))
if __name__=='__main__':main()
