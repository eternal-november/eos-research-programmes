from collections import Counter
from itertools import product
from hashlib import sha1
from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory
from fractions import Fraction as F
import json

ROOT=Path(__file__).resolve().parent
def output(cmd,rows,cwd=ROOT):
    return run(cmd,input='\n'.join(rows)+'\n',text=True,cwd=cwd,check=True,capture_output=True).stdout.splitlines()

def guard(availability, window, deadline):
    # The next controlled opportunity is generated in the quoted support;
    # the current choice must be made before the environment chooses it.
    base,spent=availability
    a,b=window
    assert a<=b and base<=spent
    if base>a or b>deadline:
        return 'outside'
    return 'lend' if spent<=a else 'reserve'

DELTA=7-F(637,100)-F(400,637)
def safe_camera(t):
    eps=F(t-10000,10**6)
    return eps>=0 and eps+10*F(5,1000)**2<=DELTA

def camera():
    cases=[]; inputs=[];stats=Counter()
    # 10 ms = physical opening relative to fixture origin.
    deadline=10000+((DELTA-10*F(5,1000)**2)*10**6).__floor__()
    for d,a,width in product(range(-49000,20001,1000),range(10000,11801,200),(0,100,250)):
        support=sorted({a,a+width//2,a+width})
        d_used=d+50000 if d<=9000 else d
        decision=guard((d,d_used),(support[0],support[-1]),deadline)
        valid=lambda take,t: (d_used if take else d)<=t and safe_camera(t)
        feasible=[take for take in (False,True) if all(valid(take,t) for t in support)]
        assert decision==('lend' if True in feasible else 'reserve' if False in feasible else 'outside')
        stats[decision]+=1
        for t,kind in product(support,('stock','filtered')):
            hold=kind=='filtered' and decision!='lend'
            inputs.append(f'{d} {t} {int(hold)}')
            cases.append((d,t,hold,kind,decision,valid(not hold,t)))
    lines=output(['python3','camera/run.py','--matrix'],inputs)
    assert len(lines)==len(cases)
    for (d,t,hold,kind,decision,safe),line in zip(cases,lines):
        early,late,old_b,old_c=map(int,line.split())
        assert (old_b,old_c)==(1,1)
        assert early==(not hold and d<=9000)
        actual=bool(late) and safe_camera(t)
        assert actual==safe
        if kind=='filtered' and decision!='outside':
            assert actual
        if kind=='stock' and decision=='reserve' and not actual:
            stats['stock_misses_within_guarded_envelope']+=1
        if kind=='filtered' and decision=='lend' and early:
            stats['optional_captures_preserved']+=1
    stats['native_runs']=len(cases)
    return stats

def expiry(hist, cap, n, now):
    if n>cap:return float('inf')
    live=sorted((t,k) for t,k in hist if now-t<=1024)
    missing=sum(k for _,k in live)+n-cap
    if missing<=0:return now
    for t,k in live:
        missing-=k
        if missing<=0:return t+1025
    raise AssertionError((live,missing))

def radio():
    dirs=ROOT/'radio'
    cases=[];inputs=[];stats=Counter()
    cur=2000
    for cap,k0,k1,k2,t0,a,w in product(range(2,6),(1,2),(1,2),(1,2,3),
                                        (1010,1024,1500,1999),(2001,2040,2500,3024,3025),(0,8,24)):
        if k0+k1>cap:continue             # optional is admissible now
        support=sorted({a,a+w//2,a+w})
        deadline=3035
        old=[(t0,k0)];if_send=old+[(cur,k1)]
        decision=guard((expiry(old,cap,k2,cur),expiry(if_send,cap,k2,cur)),(a,a+w),deadline)
        def feasible(take,t):
            held=if_send if take else old
            return t<=deadline and sum(k for u,k in held if t-u<=1024)+k2<=cap
        choices=[take for take in (False,True) if all(feasible(take,t) for t in support)]
        assert decision==('lend' if True in choices else 'reserve' if False in choices else 'outside')
        stats[decision]+=1
        for t,kind in product(support,('stock','filtered')):
            take=kind=='stock' or decision=='lend'
            msg=[(t0,'P','O'*k0)]+([(cur,'Q','X'*k1)] if take else [])+[(t,'Q','R'*k2)]
            inputs += [f'{cap} {len(msg)}']+[f'{u} {actor} {s}' for u,actor,s in msg]
            cases.append((msg,t,kind,decision,feasible(take,t),
                          sum(k for u,k in (if_send if take else old) if t-u<=1024)+k2<=cap))
    for line in (dirs/'INPUTS.tsv').read_text().splitlines():
        name,_,_,_,h=line.split('\t')
        b=(dirs/name).read_bytes()
        assert sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==h
    with TemporaryDirectory() as tmp:
        dd=Path(tmp)
        for fn in ['extract_radio.py','upstream_replay.cpp','motion_broker.cpp']+[f'src{i}' for i in range(6)]:
            (dd/fn).write_bytes((dirs/fn).read_bytes())
        run(['python3','extract_radio.py'],cwd=dd,check=True)
        # The included stock driver is renamed but not invoked.
        run(['c++','-std=c++17','-Wno-return-type','-O2','motion_broker.cpp','-o','broker'],cwd=dd,check=True)
        lines=output(['./broker'],inputs,dd)
    assert len(lines)==len(cases)
    for (msg,t,kind,decision,safe,radio_ok),line in zip(cases,lines):
        n,*obs=line.split()
        assert int(n)==len(obs)==len(msg)
        assert obs[:-1]==[a+':'+p for _,a,p in msg[:-1]]
        emitted=obs[-1]!='-'
        assert emitted==radio_ok and (emitted and t<=3035)==safe
        if kind=='filtered' and decision!='outside':assert safe
        if kind=='stock' and decision=='reserve' and not safe:stats['stock_misses_within_guarded_envelope']+=1
        if kind=='filtered' and decision=='lend':stats['optional_packets_preserved']+=1
    stats['native_runs']=len(cases)
    return stats

if __name__=='__main__':
    result=json.dumps({'camera':camera(),'radio':radio()},sort_keys=True,indent=2)+'\n'
    expectation=ROOT/'expected.json'
    if expectation.exists(): assert result==expectation.read_text()
    print(result,end='')
