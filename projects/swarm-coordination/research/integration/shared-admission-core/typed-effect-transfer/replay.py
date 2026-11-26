"""Apply one qualified policy at live program boundaries of two pinned plants."""
from dataclasses import replace
from itertools import product
from pathlib import Path
import json,subprocess,sys
from boundary import Boundary,Receipt,pick,direct

wire,physical,up,flight,named,common=sys.argv[1:]
# A single substitution introduces no outcome oracle. It passes only the
# pinned local cut view to the common selector, then resumes the original
# native implementation under the selected policy.
src=Path(physical).read_text()
needle="    rr=step({6:F})"
assert src.count(needle)==1
src=src.replace(needle,"    if callable(policy):policy=policy(view)\n"+needle)
sys.argv=[sys.argv[0],up,flight,named,common]
plant={'__name__':'physical_adapter'}
exec(compile(src,physical,'exec'),plant)

OLD=frozenset({'old-cmd'})
NEW=frozenset({'new','standby'})
def site(plant,tag):
    return Boundary('transfer', 'set-once-'+plant, tag,tag+'-write-gate',1,2,5 if plant=='latch' else 6,OLD,NEW)

def record(b,kind,**kw):
    return replace(Receipt(kind,b.duty,b.effect,b.site,b.arbiter,b.epoch,1,2,b.last),**kw)

def certs(b,w,read):
    late=record(b,'interlock',sampled=2,arrives=3,writers=OLD|NEW)
    new=record(b,'interlock',writers=NEW)
    early=record(b,'interlock',until=b.last-1,writers=OLD|NEW)
    current=record(b,'interlock',writers=OLD|NEW)
    choices={'present':[current], 'late':[late], 'split':[new],
      'short':[early], 'older':[replace(current,epoch=0)],
      'different-site':[replace(current,site='elsewhere')],
      'different-effect':[replace(current,effect='false-target')],
      'wrong-arbiter':[replace(current,arbiter='wrong-local-cache')],
      'split-claims':[record(b,'interlock',writers=OLD),new],
      'terminal':[record(b,'fence',writers=OLD)], 'no-fence':[],
      'old-read':[record(b,'fence',sampled=2,writers=OLD)]}
    bits=[] if read is None else [record(b,'effect-read',value=read)]
    return tuple(choices[w]+bits)
K=('present','late','split','short','older','different-site','different-effect','wrong-arbiter','split-claims','terminal','no-fence','old-read')

def radio(old,path,notice,window):
    b=site('station','base')
    # Only the present configuration realizes the common application gate.
    native_gate=int(window=='present')
    with subprocess.Popen([wire],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True) as p:
        p.stdin.write(f'{old} {path} {notice} {native_gate} 1 0 1\n')
        p.stdin.flush()
        tag,r,ack=p.stdout.readline().split()
        assert tag=='restart' and ack=='0'
        v=None if r=='-1' else int(r)
        entries=certs(b,window,v)
        mode=pick(b,entries)
        assert direct(b,entries)==mode
        n,k={'hold':(0,0),'avoid-repeat':(0,0),'issue':(2,1),'interlocked':(4,1)}[mode]
        p.stdin.write(f'{n} {k}\n');p.stdin.flush()
        raw=tuple(map(int,p.stdout.readline().split()))
        p.stdin.close()
        assert p.wait(timeout=10)==0
    assert raw[5]==1 and raw[2]<=1
    return [mode,raw[2]==1 and raw[3]<=7,raw[3],raw[10]]

def latch(side,old,path,notice,window):
    b=site('latch',f'refuge-{side}')
    modes=[]
    def act(v):
        entries=certs(b,window,v[3])
        mode=pick(b,entries)
        assert direct(b,entries)==mode
        modes.append(mode)
        return {'hold':'wait','avoid-repeat':'wait','issue':'read',
                'interlocked':'both-guarded'}[mode]
    r=plant['run'](side,old,path,notice,act,1)
    assert len(modes)==1 and r['work']==.5
    assert not any(not old and new for t,old,new in r['phys'])
    return [modes[0],r['ok'],r['clear_at'],r['writer']]

def main():
    pairs={}
    for i,old,fault,notice,k in product(range(2),range(3),range(2),range(2),K):
        # Test actual release or true branch in either plant. A terminal-fence
        # receipt cannot be minted in the pending-old arm. No false certification.
        if old==2 and k in ('terminal','old-read'):continue
        a=radio(old,2 if fault else 0,notice,k)
        b=latch(i,old,fault,notice,k)
        assert a[0]==b[0]
        if k=='present':assert a[1] and b[1]
        if k in ('late','split','short','older','different-site','different-effect','wrong-arbiter','split-claims','no-fence'):
            assert a[0]=='hold' and b[0]=='hold'
        pairs[i,old,fault,notice,k]=[a,b]
    before=pairs[0,0,1,0,'present']
    stale=pairs[0,0,1,0,'older']
    assert all(x[0]=='interlocked' and x[1] for x in before)
    assert all(x[0]=='hold' and not x[1] for x in stale)
    # An epoch can change even though present values and the route stay the
    # same. Old receipts cannot be copied into the new authority envelope.
    b=site('latch','refuge-0')
    r=record(b,'interlock',writers=b.old|b.new)
    nb=replace(b,epoch=2,old=b.old|{'spooled'})
    assert pick(b,[r])=='interlocked'
    assert pick(nb,[r])=='hold'
    assert pick(nb,[replace(r,epoch=2)])=='hold'
    assert pick(nb,[replace(r,epoch=2,writers=r.writers|{'spooled'})])=='interlocked'
    # Evaluate materially conflicting terminal evidence instead of accepting
    # whichever delivery won. Old after new numerical record order is not proof.
    f0=record(b,'fence',writers=OLD)
    v0=record(b,'effect-read',value=0)
    v1=record(b,'effect-read',value=1)
    assert pick(b,[f0,v0,v1])==direct(b,[f0,v0,v1])=='hold'
    print(json.dumps(dict(paired_native_comparisons=len(pairs),guarded=before,
        stale=stale,timely_fenced_read=pairs[0,0,0,1,'terminal'],
        same_read_before_fence=pairs[0,0,0,1,'old-read'],
        old_pending_without_guard=pairs[0,2,1,1,'no-fence'],
        one_kernel=True,independent_native_work_every_case=True),
        indent=2,sort_keys=True))
if __name__=='__main__':main()
