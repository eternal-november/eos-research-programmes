"""Compose selected pinned #603 plant rows, then exercise the revision kernel."""
import importlib.util,itertools,json,sys
wire,root,core,spatial,*tails = sys.argv[1:]
oldsys=sys.argv
sys.argv=[sys.argv[0],wire,core,spatial,*tails]
spec=importlib.util.spec_from_file_location("prior_fixture",root+"/replay.py")
p=importlib.util.module_from_spec(spec)
spec.loader.exec_module(p)
from dataclasses import replace
from delta import Certificate,WholeFiber,Edit,direct,project
N=('pack','split','spare','early-join')
from core import view
getview=lambda r:view(r,'lead',p.CUT)
ch=lambda r,n:p.check(r,n,p.CUT,p.DUE)
main=lambda s:Certificate(s,getview,ch,N,p.CUT)
f=lambda i,*rows:WholeFiber(i,tuple(rows))
ret=lambda i:WholeFiber(i,(),True)
def verdict(cache,outcomes):
    for v in outcomes:
        yield cache.admitted(v)
views=((),((9,('qualified-local',1)),))
def run():
    params=tuple(itertools.product(range(3),*(range(2) for _ in range(10))))
    got=p.data(params)
    assert all(got[x]==p.reference(x) for x in params)
    ends=tuple(p.replay_old(h) for h in range(2))
    tight=next(k for k,t in ends[0].items() if t==19)
    loose=next(k for k,t in ends[0].items() if t==18)
    def plant(k,place,need,erase=0,stale=0,notice=0,early=0):
        aS,aR,dS,dR=place
        def args(n):
            return (2 if n=='early-join' else int(n!='pack'),aS if n!='spare' else 0,
                    aR if n!='spare' else 0,dS,dR,erase,0,need,stale,1,1)
        w=tuple(t[k] for t in ends)
        row=p.build(w[0],w,args,got,N if early else N[:3])
        return replace(row,receipts=((notice,'lead',('qualified-local',1)),)) if notice else row
    shared=(1,1,1,1); separate=(0,0,0,0)
    packing=plant(tight,shared,0)
    split=plant(tight,separate,1)
    no_both=plant(tight,shared,1)
    spare=plant(loose,shared,1)
    packed_early=plant(tight,shared,1,early=1)
    loss=plant(tight,shared,0,erase=1)
    stale=plant(tight,separate,1,stale=1)
    timely=plant(tight,separate,1,notice=9)
    late=plant(tight,separate,1,notice=10)
    choices=[packing,split,no_both,spare,packed_early,loss,stale,timely,late]
    trials=0
    for x,y,z,u in itertools.product(choices,repeat=4):
        s={0:f(0,x),1:f(0,y,z)}
        c=main(s)
        b=direct(s,getview,ch,N)
        assert list(verdict(c,views))==[project(b,v,N) for v in views]
        c.work.clear()
        patch={0:Edit(0,f(1,u)),1:Edit(0,ret(1))}
        assert c.revise(patch,at=9,qualified=True)
        s1={k:e.replacement for k,e in patch.items()}
        fresh=direct(s1,getview,ch,N)
        # Genuine cached direct, same information and exact arithmetic.
        b.update(direct(s1,getview,ch,N))
        assert list(verdict(c,views))==[project(fresh,v,N) for v in views]
        assert list(verdict(c,views))==[project(b,v,N) for v in views]
        assert c.work['checks']==len(N)
        trials+=1

    h=main({0:f(0,packing),1:f(0,split)})
    g=main({0:f(0,split),1:f(0,packing)})
    assert h.admitted(())==g.admitted(())==('spare',)
    retire={1:Edit(0,ret(1))}
    assert h.revise(retire,at=9,qualified=True)
    assert g.revise(retire,at=9,qualified=True)
    assert h.admitted(())==('pack','spare') and g.admitted(())==('split','spare')
    assert h.issue((),'pack',at=9)
    assert not h.revise({0:Edit(0,f(1,no_both))},at=9,qualified=True)
    s=main({0:f(0,packing)})
    assert not s.revise({0:Edit(0,ret(1))},at=10,qualified=True)
    assert not s.revise({0:Edit(0,ret(1))},at=9,qualified=False)
    assert not s.revise({0:Edit(0,ret(1)),1:Edit(3,f(4,split))},at=9,qualified=True)
    assert s.admitted(())==('pack','spare')
    assert not s.revise({0:Edit(0,f(1))},at=9,qualified=True)
    assert s.revise({1:Edit(-1,f(0,no_both))},at=9,qualified=True)
    assert s.admitted(())==('spare',)
    assert not s.revise({1:Edit(-1,f(0,split))},at=9,qualified=True)
    assert s.revise({0:Edit(0,ret(1)),1:Edit(0,ret(1))},at=9,qualified=True)
    assert s.admitted(()) is None and not s.issue((),'pack',at=9)
    # Two changed fibers must be installed as one edit: serial add/drop
    # would expose a false pack window while support switches names.
    a={0:f(0,split),1:f(0,packing)}
    d={0:Edit(0,f(1,packing)),1:Edit(0,f(1,split))}
    batch=main(a)
    serial=main(a)
    assert batch.admitted(())==('spare',)
    assert batch.revise(d,at=9,qualified=True) and batch.admitted(())==('spare',)
    assert serial.revise({0:d[0]},at=9,qualified=True) and serial.admitted(())==('pack','spare')
    # Disjoint qualified patches commute before issue, not across an issue.
    forward=main(a)
    backward=main(a)
    for i in (0,1):
        assert forward.revise({i:d[i]},at=8+i,qualified=True)
    for i in (1,0):
        assert backward.revise({i:d[i]},at=9-i,qualified=True)
    assert list(verdict(forward,views))==list(verdict(backward,views))
    big={i:f(0,choices[i%len(choices)]) for i in range(512)}
    s=main(big)
    s.work.clear()
    assert s.revise({0:Edit(0,f(1,split)),1:Edit(0,ret(1))},at=8,qualified=True)
    assert s.work['checks']==len(N)
    direct_count=0
    def measured(r,n):
        nonlocal direct_count
        direct_count+=1
        return ch(r,n)
    changed={0:f(1,split),1:ret(1)}
    full=direct(big|changed,getview,measured,N)
    total_count=direct_count
    reference=direct(big,getview,ch,N)
    direct_count=0
    reference.update(direct(changed,getview,measured,N))
    assert list(verdict(s,views))==[project(full,v,N) for v in views]
    assert list(verdict(s,views))==[project(reference,v,N) for v in views]
    print(json.dumps(dict(native=len(params),native_plant_traces=sum(map(len,ends)), comparisons=trials,
        same_aggregate_retraction=[list(h.admitted(())),list(g.admitted(()))],
        affected_fixture=dict(total_original_fibers=512,full_replay_checks=total_count,
          replacement_checks=s.work['checks'],exact_cached_direct_replacement_checks=direct_count),
        empty_failed_closed=True,post_issue_immutable=True,atomic_rebind_required=True),indent=2,sort_keys=True))
if __name__=='__main__': run()
