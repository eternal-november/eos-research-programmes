"""Checked finite impact discovery, then feed #604 the complete changed fibers."""
import importlib.util
from itertools import product
import json,sys
from scope import Patch,Scope
wire,ack,core,spatial,fiber,*tail=sys.argv[1:]
sys.path.insert(0,fiber)
from delta import Certificate,WholeFiber,Edit

sys.argv=[sys.argv[0],wire,core,spatial,*tail]
spec=importlib.util.spec_from_file_location('ack',ack+'/replay.py')
a=importlib.util.module_from_spec(spec)
spec.loader.exec_module(a)
from core import view
N=('pack','split','spare','early-join')
getview=lambda x:view(x,'lead',a.CUT)
check=lambda x,n:a.check(x,n,a.CUT,a.DUE)
VIEW=()

def full(radio,duty,links):
    return {name:frozenset((r,d) for kr,kd in choices
            for r in radio[kr] for d in duty[kd]) for name,choices in links.items()}

def updated(old, patch):
    return {k:v for k,v in (old|patch).items() if v is not None}

def patches(cert,p,out,make):
    return {n:Edit(cert.coverage[n][0] if n in cert.coverage else -1,
             WholeFiber(p.after,tuple(make(r,d) for r,d in sorted(w)),not w))
            for n,w in out.items()}

def fresh(s,make):
    rows=[make(r,d) for f in s.values() for r,d in sorted(f)]
    obs=[r for r in rows if getview(r)==VIEW]
    return tuple(z for z in N if all(check(r,z) for r in obs)) if obs else None

def cert(s,make):
    return Certificate({n:WholeFiber(0,tuple(make(r,d) for r,d in sorted(f))) for n,f in s.items()},
           getview,check,N,a.CUT)

def mk_native():
    pp=tuple(product(range(3),*(range(2) for _ in range(10))))
    got=a.data(pp)
    assert all(got[p]==a.reference(p) for p in pp)
    ends=tuple(a.replay_old(h) for h in range(2))
    tight=next(k for k,t in ends[0].items() if t==19)
    loose=next(k for k,t in ends[0].items() if t==18)
    def build(rb,db):
        aliases, erasure, stale=rb
        k,need=(tight,db[1]) if db[0] else (loose,db[1])
        def p(n):
            m=2 if n=='early-join' else int(n!='pack')
            early=0 if n=='spare' else aliases
            return m,early,early,aliases,aliases,erasure,0,need,stale,1,1
        w=tuple(t[k] for t in ends)
        return a.build(w[0],w,p,got,N[:3])
    from functools import lru_cache
    return lru_cache(None)(build),len(pp),sum(map(len,ends))

def main():
    make,raw,old=mk_native()
    sr=(0,0,0); jr=(1,0,0); er=(1,1,0); st=(0,0,1)
    relaxed=(0,0); load=(1,1); not_consumed=(1,0)
    one=lambda x:frozenset([x])
    ij=tuple(product(range(2),repeat=2))
    named=tuple(frozenset(p for i,p in enumerate(ij) if mask & (1<<i)) for mask in range(1,16))
    trials=0
    # All nonempty route/cause link relations on two source keys each,
    # independently four binary source switches at the same edition.
    for l0,l1,bits in product(named,named,product((0,1),repeat=4)):
        radio={0:one(sr),1:one(jr)}
        duty={0:one(relaxed),1:one(not_consumed)}
        links={0:l0,1:one((0,0))}
        r={k:one(er if k else st) for k in radio if bits[k]}
        d={k:one(load) for k in duty if bits[2+k]}
        l={0:l1} if l1!=l0 else {}
        p=Patch(0,1,r,d,l)
        ix=Scope(radio,duty,links)
        oldf=full(radio,duty,links)
        newf=full(updated(radio,r),updated(duty,d),updated(links,l))
        touched,out=ix.compile(p)
        exact={k:newf[k] for k in oldf if oldf[k]!=newf[k]}
        assert out==exact and set(out)<=touched
        c=cert(oldf,make)
        assert c.revise(patches(c,p,out,make),at=9,qualified=True)
        assert c.admitted(VIEW)==fresh(newf,make)
        ix.install(p)
        assert ix.compile(Patch(1,2,{}, {}, {}))==(frozenset(),{})
        trials+=1

    # A new physical combination enters support without removing any old
    # witness. There is no current recipient notice of which branch occurred.
    r={0:one(sr)};d={0:one(relaxed)}
    l={0:one((0,0)),1:one((0,0))}
    ix=Scope(r,d,l)
    c=cert(full(r,d,l),make)
    start=c.admitted(VIEW)
    assert start==('pack','split','spare')
    new=Patch(0,1,{1:one(jr)},{1:one(load)},{0:one((0,0))|one((1,1))})
    cand,out=ix.compile(new)
    assert cand=={0} and out[0]=={(sr,relaxed),(jr,load)}
    assert c.revise(patches(c,new,out,make),at=9,qualified=True)
    after=c.admitted(VIEW)
    assert after==('spare',)
    c0=cert(full(r,d,l),make)
    cp=patches(c0,new,out,make)
    assert not c0.revise(cp,at=10,qualified=True) and ix.epoch==0
    ix.install(new)
    try:
        ix.compile(Patch(1,2,{1:None},{},{}))
        raise AssertionError('unresolved active link')
    except ValueError as e:
        assert 'lacks' in str(e)
    retire=Patch(1,2,{1:None},{1:None},{0:None})
    _,out=ix.compile(retire)
    assert out=={0:frozenset()} and c.revise(patches(c,retire,out,make),at=9,qualified=True)
    ix.install(retire)
    assert c.admitted(VIEW)==start

    # A semantic no-op at revision 1 changes which future edits can matter.
    # The incoming link must be installed even if no certificate call is needed.
    r={0:one(sr),1:one(sr)};d={0:one(not_consumed)}
    l={0:one((0,0))}
    ix=Scope(r,d,l);c=cert(full(r,d,l),make)
    first=Patch(0,1,{},{},{0:one((1,0))})
    assert ix.compile(first)==(one(0),{})
    ix.install(first)
    second=Patch(1,2,{1:one(jr)}, {},{})
    assert ix.compile(Patch(1,2,{0:one(jr)}, {},{}))==(frozenset(),{})
    before=c.admitted(VIEW)
    cand,out=ix.compile(second)
    assert cand=={0} and c.revise(patches(c,second,out,make),at=9,qualified=True)
    relinked=c.admitted(VIEW)
    assert relinked==('pack','spare') and before==start

    # Different edge keys with equal values remain separate in the compiler.
    mult=Scope({0:one(sr),1:one(sr)},{0:one(relaxed)},{0:one((0,0))|one((1,0))})
    clear=Patch(0,1,{0:None},{},{0:one((1,0))})
    assert mult.compile(clear)==(one(0),{})
    mult.install(clear)
    assert mult.compile(Patch(1,2,{1:one(jr)|one(sr)}, {},{}))[1][0]=={(sr,relaxed),(jr,relaxed)}

    # One leaf has a single incident live joint history; all other named histories
    # still exist. Counts are observed, not claims about end-to-end runtime.
    r={0:one(sr),1:one(sr)};d={0:one(not_consumed)}
    l={i:one((int(i==0),0)) for i in range(2048)}
    ix=Scope(r,d,l)
    p=Patch(0,1,{1:one(jr)},{},{})
    touched,out=ix.compile(p)
    prev=full(r,d,l);new=full(updated(r,p.radio),d,l)
    assert len(touched)==len(out)==1 and len(new)==2048
    c=cert(prev,make);c.work.clear()
    assert c.revise(patches(c,p,out,make),at=9,qualified=True)
    assert c.admitted(VIEW)==fresh(new,make) and c.work['checks']==4
    result=dict(raw_radio=raw,raw_warehouse=old,exhaustive_patches=trials,
        old_only_false_permits=list(start),after_new_pair=list(after),
        stable_verdict_relink_future=list(relinked),dangling_refused=True,
        repeated_source_value_then_expanded=True,late_refused=True,
        sparse=dict(fibers_full_join=len(new),candidates_indexed=len(touched),
                    changed_fibers=len(out),downstream_checks=c.work['checks']))
    print(json.dumps(result,indent=2,sort_keys=True))
if __name__=='__main__': main()
