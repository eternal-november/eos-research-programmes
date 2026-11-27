"""Make the unpaid-shadow policy executable without the qualified receipt."""
import json
from itertools import product
from mission import (W,State,KEY,EXIT,inputs,known,signature,transition,synth,
                     replay_policy,load_native)

def shadow_exec(graph,worlds,public_wait_mask,args,menu):
    # Physically run the same prefix in a new plant. Only a virtual return
    # from the no-query law is supplied to the policy; never read true A.
    def run(w:W):
        s=State()
        # Initial menu was computed on the full support. Keep a virtual belief
        # id tuple from that menu; filter its branches with the emulated view.
        ids=tuple(range(len(worlds)))
        pseudo=W(False,False,public_wait_mask)
        actions=[]
        while (s,ids) in menu:
            a,cells=menu[(s,ids)]
            ns=transition(graph,s,("wait",) if a==("read",) else a,w,*args[:4])
            kk=(signature(a,ns,pseudo,"sealed",None),known(ns,w,args[0]))
            cs,ids=cells[kk]
            assert cs==ns
            actions.append(a)
            s=ns
        assert s.pos==EXIT and s.t<=args[-1] and s.inspected and s.deposited
        return actions
    count=0
    for w in worlds:
        actual=run(w)
        matching=run(W(False,w.closed,public_wait_mask))
        assert actual==matching
        count+=1
    return count

def main():
    graph,coords,d=inputs()
    source=load_native(graph,coords,d)
    native_paid=tuple(body==KEY for cap,mode,body in source if cap==1)
    assert native_paid==(False,True)
    counts={"same_exact_service":0,"qualified_policy_runs":0,
            "explicitly_erased_runs":0,"ordinary_state_count":0}
    for mask,site,report,exit_tick in product((0,2,99,"mixed"),(1,8),(15,18,21,24),(18,21,24,27)):
        support=[W(b,z,r) for b,z,r in product(native_paid,(False,True),(0,99) if mask=="mixed" else (mask,))]
        args=(3,site,report,12,exit_tick)
        active,menu,astates=synth(graph,support,"sealed",*args,True)
        passive,pas,pstates=synth(graph,support,"none",*args,True)
        assert active==passive
        counts["ordinary_state_count"]+=astates+pstates
        counts["same_exact_service"]+=1
        if passive:
            real=replay_policy(graph,support,"sealed",*args,True,menu)
            assert len(real)==len(support)
            counts["qualified_policy_runs"]+=len(real)
            counts["explicitly_erased_runs"]+=shadow_exec(graph,support,99 if mask=="mixed" else mask,args,menu)
    # Why the laws are not redundant. Exhaust all deterministic one-cut
    # controls; in both fixtures a qualified one-bit read chooses a winner.
    ss=(False,True)
    acceptable=lambda a,e,b:a==e
    coupled=[(False,False),(True,True)]
    assert not any(all(acceptable(a,*w) for w in coupled) for a in ss)
    assert all(acceptable(b,e,b) for e,b in coupled)
    both=[(False,b) for b in ss]
    no_duplicate=lambda a,e,b:a!=b
    assert not any(all(no_duplicate(a,*w) for w in both) for a in ss)
    assert all(no_duplicate(not b,e,b) for e,b in both)
    print(json.dumps(counts,sort_keys=True))

if __name__=="__main__":main()
