"""Exact named deletions with a fixed order and fixed eligibility bits."""
import json
def run():
    changes=promotion=queries=budgets=0
    for n in range(1,5):
        for m in range(1,5):
            Q=(tuple(range(n)),tuple(range(n,n+m)))
            for mask in range(1<<(n+m)):
                eligible=lambda i:bool(mask&(1<<i))
                def find(q): return next((j for j,i in enumerate(q) if not eligible(i)),len(q))
                need=sum(map(find,Q))
                old=any(eligible(q[0]) for q in Q)
                for k in range(4):
                    feas=[]
                    for d in range(1<<(n+m)):
                        spent=d.bit_count()
                        if spent>k:continue
                        remaining=[tuple(i for i in q if not(d>>i)&1) for q in Q]
                        ref=any(q and eligible(q[0]) for q in remaining)
                        # Optimized guard only retains first k+1 candidates from each queue.
                        head=[next((i for i in q[:k+1] if not(d>>i)&1),None) for q in Q]
                        calc=any(i is not None and eligible(i) for i in head)
                        assert ref==calc
                        if not ref:feas.append(spent)
                        changes+=int(ref!=old);promotion+=int(ref and not old);queries+=1
                    assert bool(feas)==(need<=k) and (not feas or min(feas)==need)
                    budgets+=1
    return dict(queries=queries,changed=changes,promoted_block=promotion,minimum_checks=budgets)
if __name__=='__main__':print(json.dumps(run(),sort_keys=True,separators=(',',':')))
