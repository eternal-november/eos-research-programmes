"""Observe actual resolved entity and count post-write motion, not requests."""
import json
from pathlib import Path
import sys

def main():
    n=false_reuse=deferred=witnesses=0
    one={}
    for row in Path(sys.argv[1]).read_text().splitlines():
        k,alias,rewrite,same,actual,keep,ab,ab_work,ba,ba_work=map(int,row.split())
        for A in range(17):
            both=[order for order,dip,worked in (("AB",ab,ab_work),("BA",ba,ba_work)) if dip<=A and worked]
            exact=bool(both)
            if not exact and keep<=A:deferred+=1
            # Transporting a certificate of distinct scopes to a new same-name
            # scene would allow AB if it was valid for the earlier mapping.
            old_admits=(same==2 and keep<=A)
            if old_admits and not exact:false_reuse+=1
            # Re-resolve through the native source, then use the actual order
            # recurrence instead of pretending the logical names separate.
            t=min(k,16)
            q=max(t-1,0)
            if actual==2:
                ref=q<=A
            else:
                u=min(q+1,16)
                v=max(min(t+1,16)-1,0)
                ref=(q<u<=A or q<v<=A)
            assert ref==exact
            n+=1
            if k==0 and alias==0 and A==0:
                one[str(rewrite)]=dict(old_entity=same,new_entity=actual,open_only=keep,
                                      after_open_then_close=[ab,ab_work],
                                      after_close_then_open=[ba,ba_work],
                                      both=both)
            if k==0 and actual==1 and A==0:
                assert ba==ba_work==0 and ab>0 and not exact
                witnesses+=1
    assert n==1428 and witnesses==2
    assert one["0"]["both"]==["AB","BA"] and not one["1"]["both"]
    print(json.dumps(dict(questions=n,invalid_old_disjoint_reuses=false_reuse,
                          safe_defer=deferred,witness=one),sort_keys=True))
if __name__=="__main__":main()
