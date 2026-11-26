"""Exact receive-boundary analysis with original simulated callback effects."""
from functools import lru_cache
from itertools import product
import json,subprocess,sys

def expected(C,q,cp,x,y,same,shared,drop):
    sent=x if x<=cp else 0
    rb=q if shared else 0
    seen=bool(sent and not drop and rb+x<=cp)
    if seen:rb+=x
    p=sent if same else 0
    if p+y>C:return int(seen),0,sent,p,rb
    p+=y
    if rb+y>C:return int(seen),0,sent,p,rb
    return int(seen),1,sent,p,rb+y

checks=[]
for C in range(1,9):
    for q,cp,y,same,share in product(range(C+1),range(1,C+1),range(1,C+1),(0,1),(0,1)):
        if same and cp!=C:continue
        for x in range(1,cp+2):
            checks.append((C,q,cp,x,y,same,share,0))
checks.append((5,2,2,1,2,0,0,1))
s=''.join(' '.join(map(str,a))+'\n' for a in checks)
p=subprocess.run([sys.argv[1]],input=s,text=True,stdout=subprocess.PIPE,check=True)
result={}
for args,row in zip(checks,p.stdout.splitlines(),strict=True):
    vals=tuple(map(int,row.split()))
    assert expected(*args)==vals,(args,vals,expected(*args))
    result[args]=vals

# Exhaust a matched adaptive common-sender policy tree. Before the first
# differing observation it has exactly one history to respond to.
def best(C,q,y):
    @lru_cache(None)
    def solve(total):
        for x in range(1,C-total+1):
            T=total+x
            if q+T>C: # shared rejects, distinct accepts
                if T+y<=C and q+total+y<=C:return True
            elif solve(T):
                return True
        return False
    return solve(0)

proof=0
for C in range(1,17):
    for q in range(C+1):
        for y in range(1,C+1):
            exist=q>0 and q+y<=C and y<=q-1
            assert best(C,q,y)==exist,(C,q,y,best(C,q,y),exist)
            proof+=1
same=[result[(5,2,5,4,2,1,i,0)] for i in range(2)]
split_same_limit=[result[(5,2,5,4,2,0,i,0)] for i in range(2)]
other=[result[(5,2,2,1,2,0,i,0)] for i in range(2)]
dropped=result[(5,2,2,1,2,0,0,1)]
assert [r[:2] for r in same]==[(1,0),(0,0)]
assert [r[:2] for r in split_same_limit]==[(1,0),(0,1)]
assert [r[:2] for r in other]==[(1,1),(0,1)]
assert dropped[0]==other[1][0]==0
print(json.dumps(dict(native_cases=len(checks),adaptive_common_sender_cases=proof,
    same_sendreceiver_limit=same,new_sender_same_limit=split_same_limit,
    different_existing_sender_limit=other,dropped_separate_probe=dropped,
    row_columns=['probe_receipt','old_paid','probe_tx_debit','old_tx_debit','old_rx_debit']),
    sort_keys=True,indent=2))
