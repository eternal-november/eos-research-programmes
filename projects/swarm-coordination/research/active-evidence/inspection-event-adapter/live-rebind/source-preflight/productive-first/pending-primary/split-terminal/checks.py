from itertools import product
from hashlib import sha256
import json,subprocess,sys
params=[q for q in product((4,7,9,10),(1,2,5),(0,1),*( (0,1) for _ in range(4)),
                          (3,5),(0,1),(0,1),(0,1))
        if not(q[-2] and q[4])]
r=subprocess.run([sys.argv[1]],input=''.join(' '.join(map(str,q))+'\n' for q in params),
                 text=True,stdout=subprocess.PIPE,check=True)
all_rows=[];v={}
for x,line in zip(params,r.stdout.splitlines(),strict=True):
 t,d,tie,req_drop,ret_drop,st,rx,H,good,cert,policy=x
 reached=not req_drop
 before= t<9 or (t==9 and not tie)
 fit_requested=H>=2+2*max(st,rx)
 qualified=cert and t+d<=11 and fit_requested
 revoked=reached and before and (policy==0 or qualified)
 p=good and not revoked
 receipt=revoked and not ret_drop
 by_cut=(t+d<=11)
 charged_tx=2+ (3 if not revoked else 2*int(st and by_cut))
 charged_rx=2+ (2 if receipt and by_cut and rx else 0)
 f=receipt and by_cut and fit_requested
 expected=tuple(map(int,(reached,revoked,receipt,p,f,p or f,charged_tx,charged_rx,1)))
 actual=tuple(map(int,line.split()))
 assert actual==expected,(x,actual,expected)
 all_rows.append((x,actual));v[x]=actual

keys={
 'lost_reply_strands_healthy':(7,2,0,0,1,0,0,3,1,0,0),
 'known_loss_retains_healthy_primary':(7,2,0,0,1,0,0,3,1,0,1),
 'true_return_scope_allows_early_cancel':(7,2,0,0,0,0,0,3,0,1,1),
 'return_delivers_after_slot':(7,5,0,0,0,0,0,3,1,0,0),
 'charged_receipt_uses_tail_budget':(7,2,0,0,0,1,0,3,1,0,0),
 'source_tick_preemption':(9,0+2,1,0,0,0,0,3,0,1,1),
}
assert v[keys['lost_reply_strands_healthy']][1:6]==(1,0,0,0,0)
assert v[keys['known_loss_retains_healthy_primary']][1:6]==(0,0,1,0,1)
assert v[keys['true_return_scope_allows_early_cancel']][1:6]==(1,1,0,1,1)
assert v[keys['return_delivers_after_slot']][1:6]==(1,1,0,0,0)
assert v[keys['charged_receipt_uses_tail_budget']][1:6]==(1,1,0,0,0)
assert v[keys['source_tick_preemption']][1:6]==(0,0,0,0,0)
# Within this cut and one-reply catalogue, the original owner observes a
# successful request in both worlds, not the future primary and return.
wrong=[]
for cancel in (False,True):
    lost_on_revoke=v[7,2,0,0,1,0,0,3,1,0,0]
    lost_on_retain=v[7,2,0,0,0,0,0,3,0,0,1]
    wrong.append(lost_on_revoke[5] if cancel else lost_on_retain[5])
assert wrong==[0,0]
blob=json.dumps(all_rows,separators=(',',':')).encode()
print(json.dumps(dict(rows=len(all_rows),canonical_rows_hash=sha256(blob).hexdigest(),
                      witnesses={label:v[x] for label,x in keys.items()}),
                 indent=2,sort_keys=True))
