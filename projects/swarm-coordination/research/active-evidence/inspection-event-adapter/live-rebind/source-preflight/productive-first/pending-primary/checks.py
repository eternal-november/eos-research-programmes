from itertools import product
from hashlib import sha256
import subprocess,json,sys
params=list(product((3,4,6),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(4,6),range(3)))
run=subprocess.run([sys.argv[1]],input=''.join(' '.join(map(str,x))+'\n' for x in params),
                   text=True,stdout=subprocess.PIPE,check=True)
picked={}
all_rows=[]
for p,row in zip(params,run.stdout.splitlines(),strict=True):
 t,prior,buffered,w,a,so,ao,H,rule=p
 # Independent arithmetic/event-order comparison. The native first report
 # has charged P TX and Base RX 2 bytes; application work is separate.
 first=(t<4 or (t==4 and prior))
 cut=(0 if not first else 3 if not w else 1 if buffered else 2 if a else 3)
 tx=2+3*first
 rx=2
 possible=(tx+2<=H+2)
 revoke_source=rule==2 and cut==0 and so and possible
 revoke_app=rule==2 and cut==1 and ao and possible
 allow=(cut!=2 if rule==0 else cut==3 if rule==1
                 else (cut==3 and possible) or revoke_source or revoke_app)
 sent_alt=allow and possible
 # In the late attempt arm, the first plus actual earlier alternate may
 # make the primary wire send inadmissible if only 4 headroom remains.
 wire=bool(w and (first or (not revoke_source and (not sent_alt or H>=5))))
 old=bool(wire and a and not revoke_app)
 expected=(cut,tx,rx,int(revoke_source),int(revoke_app),int(wire),int(old),
           int(sent_alt),int(old+sent_alt==1),1)
 actual=tuple(map(int,row.split()))
 assert actual==expected,(p,actual,expected)
 picked[p]=actual
 all_rows.append((p,actual))

# Completeness/ownership cases at the same contact and old physical setup.
def x(t,prior,b,w,a,so,ao,h,rule):
 return picked[t,prior,b,w,a,so,ao,h,rule]
# Just-unpaid duplicates if the earlier primary is still queued and may pay.
assert x(6,0,1,1,1,1,0,6,0)[6:9]==(1,1,0)
# Waiting past fallback availability misses when that queued path won't pay.
assert x(6,0,1,0,1,1,0,6,1)[6:9]==(0,0,0)
for w in (0,1):
 assert x(6,0,1,w,1,1,0,6,2)[3:9]==(1,0,0,0,1,1)
# Actual source at the same tick, different ordering, changes who could revoke.
assert x(4,0,1,1,0,1,0,6,2)[3]==1
assert x(4,1,1,1,0,1,0,6,2)[3:9]==(0,0,1,0,0,0)
# Source queued control cannot cancel a physically buffered late application.
assert x(3,0,1,1,0,1,0,6,2)[8]==0
assert x(3,0,1,1,0,1,1,6,2)[3:9]==(0,1,1,0,1,1)
# Holding application authority doesn't create actual airtime; do not discard
# the available old branch merely because cancellation can be performed.
assert x(3,0,1,1,1,1,1,4,2)[3:9]==(0,0,1,1,0,1)
assert x(3,0,1,1,0,1,1,4,2)[8]==0
keys=[
 ('unpaid_duplicates',(6,0,1,1,1,1,0,6,0)),
 ('wait_misses',(6,0,1,0,1,1,0,6,1)),
 ('queue_revoked',(6,0,1,1,1,1,0,6,2)),
 ('tie_old_wins',(4,1,1,1,0,1,0,6,2)),
 ('buffer_owner',(3,0,1,1,0,1,1,6,2)),
 ('buffer_charge_persists',(3,0,1,1,0,1,1,4,2))
]
blob=json.dumps(all_rows,separators=(',',':')).encode()
print(json.dumps(dict(rows=len(all_rows),canonical_rows_sha256=sha256(blob).hexdigest(),
  witness={k:picked[p] for k,p in keys}),sort_keys=True,indent=2))
