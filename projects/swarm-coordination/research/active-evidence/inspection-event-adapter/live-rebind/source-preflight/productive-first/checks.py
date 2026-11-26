from itertools import product
import json,subprocess,sys
xs=[]
for mode,H,healthy,a in product(range(2),range(2,8),range(2),(0,1)):
 xs.append((mode,H,healthy,a,1,1))
xs +=[(0,6,h,2,0,local) for h,local in product((0,1),range(3))]
raw=subprocess.run([sys.argv[1]],input=''.join(' '.join(map(str,p))+'\n' for p in xs),
                   stdout=subprocess.PIPE,text=True,check=True)
cache={}
for p,line in zip(xs,raw.stdout.splitlines(),strict=True):
 mode,H,healthy,a,ack,local=p
 d,o,b,f,success,total=map(int,line.split())
 spent=0
 if a==0:
    spent=1 if healthy or mode==0 else 0
    if healthy:
       ppaid=int(H>=spent+3);fpaid=0
       spent+=3*ppaid
    else:
       ppaid=0;fpaid=int(H>=spent+2)
       spent+=2*fpaid
    assert (d,o)==(healthy,healthy)
 else:
    ppaid=int(healthy and H>=3)
    spent=3 if H>=3 and (healthy or mode==0) else 0
    picked=not(ack and ppaid) and (local==1 or (local==2 and not ppaid))
    fattempt=int(picked and H>=spent+2)
    fpaid=int(fattempt and (a==2 or not healthy))
    spent+=2*fattempt
    assert (d,o)==(0,int(ack and ppaid))
 assert (b,f,success,total)==(ppaid,fpaid,int(ppaid+fpaid==1),spent+2)
 cache[p]=(b,f,success,total)
def robust(mode,H,a):
 return all(cache[mode,H,w,a,1,1][2] for w in (0,1))
assert robust(1,3,1) and not robust(1,3,0)
assert robust(0,4,0) and not robust(0,4,1)
for h in (0,1):assert cache[0,6,h,2,0,2][2]
assert not cache[0,6,1,2,0,1][2] and not cache[0,6,0,2,0,0][2]
print(json.dumps(dict(rows=len(xs),thresholds=[
 {'failed_path_mode':m,'diagnostic':min(b for b in range(2,8) if robust(m,b,0)),
  'productive':min(b for b in range(2,8) if robust(m,b,1))} for m in (0,1)],
 cases={str(k):v for k,v in cache.items()}),sort_keys=True,indent=2))
