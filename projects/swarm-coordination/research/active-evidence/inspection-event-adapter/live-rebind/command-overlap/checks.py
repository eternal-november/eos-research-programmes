from itertools import product
import subprocess,json,sys
tests=list(product((0,1),(0,1),range(1,5),(0,1)))
r=subprocess.run([sys.argv[1]],input=''.join(' '.join(map(str,x))+'\n' for x in tests),
                 text=True,stdout=subprocess.PIPE,check=True)
rows=[]
for p,raw in zip(tests,r.stdout.splitlines(),strict=True):
 s,t,b,drop=p
 command,tx,rx,old,optional,sw=map(int,raw.split())
 attempt=2*s+b<=5
 delivered=attempt and not drop and 2*t+b<=5
 left_tx=2+(b if s and attempt else 0)
 left_rx=2+(b if t and delivered else 0)
 rebind=delivered and max(left_tx,left_rx)+2<=5
 new=not rebind and max(left_tx,left_rx)+3<=5
 assert (command,tx,rx,old,optional,sw)==(delivered,left_tx,left_rx,rebind,new,rebind)
 rows.append((p,command,tx,rx,old,optional,sw))
assert next(x for x in rows if x[0]==(1,0,1,0))[4]==1
assert next(x for x in rows if x[0]==(1,0,2,0))[4]==0
assert next(x for x in rows if x[0]==(0,1,2,0))[4]==0
print(json.dumps(rows,separators=(',',':'),sort_keys=True))
