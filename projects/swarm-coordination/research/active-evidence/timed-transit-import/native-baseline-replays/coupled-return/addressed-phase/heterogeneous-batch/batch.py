from itertools import product,permutations
from pathlib import Path
from subprocess import run
from collections import Counter
import sys
root=Path(sys.argv[1]).resolve()
p=list(permutations(range(3)))
cases=[]
stat=Counter()
def direct(ch,sz,order,start):
    paid=0
    for i in order:
        if sz[i]<=ch[i] and start+sz[i]<=ch[i]:
            paid |= 1<<i
            start+=sz[i]
    return paid
for site,old,cap,sz in product((3,4),(0,1,2),product(range(2,6),repeat=3),product((1,2),repeat=3)):
    edd=tuple(sorted(range(3),key=lambda i:(cap[i],i)))
    result=direct(cap,sz,edd,old)
    assert (result==7)==any(direct(cap,sz,o,old)==7 for o in p)
    stat['families']+=1
    stat['feasible']+=result==7
    stat['saved_vs_arrival']+=result==7 and direct(cap,sz,(0,1,2),old)!=7
    for o in p:cases.append((site,old,cap,sz,o))
rows=[]
for i,(site,old,cap,sz,o) in enumerate(cases):
    rows.append(' '.join(map(str,(i,site,old,*cap,*sz,*o))))
out=run([root/'batch'],cwd=root,input='\n'.join(rows)+'\n',text=True,check=True,capture_output=True).stdout.splitlines()
assert len(out)==len(cases)
for i,row in enumerate(out):
    idx,flag,a,prev=map(int,row.split())
    site,old,cost,length,order=cases[i]
    assert idx==i and a==1 and prev==old
    assert flag==direct(cost,length,order,old)
print(len(cases),'selected native ordered batches',dict(sorted(stat.items())))
