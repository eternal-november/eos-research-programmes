"""Direct receipt and actual timed debit controls at matched scope."""
from itertools import product
from hashlib import sha256
import json
import subprocess
import sys

def run(binary):
    inputs=[(k,s,r,d) for k,s,r,d in product(range(4),(0,1),(0,1),(0,1))
            if not(k>=2 and d)]
    raw=subprocess.run([binary],input=''.join(' '.join(map(str,x))+'\n' for x in inputs),
                        text=True,stdout=subprocess.PIPE,check=True)
    results=[]
    for p,line in zip(inputs,raw.stdout.splitlines(),strict=True):
        k,s,r,d=p
        first,refresh,edit,a,b,x,ind,tx,rx,cost,forecast=map(int,line.split())
        assert a==b==ind==1
        # Separate direct event reference for each controlled intervention:
        # before h old-prefix load is 2; after actual optional, its TX is 3
        # and RX is either 3 or 0, depending on actual erased path.
        if k==0:
            assert not first and edit
            assert bool(refresh)==bool(d or not(s or r))
            assert x==refresh
        if k==1:
            assert first and not refresh and x
            assert bool(edit)==bool(d or not(s or r))
        if k==2:
            assert first and x and (tx,rx)==(5,5)
            assert bool(edit)==not_any(s,r)
        if k==3:
            assert first and not x and (tx,rx)==(5,2)
            assert bool(edit)==(not s)
        results.append(dict(case=p,first_acquire=first,refreshed=refresh,edit=edit,
                           first_old=a,second_old=b,optional=x,independent=ind,
                           observed_tx=tx,observed_rx=rx,source_debit_reads=cost,
                           planned_attempt_checks=forecast))
    print(json.dumps(results,sort_keys=True,indent=2))

def not_any(a,b):return not (a or b)
if __name__=='__main__':run(sys.argv[1])
