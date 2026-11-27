from fractions import Fraction as F
from collections import defaultdict
import subprocess,sys
from pathlib import Path
from consume import Event,Contract,first

def source(up):
    proc=subprocess.run([sys.executable,'-B',
                      Path(__file__).with_name('gaz.py'),up],
                      capture_output=True,text=True,check=True)
    prefix=[]
    groups=defaultdict(list)
    trace=[]
    for line in proc.stdout.splitlines():
        key,*fields=line.split()
        if key!='end':
            n,t,role,parent,value,yes=line.split()
            prefix.append(Event(int(n),F(int(t)), 'sim:2/horizontal',
                                role,int(parent) or None,value,bool(int(yes))))
            continue
        old,phase,permit,change,phys=map(int,fields)
        expected=(phase==0 or phase==1 and change&1 or phase==2 and change==3)
        effect=next(e for e in prefix if e.role=='setter')
        named=[e.seq for e in prefix if e.role=='mail'][1]
        assert int(effect.value)==phys
        found=first(prefix,Contract('sim:2/horizontal',
                                    ('mail','snapshot','slot','setter'),named,F(2),'0'))
        assert bool(found)==bool(permit and expected),(phase,permit,change,found)
        assert phys==(0 if expected else old)
        if found:groups[old,phase,permit].append((change.bit_count(),change))
        trace.append(dict(cut=phase,permit=permit,old=old,action_bits=change,
                          qualified=found,actual=phys,
                          tape=[(x.seq,str(x.at),x.scope,x.role,x.parent,x.value,x.qualified)
                                for x in prefix]))
        prefix=[]
    for old in (0,1):
        assert [min(groups[old,p,1],default=(None,None))[1] for p in range(4)]==[0,1,3,None]
    return trace
