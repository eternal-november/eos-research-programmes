from pathlib import Path
from collections import defaultdict
import json
import subprocess
import sys
from fractions import Fraction

def main(up):
    path=Path(__file__).resolve().with_name('gaz.py')
    native=subprocess.run([sys.executable,'-B',path,up],capture_output=True,
                           text=True,check=True)
    got=defaultdict(list)
    tape=[]
    for entry in native.stdout.splitlines():
        k,*tail=entry.split()
        if k=='front':
            old,at,z,cmd,xorigin,zorigin=map(int,tail[:6])
            x,w=map(Fraction,tail[6:])
            repair=(at==0 or at==1 and cmd&1 or at in (2,3) and cmd&3==3)
            kept=(at!=3 or not (cmd&2) or z and cmd&4)
            assert xorigin==(2 if repair else 1) and bool(zorigin)==bool(kept),entry
            assert x==(0 if repair else old)
            assert w==(Fraction(5,8) if kept else 0)
            if repair and kept:
                got[old,at,z].append((cmd.bit_count(),cmd))
            tape.append((old,at,z,cmd,xorigin,zorigin,str(x),str(w)))
        else:
            assert k=='separate-effects'
            x0,z0,x1,z1=map(Fraction,tail)
            assert x0==0 and z1==Fraction(5,8)
            assert not (x0==0 and z0==Fraction(5,8) or x1==0 and z1==Fraction(5,8))
    exact={}
    for old in (0,1):
        for z in (0,1):
            frontier=[min(got[old,at,z],default=(None,None))[1] for at in range(5)]
            assert frontier==[0,1,3,7 if z else None,None]
            exact[f'{old}:{z}']=frontier
    return dict(frontier=exact,traces=tape,separate_effects_checked=True)

if __name__=='__main__':
    print(json.dumps(main(Path(sys.argv[1]).resolve()),separators=(',',':'),sort_keys=True))
