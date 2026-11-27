"""A dual-output sensor obligation and a moving-window bit on one declared chronology."""
from itertools import product
from fractions import Fraction as F
from subprocess import run
import sys
from pathlib import Path
import json

sys.path.insert(0,str(Path(__file__).resolve().parent/"radio"))
import joined as radio
import motion as m

def main():
    cfg=radio.setups()
    flags=list(product((0,1),(0,1),range(5),range(3)))
    inp=''.join(' '.join(map(str,row))+'\n' for row in flags)
    sense=run(['./sensor'],input=inp,text=True,check=True,capture_output=True).stdout.splitlines()
    assert len(sense)==len(flags)
    observed={}
    for key,row in zip(flags,sense):
        far,w,how,phase=key
        dep,pack,late,old,stock,tap,later=map(int,row.split())
        dis=how==1 # same process timeout is not a named END
        assert bool(dep)==(not dis or phase>0)
        assert bool(pack)==(not dis or phase>1)
        assert bool(late)==(not dis)
        assert old==dep and tap==w and later==1-w
        assert stock==(-1 if far and dep else w)
        observed[key]=(old,stock,tap,later)
    cases=[]
    for key,mode,cap,old_at in product(flags,('stock','scoped-tap','rolling-tap'),(2,3),(-421,-411,-401)):
        far,w,why,phase=key
        depth,stock,tap,later=observed[key]
        assert tap==w
        site='far' if far else 'near'
        q,allowed,*_=cfg[site]
        cutoff=radio.FLOOR(allowed*radio.TICKS)
        earliest=radio.CEIL(q*radio.TICKS)
        sent=earliest if cap==3 else max(earliest,old_at+radio.TICKS+1)
        # The later frame is at a different viewpoint after the modeled
        # dwell, not a revision to the fixed world/capture target.
        is_late=F(sent,radio.TICKS)>=F(55,100)
        frame=stock if mode=='stock' else later if mode=='rolling-tap' and is_late else tap
        sched=[(old_at+radio.OFFSET,'P','OK')]
        if frame>=0:sched.append((sent+radio.OFFSET,'Q','F' if frame else 'L'))
        cases.append((key,site,mode,depth,cap,old_at,sched,sent,cutoff))
    inp=[]
    for _,_,_,_,cap,_,a,_,_ in cases:
        inp.append(f'{cap} {len(a)}')
        inp.extend(f'{t} {o} {v}' for t,o,v in a)
    pipe=run(['./radio/broker'],input='\n'.join(inp)+'\n',text=True,check=True,capture_output=True).stdout.splitlines()
    assert len(pipe)==len(cases)
    count=timely=unsafe_live_count=0
    ext={}
    for (key,site,mode,depth,cap,o,a,sent,cutoff),line in zip(cases,pipe):
        n,*out=line.split()
        assert int(n)==len(a) and out==radio.broker_oracle(cap,a) and out[0]=='P:OK'
        outbit=out[1] if len(out)>1 else '-'
        far,w,how,phase=key
        bit=(f"Q:{'F' if w else 'L'}"==outbit and sent<=cutoff)
        legal_time=(cap==3 or o+radio.TICKS+1<=cutoff)
        wrong=(f"Q:{'L' if w else 'F'}"==outbit and sent<=cutoff)
        assert wrong==(legal_time and mode=='rolling-tap' and F(sent,radio.TICKS)>=F(55,100))
        if wrong:
            # Under the pinned coverage worlds wrong selection loses the
            # corresponding terminal condition, not merely a label match.
            x=m.at(cfg[site][3 if w else 2],2)[0]
            assert (x<m.H-1) if w else (x>4)
        unsafe_live_count+=wrong
        qualified=(mode=='scoped-tap' or
                   (mode=='rolling-tap' and F(sent,radio.TICKS)<F(55,100)) or
                   (mode=='stock' and (not far or not depth)))
        assert bit==(legal_time and qualified)
        works=bool(depth and bit)
        assert works==bool(depth and legal_time and (mode=='scoped-tap' or
              (mode=='rolling-tap' and F(sent,radio.TICKS)<F(55,100)) or
              (mode=='stock' and not far)))
        if bit:
            shape='far' if w else 'late'
            if (site,shape) not in ext:
                ext[site,shape]=m.verify(cfg[site][2 if w else 3],shape)
            timely+=1
        count+=works
    print(json.dumps({'native_frames':len(flags),'joined_cases':len(cases),'old_radio_delivered':len(cases),
      'joint_missions':count,'wrong_timely_latest_bits':unsafe_live_count,'timely_world_cues':timely,'motion_extrema':sum(ext.values()),
      'timely_far_old_image_requires_producer_read':True},sort_keys=True,separators=(',',':')))
if __name__=='__main__':main()
