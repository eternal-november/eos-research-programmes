"""Snapshot prefix capture, native source control; no field inference."""
from pathlib import Path
from types import SimpleNamespace as NS
from fractions import Fraction as F
import sys
import numpy as np
import prior

def native(path,fail,interleave,step=F(1,100)):
    state1={'sign':[],'acquired':[],'warnings':[],'published':[]}
    epoch=0
    ns=dict(np=np,rospy=NS(logwarn=state1['warnings'].append),
            Float64MultiArray=lambda data:NS(data=tuple(float(x) for x in data)))
    r=prior.selected(path,ns)()
    std=ns['sign']
    def sign(x):
        ans=std(x)
        state1['sign'].append((int(ans),epoch))
        return ans
    ns['sign']=sign
    r.currents=np.array([1.,1.,1.,1.])
    r.throttles=[20.]*4
    r.filt=.3
    r.curr_pub=NS(publish=lambda msg:state1['published'].append(msg.data))
    class Channel:
        def __init__(self,index):self.i=index
        @property
        def voltage(self):
            nonlocal epoch
            # Native order: sign left operand, voltage right operand.
            if interleave==self.i:
                epoch+=1
                r.throttles[self.i]=-20.
            if fail==self.i:raise OSError('test ADC loss')
            latest=[1.,1.,1.,1.] if fail is None else [2.,1.,1.,1.]
            time=step*self.i
            state1['acquired'].append((self.i,time,F(latest[self.i]),epoch))
            return latest[self.i]
    r.channels=[Channel(i) for i in range(4)]
    r.current_callback(None)
    assert state1['published']==[(1.,1.,1.,1.)]
    if fail is None: assert not state1['warnings'] and len(state1['acquired'])==4
    else:assert len(state1['warnings'])==1 and len(state1['acquired'])==fail
    return state1

def unsigned_pair(state1):
    good={}
    # Policy consumes records with captured sign epoch, not privileged fixture
    # cause or latest throttle. Actual current-to-force law remains external.
    for i,t,x,generation in state1['acquired']:
        sign,source=state1['sign'][i]
        if source==generation:good[i]=(t,x*sign)
    return [good.get(i) for i in (0,1)]

def lower(reads,cut,B,D,e,L):
    # Exact lower endpoint for +I0-I1 under independent bounded coordinate
    # errors/drifts plus one bounded Lipschitz additive bias, scalar model.
    if any(a is None for a in reads):return None
    (t,l),(u,r)=reads
    assert max(t,u)<=cut
    return l-r-2*e-L*(2*cut-t-u)-min(2*B,D*abs(t-u))

def main(path):
    for fail in (None,0,1,2,3):
        for interleave in (None,0,1,2,3):
            x=native(path,fail,interleave)
            pair=unsigned_pair(x)
            if interleave in (0,1):assert pair[interleave] is None
            if fail in (0,1):assert pair[1] is None
            bound=lower(pair,F(1,10),F(1,2),F(4),F(1,20),F(1,5))
            print(fail,interleave,pair,bound)
if __name__=='__main__':main(Path(sys.argv[1]))
