import ast,hashlib,sys,json,itertools
from pathlib import Path
from types import SimpleNamespace as NS
from fractions import Fraction as F
from random import Random
import numpy as np

PIN='1790e81a331d756c352a0d28ecdf30529070a847'
def selected(path,g):
    b=path.read_bytes()
    assert hashlib.sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==PIN
    tree=ast.parse(b)
    cls=next(x for x in tree.body if isinstance(x,ast.ClassDef))
    methods={'current_callback','cmd_wrench_callback','stop_bot','run'}
    body=[x for x in cls.body if isinstance(x,ast.FunctionDef) and x.name in methods]
    cls.body=body
    sign=next(x for x in tree.body if isinstance(x,ast.Assign) and x.targets[0].id=='sign')
    exec(compile(ast.Module(body=[sign,cls],type_ignores=[]),str(path),'exec'),g)
    return g['Ouijabot']

class PWM:
    def __init__(self):self.duty=None
    def ChangeDutyCycle(self,v):self.duty=v
class Channel:
    def __init__(self,v,fail=False):self.v=v;self.fail=fail
    @property
    def voltage(self):
        if self.fail: raise OSError('authored ADC failure')
        return self.v

def rounded(x):
    return [round(float(v),9) for v in x]
def native(path,broken=False,which=0,legacy_scalar_adapter=True):
    warn=[];messages=[];clock=[0.0]
    ro=NS(get_time=lambda:clock[0],logwarn=warn.append)
    g=dict(np=np,rospy=ro,io=NS(output=lambda *_:None,HIGH=1,LOW=0),
           Float64MultiArray=lambda data:NS(data=data.copy()))
    v=selected(path,g)()
    v.throttles=[20.0]*4
    v.currents=np.array([0.2,0.3,0.4,0.5]); emitted=v.currents.copy()
    v.err_prev=np.zeros(4);v.err_int=np.zeros(4);v.maxDelay=.5
    v.kFF=100.;v.kP=75.;v.kI=20.;v.kD=10.;v.iDec=.8;v.filt=.3
    kF=np.sqrt(2)*(.257*5.)/(2*.03); kT=kF*.12
    A=np.array([[kF,-kF,-kF,kF],[-kF,-kF,kF,kF],[kT,kT,kT,kT]])
    v.A_wrench=A.T@np.linalg.inv(A@A.T)
    # ROS and electronics remain mocked here; callback computations exact.
    raw=([0.8,0.7,0.6,0.9] if broken else emitted)
    v.channels=[Channel(x,broken and i==which) for i,x in enumerate(raw)]
    v.curr_pub=NS(publish=lambda m:messages.append(rounded(m.data)))
    v.pwm_pins=[PWM() for _ in range(4)];v.dir_pins=range(4)
    trace=[]
    for i,t in enumerate((0.0,.05,.10)):
        clock[0]=t
        v.current_callback(None)
        cmd=NS(linear=NS(x=7.,y=4.),angular=NS(z=9.))
        v.cmd_wrench_callback(cmd)
        v.run(None)
        trace.append(dict(time=t,i=messages[-1],duty=rounded([w.duty for w in v.pwm_pins])))
        assert all(x>0 for x in v.throttles)
        # Historical scalar behavior modeled by plain Python floats at
        # the input cut. This does not change the signs or magnitudes.
        # The unadapted NumPy 2 control is run separately below.
        if legacy_scalar_adapter:
            v.throttles=[float(x) for x in v.throttles]
    remembered=rounded(v.throttles)
    clock[0]=.601;v.run(None)
    timeout=rounded([w.duty for w in v.pwm_pins])
    assert timeout==[0.]*4 and rounded(v.throttles)==remembered
    return dict(trace=trace,warnings=warn,timeout_duty=timeout,stored_throttle=remembered)

def corners(center,rates,err,age,proj):
    spans=[(x-e-age*l,x+e+age*l) for x,l,e in zip(center,rates,err)]
    vals=[sum(a*b for a,b in zip(proj,p)) for p in itertools.product(*spans)]
    return min(vals),max(vals)
def bound(center,rates,err,age,proj):
    nom=sum(x*a for x,a in zip(center,proj))
    radius=sum(abs(a)*(e+age*l) for a,e,l in zip(proj,err,rates))
    return nom-radius,nom+radius
def main(src):
    ok=native(src)
    broken=[native(src,True,c) for c in range(4)]
    assert not ok['warnings'] and all(len(r['warnings'])==3 for r in broken)
    assert all(r['trace']==ok['trace'] for r in broken)
    later=native(src,legacy_scalar_adapter=False)
    try:
        _=(1,-1)[np.float64(1.)<0]
        rejects=False
    except TypeError: rejects=True
    assert len(later['warnings'])==(2 if rejects else 0)
    r=Random(15007)
    for _ in range(3200):
        draw=lambda l,u:[F(r.randint(l,u),5) for i in range(4)]
        center,rates,err,proj=draw(-6,6),draw(0,3),draw(0,3),draw(-2,3)
        age=F(r.randrange(10),5)
        assert corners(center,rates,err,age,proj)==bound(center,rates,err,age,proj)
    # A normalized scalar comparison makes the freshness boundary visible.
    args=([F(1),0,0,0],[F(1,2),0,0,0],[F(1,4),0,0,0])
    p=(1,0,0,0)
    assert bound(*args,F(1,2),p)[0]==F(1,2)
    assert bound(*args,F(3,4),p)[0]<F(1,2)
    return dict(fresh=ok,sensor_faults=broken,exact_corner_checks=3200,
                scalar_index_rejected=rejects,unadapted_warnings=len(later['warnings']),
                directional_guard_age='1/2 in normalized authored units')
if __name__=='__main__':
    print(json.dumps(main(Path(sys.argv[1])),sort_keys=True,separators=(',',':')))
