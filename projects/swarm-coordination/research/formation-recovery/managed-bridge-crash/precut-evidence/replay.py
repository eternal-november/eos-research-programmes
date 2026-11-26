"""Source- and time-qualified pre-cut evidence, plus actual early radio debits."""
from collections import Counter
from itertools import combinations, product
from pathlib import Path
import json
import numpy as np
import subprocess
import sys

up=Path(sys.argv[1])
text=(up/"local.py").read_text()
assert text.endswith("\nrun()\n")
prior={}
exec(compile(text[:-len("run()\n")],str(up/"local.py"),"exec"),prior)
s,body,p,v,C,E,ids=prior["actual_cut"]()
left=C[0][0];right=C[1];peer=right[0]
a=p[peer]-p[left]
a/=np.linalg.norm(a)
ort=np.array([-a[1],a[0]])
R=s.sensing_distance
BRIDGE=R-s.reconfiguration.edge_activation_margin
safe=s.collision_distance
caps=1.
error_bound=.1
endpoints={-1:-.8,1:.8}
popen=subprocess.Popen([sys.argv[2]],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True,bufsize=1)
def ask(*z):
    popen.stdin.write(" ".join(map(str,z))+"\n")
    popen.stdin.flush()
    return popen.stdout.readline().strip()

def geom(kind,truth,t):
    z=(t+3)/3
    start=0. if kind=="late-read" else .2
    r=p+t*v
    r[right,:]+=(start+(endpoints[truth]-start)*(3*z*z-2*z*z*z))*ort
    return r

def certify_path(kind,truth):
    accel=abs(endpoints[truth]-(0. if kind=="late-read" else .2))*2/3
    assert accel<1 and max(np.linalg.norm(v[j]) for j in ids+[body])+accel*3/4<1
    old_edges=E|{tuple(sorted((body,left))),tuple(sorted((body,peer)))}
    lower=float("inf")
    upper=0.
    no_view=float("inf")
    times=np.linspace(-3,0,301)
    for t,u in zip(times,times[1:]):
        x,y=geom(kind,truth,t),geom(kind,truth,u)
        for i,j in combinations(sorted(ids+[body]),2):
            q=accel*(u-t)**2/8
            lo=prior["min_chord"](x[i]-x[j],y[i]-y[j])-q
            lower=min(lower,lo)
            if (i,j) in old_edges:
                upper=max(upper,max(np.linalg.norm(x[i]-x[j]),np.linalg.norm(y[i]-y[j]))+q)
            if i==left and j in right:no_view=min(no_view,lo)
    assert lower>safe and upper<R and no_view>R
    return [round(float(lower),8),round(float(upper),8),round(float(no_view),8)]

def settled_positions(truth):
    g=geom("late-read",truth,0)
    w=prior["witness"](g,v,C,E,body,caps,caps,BRIDGE,s)
    assert w[0]<1.11
    q=g.copy()
    for i in ids:q[i]+=float(np.linalg.norm(v[i]))*v[i]/(2*caps)
    i,j=w[5]
    r=q[j]-q[i]
    d=(np.linalg.norm(r)-BRIDGE)/2
    direction=r/np.linalg.norm(r)
    q[left]+=d*direction
    q[right,:]-=d*direction
    return q,float(w[0])

physical={z:settled_positions(z) for z in endpoints}
for source,actual in ((1,-1),(-1,1)):
    assert min(np.linalg.norm(physical[source][0][left]-physical[actual][0][j])
               for j in right)>BRIDGE+.01

def read_raw(kind,truth,k,noise):
    t=k/4
    at=geom(kind,truth,t)
    assert np.linalg.norm(at[body]-at[peer])<R
    # Sensor reads a relative coordinate, not an episode label.
    baseline=(p[peer]+t*v[peer])-(p[body]+t*v[body])
    return float((at[peer]-at[body]-baseline)@ort)+noise

def keys(raw,stamp):
    # Relative offset can change no faster than the physical robot
    # plus the drift of the known nominal moving reference.
    allowance=(caps+float(np.linalg.norm(v[peer])))*(-stamp/4)+error_bound
    from_lower=sorted(z for z,y in endpoints.items() if raw-allowance<=y<=raw+allowance)
    direct=sorted(z for z,y in endpoints.items() if abs(y-raw)<=allowance)
    assert from_lower==direct
    return from_lower

def trial(kind,truth,noise,early,late,debt,arm):
    assert ask("reset")=="ok"
    interactions=[]
    def send(t,source,dest,body,path=True):
        y,charge=ask("send",t,source,dest,body,int(path)).split()
        interactions.append((t,source,dest,body,y,int(charge)))
        assert y in ("-",body) and int(charge) in (0,len(body))
        return y
    k=-4 if kind=="late-read" else -12
    # Capture is charged one before-use sensor interval; transmission
    # occurs no earlier than the second cut after the sample.
    first=k+2
    read=read_raw(kind,truth,k,noise)
    admitted=keys(read,k)
    assert truth in admitted
    if debt:
        assert send(first-4,"P","sink","used",False)=="-"
        assert interactions[-1][-1]==4
    assert ask("side",first-3)=="1"
    chosen=None
    receipt=None
    if len(admitted)==1 or arm=="raw":
        sign=admitted[0] if arm!="raw" else (1 if read>0 else -1)
        payload="c7+" if sign>0 else "c7-"
        attempts=[(first+1,late)] if arm=="reserve" else [(first,early),(first+1,late)]
        for t,up_link in attempts:
            g=geom(kind,truth,t/4)
            assert t<0 and np.linalg.norm(g[left]-g[body])<R
            payload_seen=send(t,"P","proof",payload,up_link)
            if payload_seen==payload:
                receipt=t
                # This is an authored trusted endpoint and current message
                # scope; do not pass the physical sign to the controller.
                chosen=1 if payload_seen[-1]=="+" else -1
                break
    if chosen is None:
        outcome=None
    else:
        q=physical[truth][0]
        p_local=physical[chosen][0][left]
        gap=float(min(np.linalg.norm(p_local-q[j]) for j in right))
        outcome=gap<=BRIDGE+1e-8
        assert outcome==(chosen==truth)
    if arm!="raw":
        assert not (chosen is not None and chosen!=truth)
    return dict(read_sensor_intervals=1,choices=admitted,actual_choice=chosen,receipt_tick=receipt,
                bridge_by_deadline=outcome,side=1,tape=interactions,
                native_bytes=1+sum(x[-1] for x in interactions))

out={}
selected={}
for args in product(("late-read","early-reassignment"),(-1,1),(-.08,0.,.08),
                    (False,True),(False,True),(False,True)):
    kind,truth,noise,early,late,debt=args
    all_={}
    for arm in ("typed","direct","reserve","raw"):
        x=all_[arm]=trial(*args,arm)
        out.setdefault((kind,arm),Counter()).update(cases=1,paid=int(x["bridge_by_deadline"] is True),
                wrong=int(x["bridge_by_deadline"] is False),
                evidence_intervals=x["read_sensor_intervals"],bytes=x["native_bytes"])
    assert all_["typed"]==all_["direct"]
    if noise==0. and late:
        selected["/".join(map(str,(kind,truth,early,debt)))]=all_
key="late-read/1/False/False"
a=selected[key]
assert a["typed"]["receipt_tick"] is None and a["reserve"]["receipt_tick"]==-1
assert a["typed"]["tape"][0][-1]==3 and a["typed"]["tape"][-1][-1]==0
key="early-reassignment/-1/True/False"
assert selected[key]["typed"]["actual_choice"] is None
assert selected[key]["raw"]["bridge_by_deadline"] is False
popen.stdin.close()
assert popen.wait()==0
print(json.dumps(dict(totals={"/".join(k):v for k,v in out.items()},samples=selected,
         prehistory={f"{k}/{z}":certify_path(k,z) for k,z in product(("late-read","early-reassignment"),(-1,1))}),
         sort_keys=True))
