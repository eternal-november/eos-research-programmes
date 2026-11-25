"""Audit effect spans and observed vs actual outputs via pointwise time tests."""
from itertools import product
from copy import deepcopy
from checks import seed
from mission import Fixture,State

def absent(w,k,name,t0,t1):
    return any(any(a<=t<b for a,b in w.get(k,{}).get(name,[]))
               for t in range(t0,t1))

def launch(f,i,s,a):
    z=f.step(i,s,a)
    while z.busy_until>z.tick:z=f.step(i,z,("advance",))
    return z

def compare():
    n=0
    for dur,t0,down,length,mask,ack,source in product(
            range(1,5),range(2,7),range(2,8),(1,3),range(3),(False,True),(False,True)):
        d=seed(B=15,H=20);d["round_d"]=dur
        d["worlds"]=[{"radio_down":{},"slots_down":{},"coupled_resources_down":{}}]
        d["resources"]=["feed"]; d["slots"][1]["needs"]=["feed"]
        world=d["worlds"][0];interval=[[down,down+length]]
        if mask==0:world["radio_down"]={"r1":interval}
        if mask==1:world["slots_down"]={"r1":interval}
        if mask==2:world["coupled_resources_down"]={"feed":interval}
        if ack:world["radio_down"]["ack"]=interval
        if not source:world["absent_stock"]={"A":["r1"]}
        f=Fixture(d);s=State(t0,"J",charge=50)
        z=launch(f,0,s,("send",(("A","r1"),("B","r2"))))
        A=(source and not any(absent(world,k,key,t0,t0+dur) for k,key in
            (("radio_down","r1"),("slots_down","r1"),("coupled_resources_down","feed"))))
        actual=(("A",t0+dur),("B",t0+dur)) if A else (("B",t0+dur),)
        assert z.delivered==actual and z.tick==t0+dur
        assert z.receipts==(() if absent(world,"radio_down","ack",t0,t0+dur) else actual)
        n+=1
    print(n,"independent pointwise service, resource and receipt audits")

def validation():
    d=seed()
    d["worlds"][0]["radio_down"]={"mistyped-id":[[5,6]]}
    try:Fixture(d)
    except AssertionError:pass
    else:raise AssertionError("mistyped source silently accepted")
    print("unknown physical source identifier rejected")

def capacity():
    d=seed(B=10,H=12)
    d["shared_capacity"]={"wire":1}
    for slot in d["slots"]:slot["band_use"]={"wire":1}
    f=Fixture(d);assert not any(a[0]=="send" for a in f.choices(f.initial(0)))
    d["all_in_round"]=False
    f=Fixture(d);assert all(a[0]!="send" or len(a[1])==1 for a in f.choices(f.initial(0)))
    print("two different slot IDs on a shared unit-capacity bank cannot be reserved together")
if __name__=="__main__":compare();validation();capacity()
