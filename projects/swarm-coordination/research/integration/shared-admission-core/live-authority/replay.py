from collections import defaultdict
from dataclasses import replace
from hashlib import sha1
from itertools import product
import json, subprocess, sys
from pathlib import Path
native,space,shared=sys.argv[1:]
data=(Path(shared)/'core.py').read_bytes()
assert sha1(f"blob {len(data)}\0".encode()+data).hexdigest()=="687bf1250c6725992b6de696d0781d7948b4a89e"
sys.path.insert(0,shared)
from core import Event, Fragment, admitted, check, join, view

F=frozenset
DUE={'prior-clear':19,'second-crossing':20,'disjoint':13}
CUT=11
NAMES=tuple(product((12,15,19),range(2),range(2)))
empty=F()

def cap(version,site):
    return ('grant',version,site)

def fragment(p,log,renew,law):
    clear=p[0]
    hist=tuple((t,s,i,e) for t,s,i,e,_,_,_ in log)
    events=[]
    last=empty
    for t,site,version,end in hist:
        active=F((cap(version,site),)) if end>=1 else empty
        if active!=last:
            events.append(Event(t,0,add=active-last,drop=last-active))
            last=active

    def issue(row):
        t,site,i,end,*_=row
        return (i,site,bool(end))
    received=[(5,'crew',issue(log[5]))]
    if renew:
        received.append((CUT,'crew',issue(log[CUT])))
    known={(i,s) for _,_,(i,s,ok) in received if ok}
    opts={}
    for t,i,s in NAMES:
        if (i,s) not in known:
            continue
        n=F((cap(i,s),))
        x=empty if s else F(('X-occupied',))
        opts[t,i,s]=(
            Event(t,2,need=n,absent=x),
            Event(t+1,2,need=(n if law=='through' else empty),
                  absent=x,paid=('second-crossing',)))
    events.append(Event(13,1,paid=('disjoint',) if log[13][-1]==1 else ()))
    ident=(p,renew,law)
    au=Fragment(ident,tuple(received),empty,tuple(events))
    ph=Fragment(ident,(),F(('X-occupied',)),
         (Event(clear,1,drop=F(('X-occupied',)),paid=('prior-clear',)),))
    return join((au,),(ph,),opts)[0]

def direct(p,log,renew,law,a):
    t,i,s=a
    ticket=any(log[j][1:4]==(s,i,1) for j in ((5,CUT) if renew else (5,)))
    available=(s==1 or p[0]<=t)
    actual=log[t][1:4]==(s,i,1)
    durable=law=='issue' or log[t+1][1:4]==(s,i,1)
    return ticket and available and actual and durable and p[0]<=19 and log[13][-1]==1

def collect(ps):
    q=''.join(' '.join(map(str,p))+' 0\n' for p in ps)
    z=subprocess.run([native],input=q,check=True,capture_output=True,text=True)
    rows=[tuple(map(int,l.split())) for l in z.stdout.splitlines()]
    assert len(rows)==len(ps)*21
    return {p:rows[i*21:(i+1)*21] for i,p in enumerate(ps)}

def main():
    physical=json.loads(Path(space).read_text())
    clear=sorted({x['real_y_relocation'] for x in physical if x['actual_due_paid']})
    assert clear==[6,18,19]
    ps=list(product(clear,(10,12,13,16,99),range(2),(10,12,15,99),(11,99)))
    logs=collect(ps)
    count=defaultdict(int)
    regions=defaultdict(list)
    for p,log in logs.items():
        c,e,s,w,late=p
        for t,ss,i,end,a,d,z in log:
            assert i==(t>=e) and ss==(s if t>=e else 0)
            assert a==1+(t>=c) and d==1 and z==(t>=13)
            # Old readiness has freed native booking X at t=4 even if
            # the physical occupancy source has not yet witnessed departure.
            assert end==int(4<=t<e or e<=w<=t), (p,log)
        for r,law in product(range(2),('issue','through')):
            row=fragment(p,log,r,law)
            a=tuple(k for k in NAMES if check(row,k,CUT,DUE))
            d=tuple(k for k in NAMES if direct(p,log,r,law,k))
            assert a==d,(p,r,law,a,d)
            regions[r,law,p[3]].append((row,d))
            count['full_trajectory_checks']+=len(NAMES)
            count['qualified_options']+=len(a)
    for (r,law,w),group in regions.items():
        b=defaultdict(list)
        for row,d in group:b[view(row,'crew',CUT)].append(d)
        found=admitted([row for row,_ in group],'crew',CUT,DUE,NAMES)
        exp={obs:tuple(k for k in NAMES if all(k in x for x in choices))
             for obs,choices in b.items()}
        assert found==exp
        count['local_views']+=len(found)
        count['local_views_with_option']+=sum(bool(v) for v in found.values())

    def witness(p,r,law):
        row=fragment(p,logs[p],r,law)
        return [view(row,'crew',CUT),[a for a in NAMES if check(row,a,CUT,DUE)]]
    # Native grant and physical occupation are different clocks.
    x=(18,99,0,99,99)
    assert logs[x][12][3]==1 and logs[x][12][4]==1
    assert not check(fragment(x,logs[x],1,'issue'),(12,0,0),CUT,DUE)
    # Same range-end now, physically different grant after rebind.
    y=(18,10,1,10,99)
    assert logs[y][11][3]==logs[x][11][3]==1
    assert (12,1,1) in witness(y,1,'issue')[1]
    assert witness(y,0,'issue')[1]==[]
    identical=(6,10,0,10,99)
    assert logs[identical][11][1:4]==(0,1,1)
    assert witness(identical,0,'issue')[1]==[]
    assert (12,1,0) in witness(identical,1,'issue')[1]
    # Old delayed readiness fails to re-authorize a replaced reservation.
    lost=(18,10,1,99,11)
    assert logs[lost][11][3]==0 and witness(lost,1,'issue')[1]==[]
    # Even a fresh cut doesn't constrain an authorized replacement at/after issue.
    old=(6,13,1,15,99)
    assert (12,0,0) in witness(old,1,'issue')[1]
    assert (12,0,0) not in witness(old,1,'through')[1]
    e=(6,12,1,12,99)
    assert witness(old,1,'issue')[0]==witness(e,1,'issue')[0]
    assert (12,0,0) not in witness(e,1,'issue')[1]
    match=admitted([fragment(p,logs[p],1,'issue') for p in (old,e)],'crew',CUT,DUE,NAMES)
    assert set(match.values())=={()}
    # Local inline requalification is a materially different interface.
    # In these selected controls the same native process acknowledges the
    # modeled completion after the gate, and disjoint work still completes.
    controls=[
        ((6,16,1,15,99),(0,1,1)),
        ((18,12,1,12,99),(1,1,1)),
        ((18,99,0,99,99),(-1,0,1)),
        ((6,10,0,99,11),(-1,0,1)),
        ((6,13,1,15,99),(0,0,1))]
    selected=[]
    for p,expected in controls:
        line=' '.join(map(str,p))+' 1\n'
        lines=subprocess.run([native],input=line,check=True,capture_output=True,text=True).stdout.splitlines()
        assert len(lines)==22
        actual=tuple(map(int,lines[-1].split()))
        assert actual==expected
        selected.append([p,actual])
    def wk(p,r,law):return {'input':p,'received_and_options':witness(p,r,law)}
    print(json.dumps(dict(native_schedules=len(ps),native_cuts=len(ps)*21,physical_runs=len(physical),
        counts=dict(count),local_qualification=selected,witnesses={'native_early_grant':wk(x,1,'issue'),
              'new_current_geometry':wk(y,1,'issue'),'same_geometry_new_version':wk(identical,1,'issue'),'no_updated_receipt':wk(y,0,'issue'),
              'late_old_readiness':wk(lost,1,'issue'),'version_changes_during_motion_issue':wk(old,1,'issue'),
              'version_changes_during_motion_through':wk(old,1,'through'),'version_changes_before_issue':wk(e,1,'issue')}),
           indent=2,sort_keys=True))
if __name__=='__main__':main()
