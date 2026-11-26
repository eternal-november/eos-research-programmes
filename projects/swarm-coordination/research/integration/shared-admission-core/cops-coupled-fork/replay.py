"""Compare original COPS time-expanded flow with an independent state solver."""
from collections import defaultdict
from itertools import product
from hashlib import sha1
from pathlib import Path
import json,subprocess,sys
from bridge import FixtureGraph,initialize,scoped_solver

COPS,Constraint=initialize(sys.argv[1])
core_root=Path(sys.argv[2])
raw=(core_root/'core.py').read_bytes()
assert sha1(f"blob {len(raw)}\0".encode()+raw).hexdigest()=="687bf1250c6725992b6de696d0781d7948b4a89e"
sys.path.insert(0,str(core_root))
from core import Event,Row,admitted

H=5
INSPECT=3
EXIT=4
AGENTS={'scout':'S','mule':'M','base':'B'}
POLICY_CHOICES=('M','U','W','J')
NODES=('S','N','X','Y','I','E','M','U','W','G','J','Z','B')
SAFE={'M','Z'}
DUE={'inspect':3,'lead-safe':4,'mule-safe':5,'report':3}

def fixture(block,loss,branch,staging):
    movements=[('N','I'),('S','X'),('X','Y'),('Y','I'),('I','E'),
               ('M','U'),('M','W'),('W','G'),('G','Z'),('U','Z')]
    if not block:movements.append(('S','N'))
    if staging:movements += [('M','J'),('J','U'),('J','G'),('J','M')]
    # Named fixture comms channels; different from travel and separate
    # from line of sight. Only one Y receive contact survives after tick2.
    links=[('N','M'),('Y','U'),('Y','G'),('Z','B')]
    if not loss:links += [('N','B'),('X','B')]
    erase=tuple((t,'Y','U' if branch else 'G') for t in range(2,H+1))
    return tuple(movements),tuple(links),erase

def call(case,limit,masters=('scout','mule'),first=None,second=None):
    mv,links,closed=fixture(*case)
    # Unused optional cell J remains in the fixture alphabet to allow
    # testing an impossible forced position without modifying topology.
    graph=FixtureGraph(mv+tuple((v,v) for v in NODES),links,AGENTS)
    req=[('scout',INSPECT,('I',)),('scout',EXIT,('E',)),('mule',H,tuple(sorted(SAFE)))]
    if first is not None:req.append(('mule',1,(first,)))
    if second is not None:req.append(('mule',2,(second,)))
    cls=scoped_solver(COPS,Constraint,req,closed,
                      tuple((t,a,b) for a,b in links for t in range(limit+1,H+1) if b=='B'))
    c=cls(graph=graph,master=list(masters),static_agents=['base'],src=['scout'],snk=['base'],always_src=True)
    c.T=H
    sol=c.solve_flow(master=True,connectivity=True,frontier_reward=False,cut=False)
    if sol['status']=='infeasible':return None
    assert sol['status']=='optimal'
    assert c.traj[('scout',INSPECT)]=='I' and c.traj[('scout',EXIT)]=='E'
    assert c.traj[('mule',H)] in SAFE
    return {a:tuple(c.traj[(a,t)] for t in range(H+1)) for a in AGENTS}, c.conn

def reference(case,limit,masters=('scout','mule'),first=None,second=None):
    mv,links,closed=fixture(*case)
    edges=set(mv)
    # Only carry already present data along a traveled arc; a transition
    # cannot use a predecessor's later local observation.
    def att(t,positions,perm,report):
        local={(i,j) for i,p in enumerate(positions) for j,q in enumerate(positions)
               if (p,q) in links and (t,p,q) not in closed}
        changed=True
        while changed:
            old=perm,report
            for i,j in local:
                if perm>>i&1:perm |=1<<j
                if perm>>i&1 and report>>i&1:
                    if j!=2 or t<=limit:report |=1<<j
            changed=old!=(perm,report)
        return perm,report
    ini=tuple(AGENTS.values())
    p=sum(1<<i for i,a in enumerate(AGENTS) if a in masters)
    pool={(ini,p,1)}
    for t in range(H+1):
        nxt=set()
        for xyz,author,data in pool:
            if t==1 and first is not None and xyz[1]!=first: continue
            if t==2 and second is not None and xyz[1]!=second:continue
            if t==INSPECT and xyz[0]!='I':continue
            if t==EXIT and xyz[0]!='E':continue
            if t==H and xyz[1] not in SAFE:continue
            author,data=att(t,xyz,author,data)
            if t==H:
                if data&4 and author==7:return True
                continue
            moves=[set([z])|{y for x,y in edges if x==z and author>>j&1 and j!=2}
                   for j,z in enumerate(xyz)]
            nxt.update((tuple(b),author,data) for b in product(*moves))
        pool=nxt
    return False

def native_contacts():
    bin=sys.argv[3]
    cases=tuple(product(range(2),range(2),range(2),range(5),range(3)))
    data=''.join(' '.join(map(str,p))+'\n' for p in cases)
    out=subprocess.run([bin],input=data,text=True,capture_output=True,check=True).stdout.splitlines()
    assert len(out)==len(cases)
    for (block,loss,b,notice,pose),line in zip(cases,out):
        v=b if notice==0 else 1-b if notice==4 else -1
        report=(not loss) or (not block) or pose==b
        via= loss and report
        row=tuple(map(int,line.split()))
        d=1 if not loss else 3 if report else -1
        assert row==(v,int(notice!=1),int(via),int(report),1,d,2*int(not loss or not block or pose<=1),2*int(via))
    inline=[]
    for b,notice in product(range(2),range(5)):
        with subprocess.Popen([bin],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True) as p:
            p.stdin.write(f'1 1 {b} {notice} -1\n')
            p.stdin.flush()
            tag,read=p.stdout.readline().split()
            assert tag=='view'
            q=int(read)
            pose=q if q>=0 else 2
            p.stdin.write(f'{pose}\n')
            p.stdin.flush()
            r=tuple(map(int,p.stdout.readline().split()))
            p.stdin.close()
            assert p.wait(timeout=10)==0
        assert r[5]==(3 if notice==0 else -1)
        inline.append([b,notice,q,pose,r])
    return len(cases),inline

def main():
    matrix={}
    for block,loss,branch in product(range(2),repeat=3):
        p=(block,loss,branch,0)
        row=[]
        for limit in range(1,5):
            ans=call(p,limit)
            assert (ans is not None)==reference(p,limit),(p,limit,ans)
            row.append(ans is not None)
        matrix[str(p)]=row
    # Blocked travel alone keeps the report deliverable from X. Losing
    # direct contact alone still permits a handoff via old approach N.
    # Both remove all those continuations in the same report flow.
    assert matrix[str((0,0,0,0))]==[True]*4
    assert matrix[str((1,0,0,0))]==[True]*4
    assert matrix[str((0,1,0,0))]==[False,False,True,True]
    assert matrix[str((1,1,0,0))]==[False,False,True,True]
    assert matrix[str((1,1,1,0))]==[False,False,True,True]
    force={}
    for branch,flex,first in product(range(2),range(2),POLICY_CHOICES):
        p=(1,1,branch,flex)
        native=call(p,3,first=first)
        assert (native is not None)==reference(p,3,first=first),(p,first,native)
        force[branch,flex,first]=native is not None

    # The branch cue is available only at t=1, after the first move;
    # do not condition that first choice on the actual branch.
    noflex=[u for u in POLICY_CHOICES if all(force[b,0,u] for b in range(2))]
    withflex=[u for u in POLICY_CHOICES if all(force[b,1,u] for b in range(2))]
    assert not noflex and withflex==['J']
    # But a post-cut unknown branch cannot choose the second hop either.
    second={}
    trajectories=[]
    for branch,dest in product(range(2),('U','G')):
        p=(1,1,branch,1)
        solution=call(p,3,first='J',second=dest)
        ok=solution is not None
        assert ok==reference(p,3,first='J',second=dest)
        assert ok==((branch==0 and dest=='U') or (branch==1 and dest=='G'))
        second[branch,dest]=ok
        if ok:
            poses,comm=solution
            assert poses['scout'][2]=='Y' and poses['mule'][2]==dest and poses['mule'][3]=='Z'
            assert ('Y',dest,'scout') in comm[2]
            assert ('Z','B','scout') in comm[3]
            trajectories.append([branch,['S','X','Y','I','E'],['M','J',dest,'Z'],[[2,'Y',dest],[3,'Z','B']]])
    assert ('J','M') in fixture(1,1,0,1)[0]  # Preset physically separate retreat.

    assert not any(all(second[b,u] for b in range(2)) for u in ('U','G'))
    # Model explicit passed/failed report and carried services for the
    # shared core. It accepts a defined two-stage policy name, not choice
    # of a hidden full source trace at t=0.
    outcomes=[]
    for visible in range(2):
        names=tuple(product(('U','G'),repeat=(2 if visible else 1)))
        rows=[]
        for b in range(2):
            opts={}
            for d in names:
                target=d[b] if visible else d[0]
                terminal=(Event(3,3,paid=('report',)),) if second[b,target] else ()
                opts[d]=terminal
            rows.append(Row((),frozenset(),(Event(3,1,paid=('inspect',)),
                                Event(4,1,paid=('lead-safe',)),Event(3,2,paid=('mule-safe',))),opts))
        x=admitted(rows,'crew',0,DUE,names)[()]
        assert x==((('U','G'),) if visible else ()),x
        outcomes.append(x)
    missing=call((1,1,0,1),3,masters=('scout',),first='J')
    assert missing is None and not reference((1,1,0,1),3,masters=('scout',),first='J')
    uses=[]
    for branch in range(2):
        p=(1,1,branch,0)
        ordinary=call(p,3)
        assert ordinary is not None and reference(p,3)
        path=ordinary[0]['mule']
        moves=sum(a!=b for a,b in zip(path,path[1:]))
        assert moves==2+branch
        # The decoded adaptive route M-J-U/G-Z uses three moves either way.
        uses.append([moves,3])
    count,inline=native_contacts()
    print(json.dumps({'native_and_direct_nominal':matrix,
        'local_forced_first_move':{str(k):v for k,v in force.items()},
        'common_first':{'no_staging':noflex,'staging':withflex},
        'common_policies_after_staging':outcomes,
        'late_plan_no_master_can_move':False,
        'native_direct_checks':55,'known_vs_adaptive_mule_moves':uses,'decoded_cops_witnesses':trajectories,'subt_packet_controls':count,'staged_local_policy':inline},sort_keys=True,indent=2))

if __name__=='__main__':main()
