from itertools import product
import subprocess,json,sys
from motion import World,Layout,optimum,rollout,paid,normal_cut

def audit():
    rows=[];holds={};policy_memo=0
    worlds=(World('right',False,True),World('left',True,True))
    weak=(worlds[0],World('left',True,False))
    unknown=(worlds[0],World('right',True,True))
    cases=[(Layout(k,q,l,r,d,bool(w)),m) for k,q,l,r,d,w,m in
           product(range(1,6),range(1,4),(2,3),(2,3),range(5,10),(0,1),
                   ('correlated','lost-wire'))]
    cases.extend((Layout(4,1,3,3,d,True),'decoupled') for d in range(5,10))
    for L,law in cases:
        ws=worlds if law=='correlated' else weak if law=='lost-wire' else unknown
        res,memo=optimum(L,ws)
        policy_memo+=memo
        cut=None if law=='decoupled' else normal_cut(L,law=='correlated')
        assert (res is None)==(cut is None),(L,law,res,cut)
        if res is not None:assert res[:2]==(1,cut),(L,law,res,cut)
        if res is not None:
            for w in ws:
                s,trace=rollout(L,w,res[2])
                tail,optional=paid(s)
                assert tail and s.place=='base' and s.t<=L.due
                rows.append((int(w.lost_primary),s.instruction_at,s.type_of_contact,1,int(optional)))
                if L==Layout(4,1,3,3,7,True) and law=='correlated':
                    holds[str(w.closed)]=dict(trace=trace,arrived=s.t,applied=s.applied)
    # Separate physical timing and observation-support controls.
    expected_fixed=[]
    for lost,receipt,ch in product((0,1),(-1,3,4,5,6,7,8),(0,1,2)):
        rebind=receipt in (3,4) and ch!=2
        expected_fixed.append((lost,receipt,ch,int(bool(lost)==rebind),int(not rebind)))
    plots=rows+expected_fixed
    got=subprocess.run([sys.argv[1]],input=''.join(f'{l} {r} {c}\n' for l,r,c,_,_ in plots),
                       stdout=subprocess.PIPE,text=True,check=True)
    for inp,line in zip(plots,got.stdout.splitlines(),strict=True):
        old0,old1,new,other,placed,command=map(int,line.split())
        assert old0==other==1 and (old1,new)==inp[3:] and placed==int(not new),(inp,line)
        assert command==int(inp[1]>=0 and inp[2]==1),(inp,line)
    assert holds['left']['applied']==4
    for wire,scenario in ((False,worlds),(True,weak),(True,unknown)):
        assert optimum(Layout(4,1,3,3,7,wire),scenario)[0] is None
    shortened=(World('left',True,True,2),World('right',False,True,2))
    for visibility in (1,2,3):
        case=Layout(4,1,3,3,7,True,visibility)
        robust=optimum(case,shortened)[0]
        assert (robust is not None)==(visibility>=2)
    print(json.dumps(dict(qualified_range_controls=3,layout_controls=len(cases),visited_observation_states=policy_memo,
         native_policy_histories=len(rows),native_cut_controls=len(expected_fixed),witness=holds),
         sort_keys=True,indent=2))

if __name__=='__main__':audit()
