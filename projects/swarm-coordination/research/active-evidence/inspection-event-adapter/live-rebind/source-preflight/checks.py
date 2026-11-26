from pathlib import Path
from hashlib import sha1
from itertools import product
from importlib.util import spec_from_file_location,module_from_spec
import subprocess,json,sys
from policy import WORLDS,ACTS,CASES,exact,direct,execute,feasible_at_same_info,PE,FE,F

def audit():
    candidates=list(product(range(4,8),range(1,4),range(1,4),(0,1)))
    native=[(*p,*w,*a) for p,w,a in product(candidates,WORLDS,ACTS)]
    replay=subprocess.run([sys.argv[1]],input=''.join(' '.join(map(str,x))+'\n' for x in native),
                          stdout=subprocess.PIPE,text=True,check=True)
    all_rows={p:{} for p in candidates}
    for arg,row in zip(native,replay.stdout.splitlines(),strict=True):
        p,w,a=arg[:4],arg[4:10],arg[10:]
        fields=tuple(map(int,row.split()))
        assert fields==direct(p,w,a),(arg,fields)
        assert fields[5:]==(1,1)
        all_rows[p][w,a]=fields

    tracked={};verified=0;motion_pairs=0
    old=Path(sys.argv[2]).resolve()/'motion.py'
    b=old.read_bytes()
    assert sha1(f"blob {len(b)}\0".encode()+b).hexdigest()=="edf89dde9225d56c50cc1378c20b432a13af3b3e"
    spec=spec_from_file_location('verified_geometry',old)
    plant=module_from_spec(spec)
    sys.modules[spec.name]=plant;spec.loader.exec_module(plant)

    for p in candidates:
        raw=all_rows[p]
        matched={key:direct(p,*key) for key in raw}
        for mode,worlds in CASES.items():
            answer=exact(raw,worlds)
            yes=feasible_at_same_info(matched,worlds)
            assert (answer is not None)==yes
            # Separate global policy metric on the observation-induced tables.
            if answer is not None:
                expected=exact(matched,worlds)
                assert expected[0]==answer[0]
                scored=0
                for w,arm in product(worlds,('left','right')):
                    effect,_=execute(raw,answer[1],w)
                    goal=plant.Layout(4,1,3,3,7,False)
                    hiding=plant.World(arm,False,False,2)
                    s=plant.apply(goal,plant.State(hiding),'K')
                    s=plant.apply(goal,s,'right' if s.got_view=='left' else 'left')
                    assert s is not None and s.place=='base' and s.t==4
                    assert effect[2]==effect[5]==effect[6]==1
                    scored+=effect[3]
                    motion_pairs+=1
                assert scored==2*answer[0]
            verified+=1
            if p in ((5,1,1,0),(5,1,1,1),(5,1,2,0)):
                tracked[str((p,mode))]=answer

    p=(5,1,1,0);early=all_rows[p]
    assert exact(early,CASES['stable'])[0]==1
    assert exact(early,CASES['one_sided_erasure'])[0]==1
    assert exact(early,CASES['two_silent_branches']) is None
    assert exact(early,CASES['drift']) is None
    assert exact(early,CASES['both_routes_can_fail']) is None
    assert exact(all_rows[(5,1,2,0)],CASES['one_sided_erasure']) is None
    late=all_rows[(5,1,1,1)]
    assert exact(late,CASES['one_sided_erasure'])[0]==1
    decision=exact(late,CASES['one_sided_erasure'])[1]
    assert execute(late,decision,F)[1][2] # protect fallback capacity before .5
    # The missing primary measurement does not decide which route works.
    for a in ACTS:
        assert early[PE,a][:2]==early[FE,a][:2],a
    # Positive fallback observation and authorization after it are different.
    too_large=all_rows[(5,1,2,0)][F,(1,1,1,1)]
    assert too_large[1]==1 and too_large[2]==0 and too_large[4]==0

    print(json.dumps(dict(native_rows=len(native),belief_cases=verified,
       decoupled_geometry_paired_winning_rollouts=motion_pairs,
       representative_cases=tracked),sort_keys=True,indent=2))

if __name__=='__main__':audit()
