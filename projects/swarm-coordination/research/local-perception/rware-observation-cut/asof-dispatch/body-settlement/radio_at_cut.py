"""Known source namespace, qualified body cut and physically shared receive debit."""
from itertools import product
from collections import defaultdict
import json
import subprocess
import committed_pose as plant

def oracle(cap,events):
    sent=defaultdict(list);heard=[];out=[]
    def live(window,t):
        return sum(n for p,n in window if t-p<=16)
    for t,s,v in events:
        n=len(v)
        if live(sent[s],t)+n>cap:out.append('-');continue
        sent[s].append((t,n))
        if live(heard,t)+n>cap:out.append('-');continue
        heard.append((t,n));out.append(s+':'+v)
    return out

def frames(h):
    _,t,b,c=h['receipt'];assigned=f'A{t:02d}{b}{c}'
    os=h['settled_delta'][1]
    assert os in (0,1)
    cue='M' if os else 'Z'
    return assigned,cue

def admitted(callbacks,h,goal):
    # A pre-installed, controlled source namespace: E is authorized to
    # report the result of these three named ticks on actuator 4. There is
    # no payload space or defense here for unbound/reused sender slots.
    pd=[v[1:] for s,v in callbacks if s=='P' and len(v)==5 and v[0]=='A']
    sd=[v for s,v in callbacks if s=='E' and v in ('M','Z')]
    if len(pd)!=1 or len(sd)!=1:return None
    a=pd[0];j=('dispatch',int(a[:2]),int(a[2]),int(a[3]))
    old_x=2 if h['flag']==(j[3]==1) else 4
    fixed_nonactors=frozenset({(old_x,3),(1,6),(3,0),(6-old_x,6)})
    assert fixed_nonactors==frozenset(tuple(ij) for ij in h['nonactor_cells'])
    return plant.frozen_receiver(j,h['flag'],(1,4,1,21,0,int(sd[0]=='M'),h['heading'],fixed_nonactors),
                                 h['heading'],2,(3,goal))

def main():
    scenes={(p,s,b):plant.replay(s,p,b) for p,s,b in product((2,4),(14,9),(False,True))}
    qs=[]
    for k,h in scenes.items():
        p,e=frames(h)
        Q=(15,'Q','OK4') # old source action actually changes request to item4
        E=(21,'E',e)
        W=(21,'W',e)     # identical bytes, deliberately different source
        P=lambda at:(at,'P',p)
        patterns={
            'near-minimum':(P(15),Q,E),
            # E is released by 21, but P already exists at time 1. At cut
            # 21, t5 equals one second old. Launch t4 expires the debit.
            'expired':(P(4),Q,E),
            'inclusive':(P(5),Q,E),
            'invalid-first':(P(15),Q,W,E),
            'qualified-first':(P(15),Q,E,W),
            'invalid-only':(P(4),Q,W),
            'late':(P(4),Q,(22,'E',e)),
            'missing-origin':(Q,E),
        }
        for cap,(name,events) in product(range(4,12),patterns.items()):
            qs.append((k,cap,name,events))
    inp=[]
    for _,cap,_,es in qs:
        inp.append(f'{cap} {len(es)}');inp.extend(f'{t} {s} {v}' for t,s,v in es)
    all_rows=subprocess.run(['./pose_deliver'],input='\n'.join(inp)+'\n',text=True,check=True,capture_output=True).stdout.splitlines()
    assert len(all_rows)==len(qs)
    table={};joints=0
    for (k,c,n,es),line in zip(qs,all_rows):
        h=scenes[k];_,_,blocked=k
        count,*out=line.split()
        assert int(count)==len(es) and out==oracle(c,es)
        old=any(d=='Q:OK4' and t<=15 for d,(t,_,_) in zip(out,es))
        offered=[tuple(d.split(':',1)) for d,(t,_,_) in zip(out,es) if d!='-' and t<=21]
        answers=[admitted(offered,h,y) for y in (3,4)]
        good=answers[0 if blocked else 1]
        exact=h['results'][str(3 if blocked else 4)]['direct']
        assert good in (None,exact) and answers[1 if blocked else 0] is None
        if n in ('near-minimum','inclusive','qualified-first','invalid-first','expired'):
            thresh={'near-minimum':9,'inclusive':9,'qualified-first':9,'invalid-first':10,'expired':8}[n]
            assert (bool(good) and old)==(c>=thresh), (k,c,n,out,answers,thresh,old)
            solitary={'near-minimum':c in (6,7),'inclusive':c in (6,7),
                      'expired':c in (5,6,7),'qualified-first':c in (6,7),
                      'invalid-first':c==7}
            assert bool(good)==(c>=thresh or solitary[n]), (k,c,n,out,answers,thresh)
        else:assert good is None
        vals=(old,bool(good),any(d.startswith('W:') for d in out))
        if (c,n) in table:assert vals==table[c,n]
        table[c,n]=vals;joints+=bool(good) and old
    print(json.dumps({'cases':len(qs),'joint_deadlines':joints,
                      'cells':[(c,n,*v) for (c,n),v in sorted(table.items())]},
                     sort_keys=True,separators=(',',':')))
if __name__=='__main__':main()
