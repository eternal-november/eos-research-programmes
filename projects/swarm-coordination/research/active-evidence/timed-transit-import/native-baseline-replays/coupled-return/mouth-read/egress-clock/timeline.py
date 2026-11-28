from decimal import Decimal as D
from pathlib import Path
from egress import duration,clipped,GATE_B,GATE_A,INPUTS
import json
P=Path(__file__).resolve().parent

# Source-weighted first paths from the already independently certified
# upstream fork. Rechecked against the larger placed asset selection.
BRANCH={
  'near':[(100,100,6),(75,100,6)],
  'far':[(100,100,6),(100,83,6),(101,83,6),(101,82,6),
         (102,82,6),(102,82,7),(102,75,7),(102,75,8),(100,75,8)]}
def load(k):return [tuple(x) for x in json.loads((P/(k+'.json')).read_text())]

def box(a,b):
    # Rational overapproximation; covers all swept volumes including
    # .3 m world-aligned conservative body dimension.
    return tuple(D(min(x,y))-D('.3005') for x,y in zip(a,b)),tuple(D(max(x,y))+D('.3005') for x,y in zip(a,b))
def schedule(path,t):
    schedule=[]
    for a,b in zip(path,path[1:]):
        u=t+duration([a,b])
        schedule.append((t,u,box(a,b)));t=u
    return schedule,t

def minimum_temporal_gap(first,second):
    out=D('Infinity')
    for a,b,(al,ar) in first:
        for c,d,(bl,br) in second:
            if all(max(s,u)<=min(t,v) for s,t,u,v in zip(al,ar,bl,br)):
                out=min(out,max(a,c)-min(b,d))
    return out

def overlap(first,second):
    for a,b,(al,ar) in first:
        for c,d,(bl,br) in second:
            if max(a,c)<=min(b,d) and all(max(s,u)<=min(t,v) for s,t,u,v in zip(al,ar,bl,br)):
                return (a,b,c,d)
    return None

def run():
    I=load('installer')
    I=I[:-2]+[(0,3,I[-3][2]),(0,3,6)]
    IR=[(D(0),D(14),box((100,50,8),(100,60,8)))]
    iend=0
    scale=10
    for iwait in range(101):
        st=D(14)+D(iwait)/scale
        iwalk,iend=schedule(I,st)
        insert=[(D(14),st,box(I[0],I[0]))] if st>D(14) else []
        timeline=IR+insert+iwalk+[(iend,D(200),box(I[-1],I[-1]))]
        opts={}
        for k,E in [('far','far_short'),('near','near')]:
            p=BRANCH[k];BR,arr=schedule(p,D(5))
            receipt=arr+D('.5') # scope assumption, not stock timing
            assert receipt<=35
            for w in range(401):
                added=D(w)/scale
                follow,end=schedule(load(E),receipt+added)
                BW=[(D(0),D(5),box(p[0],p[0]))]+BR
                BW+=[(arr,receipt+added,box(p[-1],p[-1]))]+follow
                BW+=[(end,D(200),box((0,0,6),(0,0,6)))]
                assert load(E)[0]==p[-1]
                if end<=200 and minimum_temporal_gap(timeline,BW)>D('.25'):
                    opts[k]=added,end,receipt,minimum_temporal_gap(timeline,BW)
                    break
        if len(opts)==2:
            print('installer leaves at',st,'arrives',round(iend,6))
            for k,(w,end,receipt,gap) in opts.items():
                assert gap>D('.000001')
                print(k,'report',round(receipt,6),'egress',round(end,6),'at endpoint waits',w,'temporal gap',round(gap,6))
            break
    else:
        raise AssertionError('no schedule found')
    # A blind first-side decision is fixed before the distinguishing cue;
    # the lower bounds already grant zero polling, no collisions and no
    # receipt delay. Rescue extensions within this library still fully
    # retrace the first path before accessing the other arm.
    F,N=duration(BRANCH['far']),duration(BRANCH['near'])
    forced_far=min(F+duration(load('far_detour')),2*F+N+duration(load('near')))
    forced_near=2*duration(BRANCH['near'])+duration(BRANCH['far'])+duration(load('far_short'))
    assert clipped(load('near'),GATE_B)
    assert forced_far>200 and forced_near>200
    print('fixed-first relaxed egress bounds within the library:',round(forced_far,6),round(forced_near,6))
if __name__=='__main__':run()
