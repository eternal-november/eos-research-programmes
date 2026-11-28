from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from chords import *

T,F,_=load_scene();m=Map(T,F)
J=json.loads((HERE/'expected-paths.json').read_text())
I=load('installer');I=I[:-2]+[(0,3,I[-3][2]),(0,3,6)]
it,iend=schedule(I,D(14))
it=[(D(0),D(14),box((100,50,8),(100,60,8)))]+it+[(iend,D(200),box(I[-1],I[-1]))]
B=chords(m,BRANCH['far'],GATE_A)
pref,arr=at(B,D(0));tc=arr+D('.5')
paths={
    'near':B[::-1]+BRANCH['near'][1:]+list(map(tuple,J['adaptive-near']['path']))[1:],
    'far':list(map(tuple,J['far_short']['path']))
}
print('shortened first far approach',len(B)-1,'legs',arr)
print('first approach:',B)
for k,p in paths.items():
    g=GATE_A if k=='near' else GATE_B
    assert all(m.certificate(a,b)>0 and not clipped([a,b],g) for a,b in zip(p,p[1:]))
    for i in range(601):
        st=tc+D(i)/10;q,end=at(p,st)
        xx=pref+[(arr,st,box(B[-1],B[-1]))]+q+[(end,D(200),box(p[-1],p[-1]))]
        if end<=D('167.5') and minimum_temporal_gap(it,xx)>D('.25'):
            print(k,'finish',round(end,6),'wait',D(i)/10)
            break
    else:raise AssertionError(k)
print('Both geometry/timing branches fit the 167.5-second diagnostic.')
