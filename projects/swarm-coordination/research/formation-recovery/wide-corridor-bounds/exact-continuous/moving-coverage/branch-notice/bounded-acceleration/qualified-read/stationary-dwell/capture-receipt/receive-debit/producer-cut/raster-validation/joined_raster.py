"""Exact interval decision using raster pixels, selected sensor output, and native receiver."""
from itertools import product
from subprocess import run
from struct import pack
from fractions import Fraction as F
import json
import sys
from pathlib import Path
import raster
from egl_depth import context,inputs

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'sensor/radio'))
import joined as radio
import motion
def main():
    s=inputs();context();g=raster.Render(s)
    arm=list(product(('near','far'),(0,1),(10.,300.),('open','cover','sliver'),(0.,.009)))
    arm=[(z,w,f,c,p) for z,w,f,c,p in arm if z=='far' or c=='open']
    raw={}
    for site,w,far,occ,offset in arm:
        buf=g.render(raster.scene(site,w,occ),(offset,0),far)
        raw[site,w,far,occ,offset]=(*g.pick(buf,48,120),*g.pick(buf,160,120))
    queries=list(product(arm,(0,1)))
    dat=b''.join(pack('=ii8f',int(k[0]=='far'),keep,*raw[k]) for k,keep in queries)
    sense=run(['./sensor/frame'],input=dat,capture_output=True,check=True).stdout.decode().splitlines()
    assert len(sense)==len(queries)
    capframes={}
    for (k,keep),line in zip(queries,sense):
        site,w,far,occ,px=k
        keep_,raw_,stock=map(int,line.split())
        assert keep_==keep
        expect=w if (site=='near' or far==300. and (occ=='open' or occ=='sliver' and px==0.)) else -1
        assert raw_==expect and stock==(-1 if site=='far' and keep else expect)
        capframes[k,keep]=(raw_,stock)
    cs=radio.setups()
    scenarios=[];inp=[]
    for (k,keep),path,cap,o in product(queries,('scoped','stock'),(2,3),(-421,-411,-401)):
        site,w,far,occ,px=k
        raw_,stock=capframes[k,keep]
        clue=raw_ if path=='scoped' else stock
        q,last,*_=cs[site]
        q=radio.CEIL(q*1024);last=radio.FLOOR(last*1024)
        t=q if cap==3 else max(q,o+1025)
        frames=[(o+1024,'P','OK')]
        if clue>=0:frames.append((t+1024,'Q','F' if clue==1 else 'L'))
        inp.append(f'{cap} {len(frames)}')
        inp.extend(f'{u} {name} {val}' for u,name,val in frames)
        scenarios.append((k,keep,path,cap,o,t,last,clue,frames))
    out=run(['./sensor/radio/broker'],input='\n'.join(inp)+'\n',text=True,check=True,capture_output=True).stdout.splitlines()
    assert len(out)==len(scenarios)
    success={};paths={};counts={}
    for (k,keep,path,c,o,t,deadline,clue,frames),v in zip(scenarios,out):
        n,*got=v.split()
        site,w,far,cov,px=k
        assert int(n)==len(frames) and got==radio.broker_oracle(c,frames) and got[0]=='P:OK'
        timely=(len(got)==2 and got[-1]==('Q:F' if w else 'Q:L') and t<=deadline)
        assert timely==(clue==w and t<=deadline)
        if timely:
          if (site,w) not in paths:
            paths[site,w]=motion.verify(cs[site][2 if w else 3],'far' if w else 'late')
        good=bool(keep and timely)
        success[k,keep,path,c,o]=good
        counts[path]=counts.get(path,0)+good
    for w in (0,1):
      for c in (2,3):
       for o in (-421,-411,-401):
        assert not success[('far',w,300.,'open',0.),1,'stock',c,o]
        assert success[('far',w,300.,'open',0.),1,'scoped',c,o]==(c==3 or o==-421)
        assert not success[('far',w,300.,'cover',0.),1,'scoped',c,o]
        assert not success[('far',w,10.,'open',0.),1,'scoped',c,o]
    print(json.dumps({'raster_preconditions':len(arm),'source_stage_frames':len(queries),
      'joined_schedules':len(scenarios),'positive_with_old_depth':counts,
      'old_radio_success':len(scenarios),'validated_motion_extrema':sum(paths.values())},
       sort_keys=True,separators=(',',':')))
if __name__=='__main__':main()
