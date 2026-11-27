"""Rendered wavelength proxy recovers a named cue on the robot side of a cut RF link."""
from itertools import product
from struct import pack
from pathlib import Path
from fractions import Fraction as F
from subprocess import run
from math import isfinite
import sys,json

root=Path.cwd()
sys.path.insert(0,str(root))
sys.path.insert(0,str(root/'sensor/radio'))
sys.path.insert(0,str(root/'optical/rware'))
from same_queue import start,move,A
import material
from egl_depth import inputs,context
import joined as radio
import motion as m

def dispatch():
    outputs={}
    # Native runner with one actual delivery. An authored mapping assigns
    # the two source dispatch outcomes to the two inspection worlds.
    for seed in (14,9):
        w=start(2,seed)
        _,r=move(w,b=A.FORWARD)
        mark,=w.request_queue
        assert r==[0.0,.5,0.0]
        outputs[mark.id-1]=w._cur_steps
    assert outputs=={0:1,1:1}
    return outputs

def main():
    graphs=dispatch()
    s=inputs();context();r=material.ColorRender(s)
    scene_set=list(product(graphs,('right','none','wrong'), (300.,10.),('open','cover')))
    stages={}
    for w,mode,far,occluded in scene_set:
        frame=r.render_flags(material.scene(w,mode,occluded),(0.,0.),far)
        stages[w,mode,far,occluded]=(*r.pick(frame,48,120),*r.pick(frame,160,120))
    cases=list(product(scene_set,(0,1),(0,1)))
    payload=b''.join(pack('=ii8f',point,old,*stages[k]) for k,point,old in cases)
    rows=run(['./sensor/color-frame'],input=payload,capture_output=True,check=True).stdout.decode().splitlines()
    assert len(rows)==len(cases)
    picked={}
    for (k,point,old),line in zip(cases,rows):
        w,mode,far,occlusion=k
        dep,raw,pts,finite,red,green=map(int,line.split())
        assert dep==old and pts==point
        qualified=(occlusion=='open' and far==300 and mode!='none')
        expected=(-1 if not qualified else w if mode=='right' else 1-w)
        assert raw==expected,(k,point,old,line,expected)
        # Even with nonfinite XYZ, the fixed source RGB branch returns
        # the target color. No geometric clearance follows from it.
        assert finite==int(bool(point and (occlusion=='cover' or far==300 and not old)))
        picked[k,point,old]=(raw,bool(finite))
    config=radio.setups()['far']
    q,last,*_=config
    cutoff=radio.FLOOR(last*1024);first=radio.CEIL(q*1024)
    # Two explicit modeled processing delays for receiving the qualified
    # RGB observation locally; no Q packet for optical-only action.
    lag=[F(105,1000),F(125,1000)]
    assert lag[0]+q<last<lag[1]+q
    schedule=[];inp=[]
    for (k,point,old),path,i,pause,c,o in product(cases,('rf','local','finite-first','blind'),(0,1),(0,1),(2,3),(-421,-411)):
        w,mode,far,cover=k
        raw,finite=picked[k,point,old]
        # Retain image service when required; coalesced history and
        # emitter identity are modeled by an as-of qualification.
        t=first if c==3 else max(first,o+1025)
        messages=[(o+1024,'P','OK')]
        if path=='rf':messages.append((t+1024,'Q','F' if w else 'L'))
        inp.append(f'{c} {len(messages)} {pause}')
        inp.extend(f'{j} {z} {data}' for j,z,data in messages)
        schedule.append((w,mode,old,path,i,pause,c,o,t,raw,finite,messages))
    pipe=run(['./sensor/radio/rf-cut'],input='\n'.join(inp)+'\n',text=True,check=True,capture_output=True).stdout.splitlines()
    assert len(pipe)==len(schedule)
    counts={z:0 for z in ('rf','local','finite-first','blind')}
    wrong=0
    restores_without_radio=0
    paths={}
    for (w,mode,old,path,i,pause,c,o,t,raw,finite,msg),line in zip(schedule,pipe):
        n,*out=line.split()
        assert int(n)==len(msg) and out[0]=='P:OK'
        if path=='rf':
            oracle=radio.broker_oracle(c,msg)
            if pause:oracle[-1]='-'
            assert out==oracle
            hit=(w if len(out)==2 and out[-1]==('Q:F' if w else 'Q:L') and t<=cutoff else -1)
        elif raw>=0 and i==0 and (path=='blind' or mode=='right' and (path=='local' or finite)):
            hit=raw
        else:hit=-1
        assert not (path=='rf' and pause and hit>=0)
        assert not (path=='finite-first' and old and hit>=0)
        if path=='blind' and hit>=0 and hit!=w:
            wrong+=1
            z=m.at(config[2 if hit else 3],2)[0]
            assert (z<m.H-1) if w else (z>4)
        if hit==w:
            if w not in paths:
                paths[w]=m.verify(config[2 if w else 3],'far' if w else 'late')
            if old:counts[path]+=1
            if old and pause and path=='local':restores_without_radio+=1
    assert restores_without_radio and wrong and counts['finite-first']==0
    print(json.dumps({'dispatches_from_native_rware':len(graphs),'rendered_scenes':len(scene_set),
      'native_rgb_cases':len(cases),'joined_cases':len(schedule),'old_radio_delivered':len(schedule),
      'service_with_old_depth':counts,'new_rf_absent_optical_service':restores_without_radio,
      'timely_wrong_unbound_rgb':wrong,'verified_motion_checks':sum(paths.values())},
      sort_keys=True,separators=(',',':')))
if __name__=='__main__': main()
