"""Nominal pinned sensor gate plus a physically paid stationary wait."""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha1
from tempfile import TemporaryDirectory
from subprocess import run
from itertools import product
from math import isqrt
from xml.etree import ElementTree as XML
import json
import sys
P=Path(__file__).resolve().parent
sys.path.insert(0,str(Path.cwd()/'sensor/radio'))
import motion as m

def read():
    c={}
    for line in (P/'INPUTS.tsv').read_text().splitlines():
        n,_,_,_,h=line.split('\t');b=(P/n).read_bytes()
        assert sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==h
        c[n]=b.decode()
    xml=XML.fromstring(c['camera.sdf'])
    assert int(xml.findtext(".//sensor[@name='camera_front']/update_rate"))==20
    s=c['Sensor.cc'];start=s.index('bool Sensor::Update(const gz::common::Time &_now,')
    return s[start:s.index('\n}',start)+2]

def physical(epsilon,processing):
    remain=m.DELTA-epsilon
    return remain>=0 and (processing<=F(1,10) or m.A*(processing-F(1,10))**2<=remain)

def witness(eps):
    q=m.S-F(3,20)+eps
    target=(m.DELTA-eps)/m.A
    ell=10**12
    low=isqrt((target.numerator*ell**2)//target.denominator)
    brk=F(low,ell)
    assert brk*brk<=target<F(low+1,ell)**2
    pref=[(F(1,10),-m.A),(F(1,5),m.A),(q,0),(q+F(1,10),m.A),(q+F(1,10)+brk,-m.A)]
    far=m.trace(pref+[(q+F(1,10)+2*brk,m.A),(2,0)])
    late=m.trace(pref+[(q+F(1,5),-m.A),(2,0)])
    assert m.at(late,2)==(4,0)
    assert m.at(far,2)[0]>=m.H-1 and m.at(far,q)==(F(39,10),0)
    return m.verify(far,'far')+m.verify(late,'late')

def main():
    got=[]
    cases=list(product(range(0,50_000_000,50_000),(0,1)))
    with TemporaryDirectory() as d:
        d=Path(d)
        (d/'native.inc').write_text(read())
        (d/'rate.cc').write_bytes((P/'rate.cc').read_bytes())
        run(['c++','-std=c++17','-Wall','-Wextra','-Werror','rate.cc','-o','gate'],cwd=d,check=True)
        got=run([str(d/'gate')],cwd=d,text=True,capture_output=True,check=True,
                input=''.join(f'{p} {z}\n' for p,z in cases)).stdout.splitlines()
    assert len(got)==len(cases)
    counts={}
    motion_checks=sum(witness(e) for e in (F(0),F(1,1000),F(18,10000),F(2,1000),m.DELTA))
    for (phase,force),r in zip(cases,got):
        cap,nxt=map(int,r.split())
        assert cap==(0 if force else phase)
        assert nxt==phase+(0 if force else 50_000_000)
        e=F(cap,10**9)
        for lag in (F(0),F(1,10),F(105,1000),F(115,1000),F(125,1000)):
            k=f'force={force};delay={lag}'
            counts[k]=counts.get(k,0)+physical(e,lag)
    assert counts['force=0;delay=0']==42 and counts['force=0;delay=21/200']==37
    assert counts['force=1;delay=21/200']==1000 and counts['force=1;delay=1/8']==0
    # Counterexample to replacing capture time shift by transport delay.
    # At p=.1 it is earlier inability to leave at enough speed, not
    # just the old global receipt stopwatch, that rules out this arm.
    assert not physical(F(3,1000),F(0))
    print(json.dumps(dict(timing_checks=len(cases),count_by_phase=counts,angle_path_checks=motion_checks,
      max_station_wait=float(m.DELTA),max_wait_with_105ms_decode=float(m.DELTA-F(1,4000)),
      planned_sensor_rate=20),sort_keys=True,separators=(',',':')))
if __name__=='__main__':main()
