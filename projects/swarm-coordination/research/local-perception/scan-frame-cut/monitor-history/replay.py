#!/usr/bin/env python3
"""Exact families of hysteresis histories under one shared scalar shift per epoch."""
from bisect import bisect_left
from fractions import Fraction
from itertools import product
from pathlib import Path
from random import Random
import json,hashlib,subprocess,sys,tempfile

def stamp(state,hit,h,r):
    on,i,j=state
    if h==r==1:
        return hit,0,0
    if hit:
        i=min(i+1,h)
        return on or i==h, i,0
    j=min(j+1,r)
    return on and j<r,0,j

def count(points,z):
    # The actual selected ray test on [0,1] x [0,1], in sixteenths.
    return sum(0<=x+z<16 and 0<y<=16 for x,y in points)

def cuts(points,lo,hi):
    return {x for p,y in points if 0<y<=16 for x in (-p,16-p)
            if lo<=x<=hi}

class Online:
    def __init__(self,lo,hi,states,m,h,r):
        assert lo<=hi
        self.params=m,h,r
        self.keys=sorted({lo,hi})
        self.states=[frozenset(states)]*(2*len(self.keys)-1)
    def idx(self,x):
        i=bisect_left(self.keys,x)
        if i<len(self.keys) and self.keys[i]==x: return 2*i
        assert 0<i<len(self.keys)
        return 2*i-1
    def vals(self):
        return set().union(*self.states)
    def advance(self,points):
        m,h,r=self.params
        lo,hi=self.keys[0],self.keys[-1]
        keys=sorted(set(self.keys)|cuts(points,lo,hi))
        zs=representatives(keys)
        vals=[frozenset(stamp(s,count(points,z)>=m,h,r)
                        for s in self.states[self.idx(z)]) for z in zs]
        # Compact an internal boundary only if point and both open cells agree.
        keep=[i for i in range(len(keys)) if i==0 or i==len(keys)-1
              or not vals[2*i-1]==vals[2*i]==vals[2*i+1]]
        keepkeys=[keys[i] for i in keep]
        self.keys=keys;self.states=vals
        self.states=[vals[self.idx(z)] for z in representatives(keepkeys)]
        self.keys=keepkeys
    def bounded_rebase(self,lo,hi,dlo,dhi):
        assert lo<=hi and dlo<=dhi
        src=self.keys
        bands=[]
        for i,x in enumerate(src):
            bands.append((x+dlo,x+dhi,True,self.states[2*i]))
            if i:
                bands.append((src[i-1]+dlo,x+dhi,False,self.states[2*i-1]))
        keys=sorted({lo,hi}|{x for a,b,_,_ in bands for x in (a,b) if lo<=x<=hi})
        def contains(v,a,b,closed):
            return a<=v<=b if closed else a<v<b
        self.keys=keys
        self.states=[frozenset(s for a,b,cl,states in bands if contains(v,a,b,cl)
                               for s in states) for v in representatives(keys)]
    def new_epoch(self,lo,hi):
        # Full product is justified only if all old--new pairs are legal.
        self.__init__(lo,hi,self.vals(),*self.params)


def representatives(ends):
    r=[]
    for i,e in enumerate(ends):
        if i: r.append(Fraction(e+ends[i-1],2))
        r.append(e)
    return r

def brute(frames,lo,hi,init,m,h,r):
    # Offline oracle: never uses the incremental partition or merging.
    out=[set() for _ in frames]
    es=sorted({lo,hi}|set().union(*(cuts(p,lo,hi) for p in frames)))
    ordinates=representatives(es)
    for s,z in product(init,ordinates):
        for i,f in enumerate(frames):
            s=stamp(s,count(f,z)>=m,h,r)
            out[i].add(s)
    return out

def seq(initial,h,r,zs,pts,m=1):
    s=initial; rows=[]
    for z,ps in zip(zs,pts):
        total=count(ps,z)
        s=stamp(s,total>=m,h,r)
        row=[z,len(ps),total,*map(int,s),*[i for p in ps for i in p]]
        rows.append(' '.join(map(str,row)))
    return rows

def study():
    ex=[[( -12,8)],[(28,8)]]
    assert all(any(count(f,z) for z in range(-16,17)) for f in ex)
    o=Online(-16,16,{(False,0,0)},1,2,1)
    o.advance(ex[0]);o.advance(ex[1])
    assert all(not s[0] for s in o.vals())
    o=Online(-16,16,{(False,0,0)},1,2,1)
    o.advance(ex[0]);o.new_epoch(-16,16);o.advance(ex[1])
    assert any(s[0] for s in o.vals())
    near=[[(4,8)],[(12,8)]]
    assert all(any(not count(f,z) for z in range(-8,9)) for f in near)
    o=Online(-8,8,{(True,0,0)},1,1,2)
    for f in near:o.advance(f)
    assert all(s[0] for s in o.vals())
    o=Online(-8,8,{(True,0,0)},1,1,2)
    o.advance(near[0]);o.new_epoch(-8,8);o.advance(near[1])
    assert any(not s[0] for s in o.vals())

    for frames,lo,hi,initial,h,r,cut in [
        (ex,-16,16,(False,0,0),2,1,24),
        (near,-8,8,(True,0,0),1,2,8)]:
        for d in (Fraction(cut),Fraction(cut)+Fraction(1,2)):
            p=Online(lo,hi,{initial},1,h,r)
            p.advance(frames[0])
            p.bounded_rebase(lo,hi,-d,d)
            p.advance(frames[1])
            assert any(s[0]!=initial[0] for s in p.vals())==(d>cut)

    # Exact independent two-frame oracle: for cells in the current support,
    # intersect the preimage interval with each original singleton/open cell.
    pp=Random(754)
    for _ in range(400):
        lo,hi=sorted([pp.randrange(-16,17),pp.randrange(-16,17)])
        left,right=sorted([pp.randrange(-21,22),pp.randrange(-21,22)])
        dlo,dhi=sorted([pp.randrange(-16,17),pp.randrange(-16,17)])
        ff=[[(pp.randrange(-16,33),8) for _ in range(pp.randrange(1,8))]
             for _ in ('old','new')]
        m,h,r=pp.randrange(1,5),pp.randrange(1,5),pp.randrange(1,5)
        initial=(False,0,0)
        o=Online(lo,hi,{initial},m,h,r)
        o.advance(ff[0]);o.bounded_rebase(left,right,dlo,dhi);o.advance(ff[1])
        old=sorted({lo,hi}|cuts(ff[0],lo,hi))
        targets=set(o.keys)
        targets.update(x+d for x in old for d in (dlo,dhi) if left<=x+d<=right)
        for z in representatives(sorted(targets)):
            states=set()
            for i,p in enumerate(old):
                if z-dhi<=p<=z-dlo:
                    states.add(stamp(initial,count(ff[0],p)>=m,h,r))
                if i and z-dhi<p and z-dlo>old[i-1]:
                    states.add(stamp(initial,count(ff[0],Fraction(old[i-1]+p,2))>=m,h,r))
            wanted={stamp(s,count(ff[1],z)>=m,h,r) for s in states}
            assert wanted==o.states[o.idx(z)]

    vectors=["1 2 1 0 0 0 2\n"+'\n'.join(seq((False,0,0),2,1,[16,-16],ex)),
             "1 1 2 1 0 0 2\n"+'\n'.join(seq((True,0,0),1,2,[-8,8],near))]
    R=Random(538)
    tested=histories=0
    for i in range(240):
        lo,hi=sorted((R.randrange(-16,17),R.randrange(-16,17)))
        m,h,r=R.randrange(1,5),R.randrange(1,5),R.randrange(1,5)
        s=(bool(R.randrange(2)),0,0)
        init={s}
        o=Online(lo,hi,init,m,h,r)
        allrows=[]
        running=s
        for epoch in range(2):
            frames=[[(R.randrange(-16,33),R.choice((-1,0,1,8,16,17)))
                     for _ in range(R.randrange(1,18))] for _ in range(R.randrange(1,10))]
            oracle=brute(frames,lo,hi,init,m,h,r)
            for j,(f,expected) in enumerate(zip(frames,oracle)):
                o.advance(f)
                assert o.vals()==expected
                # Check relation itself, not only marginal output/counters.
                es=sorted({lo,hi}|set().union(*(cuts(p,lo,hi) for p in frames)))
                for z in representatives(es):
                    seen=init.copy()
                    for earlier in frames[:j+1]:
                        seen={stamp(ss,count(earlier,z)>=m,h,r) for ss in seen}
                    assert seen==o.states[o.idx(z)]
                tested+=1
            init=o.vals()
            o.new_epoch(lo,hi)
            z=R.randint(lo,hi)
            k=len(frames)
            allrows.extend(seq(running,h,r,[z]*k,frames,m))
            for f in frames:
                running=stamp(running,count(f,z)>=m,h,r)
            histories+=k
        vectors.append(f"{m} {h} {r} {int(s[0])} {s[1]} {s[2]} {len(allrows)}\n"+
                       '\n'.join(allrows))
    return vectors, dict(online_cut_checks=tested,native_frame_comparisons=histories+4,
        bounded_rebase_relation_checks=400,trigger_displacement_strictly_above="3/2",
        release_displacement_strictly_above="1/2",
        trigger_impossible_in_first_epoch=True,release_impossible_in_first_epoch=True,
        independent_epoch_change_can_reverse_both=True)

def native(up,vectors):
    here=Path(__file__).resolve().parent
    def src(name,sha):
        b=(up/name).read_bytes()
        assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==sha,name
        return b.decode()
    def get(s,needle):
        i=s.index(needle)
        return s[i:s.index('\n}',i)+2]
    g=src('geometry_utils.hpp','3869fbb9c4916e42d196c74cf74baf992f37a11c')
    p=src('polygon.cpp','5d6fcde164621b97798d3bf44de836674b8b389c')
    methods='\n'.join(get(p,z) for z in (
        'int Polygon::getPointsInside(\n  const std::vector<Point> & points,\n  std::vector<Point> &',
        'bool Polygon::isTriggeredInternal('))
    with tempfile.TemporaryDirectory() as d:
        d=Path(d)
        (d/'t.cc').write_text((here/'harness.inc').read_text()+
         '\nnamespace nav2_util::geometry_utils {\n'+get(g,'template<class PointT>\ninline bool isPointInsidePolygon(')+
         '\n}\nnamespace nav2_collision_monitor {\n'+methods+
         '\n}\n'+(here/'tests.inc').read_text())
        subprocess.run(['c++','-std=c++20','-Werror','-Wall','-Wextra','-o',d/'t',d/'t.cc'],check=True)
        out=subprocess.run([d/'t'],input=str(len(vectors))+'\n'+'\n'.join(vectors),
                          text=True,capture_output=True,check=True)
        assert out.stdout=='native finite sequences match\n'
if __name__=='__main__':
    vectors,result=study()
    native(Path(sys.argv[1]),vectors)
    print(json.dumps(result,indent=2,sort_keys=True))
