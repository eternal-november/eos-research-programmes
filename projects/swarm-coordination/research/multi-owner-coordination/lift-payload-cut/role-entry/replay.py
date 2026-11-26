#!/usr/bin/env python3
"""Join the earlier selected native lift admission and physics dispatch cuts."""
import hashlib, subprocess, sys, tempfile
from pathlib import Path
u=Path(sys.argv[1]).resolve()
here=Path(__file__).resolve().parent
refs=Path(sys.argv[2]).resolve() if len(sys.argv)>2 else here.parent
def snippet(s,key,end):
    i=s.index(key)
    return s[i:s.index(end,i)+len(end)]
b=(u/'Physics9.cc').read_bytes()
assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()=='9207f9d48a8b725293fb6e276a2b899ae6de4240'
p=b.decode()
consume=snippet(p,'_ecm.Each<components::Model, components::LinearVelocityCmd>(', '\n      });')
cleanup=snippet(p,'std::vector<Entity> entitiesLinearVelocityCmd;', '\n    }\n  }').removesuffix('\n  }')
f=(refs/'standins.inc').read_text()
def patch(old,new):
    global f
    assert f.count(old)==1,old
    f=f.replace(old,new)
patch('bool operator==(const Vector3d&) const = default;', '''bool operator==(const Vector3d&) const = default;
  static const Vector3d Zero;
  double& operator[](int d){assert(d==2);return z;}''')
patch('Vector3d operator+(Vector3d p,Vector3d q)', '''const Vector3d Vector3d::Zero{};
namespace eigen3 { Vector3d convert(Vector3d v){return v;} }
struct Rotation { Vector3d operator*(Vector3d v)const{return v;} };
Vector3d operator+(Vector3d p,Vector3d q)''')
patch('auto Pos() const {return p;}','auto Pos() const {return p;}\n  gz::math::Rotation Rot() const {return {};}')
patch('struct LinearVelocityCmd : Box<std::vector<double>>','struct LinearVelocityCmd : Box<gz::math::Vector3d>')
patch('  for (const auto& [e,p]:poses) assert(f(e,&model,&p));','''  if constexpr(std::is_same_v<P,components::Pose>){
      for (const auto& [e,p]:poses) assert(f(e,&model,&p));
    }else{
      for (const auto& [e,v]:vels) assert(f(e,&model,&v));
    }''')
patch('  bool EntityHasComponentType(','''  template<class T,class Fn> void Each(Fn fn){
    static_assert(std::is_same_v<T,components::LinearVelocityCmd>);
    for(auto&[e,v]:vels)assert(fn(e,&v));
  }
  template<class T> void RemoveComponent(Entity e){
    static_assert(std::is_same_v<T,components::LinearVelocityCmd>);
    vels.erase(e);
  }
  bool EntityHasComponentType(''')
with tempfile.TemporaryDirectory() as d:
    d=Path(d)
    (d/'replay.py').write_bytes((refs/'replay.py').read_bytes())
    (d/'standins.inc').write_text(f)
    (d/'tests.inc').write_text((here/'join.inc').read_text()
      .replace('/*PHYSICS_BODY*/',consume).replace('/*CLEANUP_BODY*/',cleanup))
    subprocess.run([sys.executable,'-B',d/'replay.py',u],check=True)
