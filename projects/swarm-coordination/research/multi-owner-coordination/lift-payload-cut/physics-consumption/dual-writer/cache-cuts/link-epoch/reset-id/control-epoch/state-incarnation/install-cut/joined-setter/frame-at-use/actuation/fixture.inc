#include <cassert>
#include <iostream>
#include <map>
#include <sstream>
#include <type_traits>
#include <vector>
using Entity=int;
static std::ostringstream gzerr,gzdbg;
namespace gz::math {
struct Vector3d {
  double x{},y{},z{};
  static const Vector3d Zero;
  double& operator[](int i){assert(i==2);return z;}
};
const Vector3d Vector3d::Zero{};
Vector3d operator+(Vector3d a,Vector3d b){return{a.x+b.x,a.y+b.y,a.z+b.z};}
Vector3d operator-(Vector3d a,Vector3d b){return{a.x-b.x,a.y-b.y,a.z-b.z};}
struct AxisAlignedBox {
  Vector3d l,r;
  bool Contains(Vector3d p)const{return l.x<=p.x&&p.x<=r.x&&l.y<=p.y&&p.y<=r.y&&l.z<=p.z&&p.z<=r.z;}
  AxisAlignedBox operator+(Vector3d s)const{return{l+s,r+s};}
};
struct Rotation {
  int pitch=0,yaw=0;
  std::array<int,3> up()const {return {-3*pitch,0,pitch?4:5};}
  Vector3d operator*(Vector3d v)const {
    double c=pitch?.8:1.,s=.6*pitch;
    const Vector3d w{c*v.x+s*v.z,v.y,-s*v.x+c*v.z};
    return yaw?Vector3d{-w.y,w.x,w.z}:w;
  }
  bool operator==(const Rotation&) const=default;
};
namespace eigen3 { Vector3d convert(Vector3d v){return v;} }
}
namespace math=gz::math;
struct Datum {
  math::Vector3d pos;
  math::Rotation rot;
  auto Pos()const{return pos;}
  auto Rot()const{return rot;}
  auto CoordPositionSub(Datum b)const{return pos-b.pos;}
};
namespace components {
struct Model {};
struct Pose {Datum value{}; const Datum& Data()const{return value;}};
struct LinearVelocityCmd {
  math::Vector3d v{};
  auto& Data(){return v;}
  const auto& Data()const{return v;}
  int TypeId()const{return 1;}
};
}
struct ECS {
  std::map<Entity,components::Pose> poses;
  std::map<Entity,components::LinearVelocityCmd> commands;
  components::Model model;
  template<class T> auto* Component(Entity e){
    if constexpr(std::is_same_v<T,components::Pose>)return &poses.at(e);
    else return &commands.at(e);
  }
  template<class... T,class F> void Each(F f){
    if constexpr(sizeof...(T)==1){for(auto& [e,c]:commands)assert(f(e,&c));}
    else if constexpr((std::is_same_v<T,components::Pose>||...)){
      for(auto& [e,p]:poses)assert(f(e,&model,&p));
    }else{for(auto& [e,c]:commands)assert(f(e,&model,&c));}
  }
  bool EntityHasComponentType(Entity e,int id)const{assert(id==1);return commands.contains(e);}
  template<class T> void RemoveComponent(Entity e){static_assert(std::is_same_v<T,components::LinearVelocityCmd>); commands.erase(e);}
};
using EntityComponentManager=ECS;
struct Lift {
  std::map<Entity,Datum> _initial_poses;
  std::map<Entity,math::AxisAlignedBox> _initial_aabbs;
  std::vector<Entity> get_payloads(ECS&,const Entity&);
  void write(ECS&,const Entity&,double);
};
struct WorldVelocityCommandFeatureList {};
struct Body {
  bool free=true;
  Body* FindFreeGroup(){return free?this:nullptr;}
};
struct Physics {
  struct {
    std::map<Entity,Body> bodies;
    Body* Get(Entity e){auto p=bodies.find(e);return p==bodies.end()?nullptr:&p->second;}
  } entityModelMap;
  std::map<Entity,Entity> topLevelModelMap;
  struct Group {
    bool feature=true;
    std::vector<math::Vector3d> calls;
    void AddEntity(Entity,Body*){}
    template<class T> Group* EntityCast(Entity){return feature?this:nullptr;}
    void SetWorldLinearVelocity(math::Vector3d v){calls.push_back(v);}
  } entityFreeGroupMap;
  void consume8(ECS&);
  void consume9(ECS&);
};
