#include <cassert>
#include <chrono>
#include <iostream>
#include <map>
#include <mutex>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <type_traits>
#include <vector>
using Entity=int;
constexpr Entity kNullEntity=0;
static std::ostringstream gzerr,gzdbg,gzwarn;
#define GZ_PROFILE(...) ((void)0)
namespace math {
struct Vector3d {
  double x{},y{},z{};
  bool operator==(const Vector3d&) const = default;
};
struct Rot {
  int q=0;
  Vector3d operator*(Vector3d a) const {
    for(int k=0;k<q;++k) a={-a.y,a.x,a.z};
    return a;
  }
  Rot operator*(Rot b) const{return {(q+b.q)%4};}
};
struct Pose3d {
  math::Rot r{};
  auto Rot() const{return r;}
  Pose3d operator*(Pose3d b)const{return {r*b.r};}
};
namespace eigen3 {inline Vector3d convert(Vector3d x){return x;}}
}
namespace components {
struct Model {};
struct Link {};
struct Pose {math::Pose3d value{}; const auto& Data()const{return value;}};
struct ParentEntity {Entity value; Entity Data()const{return value;}};
struct Name {std::string value;};
template<int K> struct Cmd {
  using Type=math::Vector3d;
  Type value{};
  const Type& Data()const{return value;}
  template<class C> bool SetData(const Type& v,C equal){
    if(equal(value,v))return false;
    value=v;return true;
  }
};
using LinearVelocityCmd=Cmd<0>;using AngularVelocityCmd=Cmd<1>;
}
template<class T> bool CompareData(const T& a,const T& b){return a==b;}
struct EntityComponentManager {
  std::set<Entity> models,linkIds;
  std::map<Entity, std::string> names;
  std::map<Entity, components::ParentEntity> parents;
  std::map<Entity, components::Pose> poses;
  std::map<Entity, components::LinearVelocityCmd> linear;
  std::map<Entity, components::AngularVelocityCmd> angular;
  mutable int resolves=0;
  int missingCreates=0;
  bool HasEntity(Entity e)const{return poses.contains(e);}
  template<class T> static auto* get(const std::map<Entity,T>& m,Entity e){
    auto it=m.find(e);return it==m.end()?nullptr:&it->second;
  }
  template<class T> const T* Component(Entity e)const {
    if constexpr(std::is_same_v<T,components::ParentEntity>)return get(parents,e);
    if constexpr(std::is_same_v<T,components::Pose>)return get(poses,e);
    if constexpr(std::is_same_v<T,components::Model>){static const T value{};return models.contains(e)?&value:nullptr;}
    if constexpr(std::is_same_v<T,components::LinearVelocityCmd>)return get(linear,e);
    if constexpr(std::is_same_v<T,components::AngularVelocityCmd>)return get(angular,e);
  }
  template<class T> T* Component(Entity e){return const_cast<T*>(static_cast<const EntityComponentManager&>(*this).Component<T>(e));}
  template<class T> void CreateComponent(Entity e,T d){
    // Abstract storage around the inspected native missing-entity guard.
    if(!HasEntity(e)){++missingCreates;return;}
    if constexpr(std::is_same_v<T,components::LinearVelocityCmd>)linear.emplace(e,d);
    else angular.emplace(e,d);
  }
  Entity EntityByComponents(components::ParentEntity p,components::Name n,components::Link)const{
    ++resolves;
    for(Entity e:linkIds)if(parents.at(e).value==p.value&&names.at(e)==n.value)return e;
    return kNullEntity;
  }
  template<class T,class U,class F> void Each(F f) {
    static const T label{};
    for (auto& [e,c]:linear) {
      bool has=std::is_same_v<T,components::Link>?linkIds.contains(e):models.contains(e);
      if(has)assert(f(e,&label,&c));
    }
  }
  template<class ComponentTypeT> bool SetComponentData(Entity,const typename ComponentTypeT::Type&);
};
/*S*/
struct Model {
  struct Id{int id=2;} at;
  Id* dataPtr=&at;
  ::Entity Entity()const{return at.id;}
  std::string Name(const EntityComponentManager&)const{return "carrier";}
  ::Entity LinkByName(const EntityComponentManager&,const std::string&)const;
};
/*M*/
/*T*/
namespace transport {struct MessageInfo {std::string topic;auto Topic()const{return topic;}};}
namespace msgs {
struct Twist {
  math::Vector3d l,a;
  auto linear()const{return l;}
  auto angular()const{return a;}
};
auto Convert(math::Vector3d v){return v;}
}
struct UpdateInfo {bool paused=false;std::chrono::steady_clock::duration dt{};};
struct VelocityControlPrivate {
  Model model;
  std::mutex mutex;
  math::Vector3d linearVelocity{},angularVelocity{};
  const std::vector<std::string> linkNames{"shoe","port"};
  std::map<std::string,Entity> links;
  std::map<std::string,msgs::Twist> linkVels;
  std::map<std::string,math::Vector3d> linearVelocities,angularVelocities;
  void UpdateLinkVelocity(const UpdateInfo&,const EntityComponentManager&);
  void OnLinkCmdVel(const msgs::Twist&,const transport::MessageInfo&);
};
struct VelocityControl {VelocityControlPrivate p;VelocityControlPrivate* dataPtr=&p;
 void PreUpdate(const UpdateInfo&,EntityComponentManager&);
};
/*P*/
/*L*/
struct WorldVelocityCommandFeatureList {};
struct Body {bool free=true;Body* FindFreeGroup(){return free?this:nullptr;}};
struct PhysicsPrivate {
  struct Bodies {
    std::map<Entity,Body> refs;
    bool HasEntity(Entity e)const{return refs.contains(e);}
    Body* Get(Entity e){auto p=refs.find(e);return p==refs.end()?nullptr:&p->second;}
  } entityModelMap,entityLinkMap;
  std::map<Entity,Entity> topLevelModelMap;
  struct Call {Entity id; math::Vector3d v;};
  struct Features{
    std::vector<Call> calls;
    std::set<Entity> refused;
    Entity current{};
    void AddEntity(Entity e,Body*){current=e;}
    template<class T> Features* EntityCast(Entity e){assert(e==current);return refused.contains(e)?nullptr:this;}
    void SetWorldLinearVelocity(math::Vector3d v){calls.push_back({current,v});}
  } entityFreeGroupMap;
  math::Pose3d RelativePose(const Entity&,const Entity&,const EntityComponentManager&)const;
  void consume(EntityComponentManager& _ecm){/*C*/}
};
/*R*/
/*TESTS*/
