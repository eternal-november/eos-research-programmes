#include <algorithm>
#include <array>
#include <cassert>
#include <cmath>
#include <iostream>
#include <limits>
#include <map>
#include <type_traits>
using Entity=int;
#define GZ_PROFILE(...) ((void)0)
namespace math {
struct Vector3d{double x{},y{},z{};};
Vector3d operator-(Vector3d a,Vector3d b){return{a.x-b.x,a.y-b.y,a.z-b.z};}
Vector3d operator*(double k,Vector3d a){return{k*a.x,k*a.y,k*a.z};}
}
struct UpdateInfo{};
namespace components{
template<class T>struct C{T val{};const T& Data()const{return val;}};
struct Link{};
struct Inertial {
    double mass=1;
    const Inertial& Data()const{return *this;}
    const Inertial& MassMatrix()const{return *this;}
    double Mass()const{return mass;}
};
struct WindMode : C<bool>{};
struct Pose{math::Vector3d p;math::Vector3d Pos()const{return p;}};
struct WorldPose : C<Pose>{};
struct WorldLinearVelocity : C<math::Vector3d>{};
}
struct Body{
 components::Link link;
 components::Inertial mass;
 components::WindMode enabled{true};
 components::WorldPose pose;
 components::WorldLinearVelocity velocity;
};
struct EntityComponentManager{
 components::WorldLinearVelocity common{};
 bool source=true;
 std::map<Entity,Body> bodies;
 std::map<Entity,math::Vector3d> applied;
 template<class T> T* Component(Entity e){assert(e==0);return source?&common:nullptr;}
 template<class... T,class F> void Each(F f){
   static_assert(sizeof...(T)==5);
   for(auto&[e,b]:bodies)assert(f(e,&b.link,&b.mass,&b.enabled,&b.pose,&b.velocity));
 }
};
struct Link{
 Entity e{};
 void ResetEntity(Entity n){e=n;}
 void AddWorldForce(EntityComponentManager& a,math::Vector3d f){a.applied[e]=f;}
};
struct WindEffectsPrivate{
 Entity windEntity=0;
 double forceApproximationScalingFactor(math::Vector3d p){
    if(p.x==99)return std::numeric_limits<double>::quiet_NaN();
    return p.x;
 }
 void ApplyWindForce(const UpdateInfo&,EntityComponentManager&);
};
