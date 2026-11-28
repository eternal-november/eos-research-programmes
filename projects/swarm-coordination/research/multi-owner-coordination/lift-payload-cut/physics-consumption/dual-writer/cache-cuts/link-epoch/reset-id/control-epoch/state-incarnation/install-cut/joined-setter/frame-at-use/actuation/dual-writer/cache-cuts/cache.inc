#include <mutex>
template<class T> bool CompareData(const T& a,const T& b){
 return a.x==b.x&&a.y==b.y&&a.z==b.z;
}
/*SET_BODY*/
struct UpdateInfo{};
using EntityComponentManager=ECS;
#define GZ_PROFILE(...) ((void)0)
namespace msgs{
struct Twist {
 math::Vector3d l,a;
 auto linear()const{return l;}
 auto angular()const{return a;}
};
auto Convert(math::Vector3d v){return v;}
}
struct VelocityControlPrivate {
 struct{ int id=2; int Entity()const{return id;} } model;
 std::mutex mutex;
 msgs::Twist targetVel{};
 math::Vector3d linearVelocity{},angularVelocity{};
 void UpdateVelocity(const UpdateInfo&, const EntityComponentManager&);
 void OnCmdVel(const msgs::Twist&);
};
/*POST_UPDATE_BODY*/
/*MESSAGE_BODY*/
struct ConfigureControl {
 VelocityControlPrivate cached;
 VelocityControlPrivate* dataPtr=&cached;
 void use(ECS& _ecm){ /*PRODUCER_BODY*/ }
};
struct Tr {
 ECS ecs;
 Lift lift;
 Physics phys;
 ConfigureControl robot;
 const Entity watched;
 explicit Tr(Entity id):watched(id) {
   robot.cached.model.id=watched;
   ecs.poses[1].value={{0,0,0},{}};
   ecs.poses[watched].value={{.25,0,0},{}};
   lift._initial_poses[1]=ecs.poses.at(1).value;
   lift._initial_aabbs[1]={{-1,-1,-1},{1,1,1}};
   phys.entityModelMap.bodies[watched]={};
   phys.topLevelModelMap[watched]=watched;
 }
 void publish(double horizontal){robot.cached.OnCmdVel({{horizontal,0,0},{}});}
 void latch(){robot.cached.UpdateVelocity({},ecs);}
 void cycle(){
   assert(!ecs.commands.contains(watched));
   robot.use(ecs);
   lift.write(ecs,1,.625);
   phys.consume9(ecs);
   cleanup9(ecs);
   assert(!ecs.commands.contains(watched));
 }
 auto x(){return phys.entityFreeGroupMap.calls.back().x;}
 auto z(){return phys.entityFreeGroupMap.calls.back().z;}
};
int main(){return 0;}
