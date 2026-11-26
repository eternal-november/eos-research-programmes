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
 struct{ int Entity()const{return 2;} } model;
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
 Tr() {
   ecs.poses[1].value={{0,0,0},{}};
   ecs.poses[2].value={{.25,0,0},{}};
   lift._initial_poses[1]=ecs.poses.at(1).value;
   lift._initial_aabbs[1]={{-1,-1,-1},{1,1,1}};
   phys.entityModelMap.bodies[2]={};
   phys.topLevelModelMap[2]=2;
 }
 void publish(double horizontal){robot.cached.OnCmdVel({{horizontal,0,0},{}});}
 void latch(){robot.cached.UpdateVelocity({},ecs);}
 void cycle(){
   assert(!ecs.commands.contains(2));
   robot.use(ecs);
   lift.write(ecs,1,.625);
   phys.consume9(ecs);
   cleanup9(ecs);
   assert(!ecs.commands.contains(2));
 }
 auto x(){return phys.entityFreeGroupMap.calls.back().x;}
 auto z(){return phys.entityFreeGroupMap.calls.back().z;}
};
int main(){
  Tr silent;
  silent.publish(1);silent.latch();silent.cycle();
  assert(silent.x()==1&&silent.z()==.625);
  for(int k=0;k<4;k++){
    silent.latch();silent.cycle();
    assert(silent.x()==1&&silent.z()==.625);
  }
  Tr before,after;
  before.publish(1);after.publish(1);
  before.publish(0);before.latch();
  after.latch();after.publish(0);
  assert(before.robot.cached.targetVel.l.x==after.robot.cached.targetVel.l.x);
  before.cycle();after.cycle();
  assert(before.x()==0&&after.x()==1&&before.z()==after.z());
  after.latch();after.cycle();
  assert(after.x()==0&&after.z()==.625);
  Tr snapshot_only;
  snapshot_only.publish(1);snapshot_only.latch();
  snapshot_only.robot.cached.linearVelocity={}; // authored reset of sampled copy only
  snapshot_only.cycle();assert(snapshot_only.x()==0);
  snapshot_only.latch();snapshot_only.cycle();assert(snapshot_only.x()==1);
  std::cout<<"silence and repeated component cleanup: selected writer still recreates prior intent\n"
           <<"same zero mailbox at use: before versus after latch changes one setter cut\n"
           <<"selected native relatch takes the zero on the next cut\n"
           <<"authored snapshot-only reset: next relatch restores the old target\n";
}
