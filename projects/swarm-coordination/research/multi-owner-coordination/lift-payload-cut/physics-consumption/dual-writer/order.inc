// Equality stand-in used by the extracted SetComponentData helper.
template<class T> bool CompareData(const T& a,const T& b){
 return a.x==b.x&&a.y==b.y&&a.z==b.z;
}
/*SET_BODY*/
struct Control {
 struct {
   struct {int EntityValue=2; int Entity()const{return EntityValue;}} model;
   math::Vector3d linearVelocity{.125,.25,0};
 } data;
 decltype(data)* dataPtr=&data;
 void use(ECS& _ecm){
   /*PRODUCER_BODY*/
 }
};
struct Trace {
 ECS ecs;
 Lift lift;
 Physics phys;
 Control robot;
 Trace(bool allocated) {
   ecs.poses[1].value={{0,0,0},{}};
   ecs.poses[2].value={{.25,0,0},{}};
   if(allocated)ecs.commands[2]={};
   lift._initial_poses[1]=ecs.poses.at(1).value;
   lift._initial_aabbs[1]={{-1,-1,-1},{1,1,1}};
   phys.entityModelMap.bodies[2]={};
   phys.topLevelModelMap[2]=2;
 }
 void next(bool robot_first){
   if(robot_first)robot.use(ecs);
   lift.write(ecs,1,.625);
   if(!robot_first)robot.use(ecs);
   assert(ecs.commands.contains(2));
   phys.consume9(ecs);
   cleanup9(ecs);
   assert(!ecs.commands.contains(2));
 }
 const auto& calls(){return phys.entityFreeGroupMap.calls;}
};
int main(){
 for(bool allocated:{false,true}){
   Trace good(allocated), bad(allocated);
   for(int step=0;step<3;step++){
     good.next(true);bad.next(false);
     assert(good.calls().size()==size_t(step+1)&&bad.calls().size()==size_t(step+1));
     auto a=good.calls().back(),b=bad.calls().back();
     assert(a.x==b.x&&b.x==.125&&a.y==b.y&&b.y==.25);
     assert(a.z==.625&&b.z==0);
   }
 }
 Trace same(true);
 same.robot.data.linearVelocity.z=.625;
 same.next(false);
 assert(same.calls().back().z==.625); // value equality is not producer identity
 same.next(true);
 assert(same.calls().back().z==.625);
 std::cout<<"each phase order invokes one compatible setter per tick, for either initial allocation\n"
          <<"velocity control then lift: next component created and setter sees both axes\n"
          <<"lift then velocity control: a present lift write is overwritten; an absent one is skipped\n"
          <<"equal resulting z can conceal the different source order\n";
}
