template<class T> bool CompareData(const T& a,const T& b){
 return a.x==b.x&&a.y==b.y&&a.z==b.z;
}
/*SET_BODY*/
using V=math::Vector3d;
bool equals(V a,V b){return CompareData(a,b);}
struct Writer{
 struct {
    struct {int Entity()const{return 2;}} model;
    V linearVelocity;
 } command;
 decltype(command)* dataPtr=&command;
 void use(ECS& _ecm){ /*PRODUCER_BODY*/ }
};
struct Plant{
 ECS ecs;
 Lift lift;
 Physics phys;
 Writer robot;
 Plant(bool quarter){
   ecs.poses[1].value={{0,0,0},{}};
   ecs.poses[2].value={{.25,0,0},{quarter}};
   lift._initial_poses[1]=ecs.poses[1].value;
   lift._initial_aabbs[1]={{-1,-1,-1},{1,1,1}};
   phys.entityModelMap.bodies[2]={};
   phys.topLevelModelMap[2]=2;
 }
 void native(double x,double y,double z){
   robot.command.linearVelocity={x,y,0};
   robot.use(ecs);
   lift.write(ecs,1,z);
 }
 static V inverse(bool quarter,V w){
   return quarter?V{-w.z,w.y,w.x}:w;
 }
 bool composed(bool observed,bool current,V h,V v){
   assert(ecs.poses.at(2).value.rot.quarter==current);
   if(observed!=current)return false; // authored immutable cut guard
   assert(h.z==0&&v.x==0&&v.y==0);
   auto a=inverse(observed,h),b=inverse(observed,v);
   assert(equals(ecs.poses.at(2).value.Rot()*a,h));
   assert(equals(ecs.poses.at(2).value.Rot()*b,v));
   // Separate tagged contributions verified above; one modeled writer owns the slot.
   ecs.SetComponentData<components::LinearVelocityCmd>(2,a+b);
   return true;
 }
 V setter(){
   phys.consume9(ecs);
   assert(phys.entityFreeGroupMap.calls.size()==1);
   return phys.entityFreeGroupMap.calls.back();
 }
};
int main(){
 int checked=0;
 for(bool quarter:{false,true}){
   for(int x:{-1,0,1})for(int y:{-1,0,1})for(int z:{-1,0,1}){
     V h{double(x),double(y),0},v{0,0,double(z)};
     Plant a(quarter),b(quarter);
     a.native(x,y,z);
     assert(b.composed(quarter,quarter,h,v));
     assert(equals(b.setter(),h+v));
     assert(equals(a.setter(),h+v)==(!quarter||(x==0&&z==0)));
     checked++;
   }
 }
 Plant stale(true);
 assert(!stale.composed(false,true,{1,0,0},{0,0,1}));
 assert(!stale.ecs.commands.contains(2));
 stale.phys.consume9(stale.ecs);
 assert(stale.phys.entityFreeGroupMap.calls.empty());
 Plant fresh(true);
 assert(fresh.composed(true,true,{1,0,0},{0,0,1}));
 assert(equals(fresh.setter(),{1,0,1}));
 std::cout<<checked<<" selected setter comparisons; aligned native split matches; quarter turn only matches when x and z are both zero\n"
          <<"authored consumer-bound composition matches both contributions and their sum\n"
          <<"stale frame evidence: no composed write or setter in the empty-slot fixture\n";
}
