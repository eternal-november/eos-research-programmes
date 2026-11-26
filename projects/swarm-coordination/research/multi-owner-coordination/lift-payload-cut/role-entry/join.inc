namespace math=gz::math;
static std::ostringstream gzerr,gzdbg;
using rmf_fleet_adapter::lift_supervisor::Node;
struct WorldVelocityCommandFeatureList {};
struct Body{
 bool free=true, feature=true;
 Body* FindFreeGroup(){return free?this:nullptr;}
};
struct Physics{
 struct{
   std::map<Entity,Body> objects;
   Body* Get(Entity e){auto i=objects.find(e);return i==objects.end()?nullptr:&i->second;}
 } entityModelMap;
 std::map<Entity,Entity> topLevelModelMap;
 struct{
   bool feature=true;
   Entity last{};
   std::map<Entity,math::Vector3d> writes;
   void AddEntity(Entity e,Body* b){last=e;feature=b->feature;}
   template<class T> auto* EntityCast(Entity){return feature?this:nullptr;}
   void SetWorldLinearVelocity(math::Vector3d v){writes[last]=v;}
 } entityFreeGroupMap;
 void consume(EntityComponentManager& _ecm){
   /*PHYSICS_BODY*/
 }
 void cleanup(EntityComponentManager& _ecm){
   /*CLEANUP_BODY*/
 }
};
struct Scene {
 Node n;
 LiftPlugin lift;
 EntityComponentManager e;
 Physics physics;
 Scene(){
   for(auto i:{1,2,3}){
     PoseData p;
     p.p.x=i==1?0:i==2?.25:.5;
     e.poses.emplace(i,components::Pose(p));
     if(i>1){e.vels[i]={};physics.entityModelMap.objects[i]={};physics.topLevelModelMap[i]=i;}
   }
   lift._initial_poses[1]=e.poses.at(1).Data();
   lift._initial_aabbs[1]={{-1,-1,-1},{1,1,1}};
   lift._last_lift_command[1]=LiftCommand{};
 }
 LiftState admit(){
   LiftRequest r;
   r.session_id="successor";
   r.destination_floor="B";
   n._adapter_lift_request_update(std::make_unique<LiftRequest>(r));
   lift.apply(&e,std::make_unique<LiftRequest>(n._lift_request_pub->sent.back()));
   assert(e.active);
   return lift.get_current_state(1,e,e.lift.Data(),&*e.active);
 }
 void disable(int mode){
   if(mode==0)physics.entityModelMap.objects.erase(2);
   else if(mode==1)physics.topLevelModelMap[2]=1;
   else if(mode==2)physics.entityModelMap.objects.at(2).free=false;
   else if(mode==3)physics.entityModelMap.objects.at(2).feature=false;
 }
 bool modeled_current_role(Entity i){
   auto p=physics.entityModelMap.Get(i);
   return p&&p->free&&p->feature&&physics.topLevelModelMap.at(i)==i&&e.vels.contains(i);
 }
 void frame(){
   lift.velocity(e,1,.625);
   assert(e.vels.at(2).Data().z==.625&&e.vels.at(3).Data().z==.625);
   physics.consume(e);
   physics.cleanup(e);
   assert(e.vels.empty());
 }
};
int main(){
 for(int m=0;m<4;m++)for(bool after:{false,true}){
   Scene reference, impaired;
   if(!after)impaired.disable(m);
   const auto p=reference.admit(),q=impaired.admit();
   assert(p==q&&p.session_id=="successor");
   assert(impaired.modeled_current_role(2)==after);
   if(after)impaired.disable(m);
   assert(!impaired.modeled_current_role(2)&&impaired.modeled_current_role(3));
   reference.frame();impaired.frame();
   assert(reference.physics.entityFreeGroupMap.writes.at(2).z==.625);
   assert(!impaired.physics.entityFreeGroupMap.writes.contains(2));
   assert(impaired.physics.entityFreeGroupMap.writes.at(3).z==.625);
 }
 std::cout<<"eight matched comparisons: same accepted lift state and writes before consumption\n"
          <<"four recipient impairments suppress its setter without suppressing the paired compatible payload\n"
          <<"changes after entry defeat an earlier capability observation; both slots still clean up\n";
}
