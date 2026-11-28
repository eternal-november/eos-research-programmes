#include <chrono>
#include <optional>
static auto& gzdbg=gzwarn;
using Duration=std::chrono::steady_clock::duration;
using namespace std::chrono_literals;
namespace msgs {
struct Boolean {
 bool v{};
 void set_data(bool b){v=b;}
};
struct Reset {
 bool all_=false,time_=false,model_=false;
 bool all()const{return all_;}
 bool time_only()const{return time_;}
 bool model_only()const{return model_;}
};
struct Time {
 int s{},ns{};
 int sec()const{return s;}
 int nsec()const{return ns;}
};
struct WorldControl {
 bool p{},s{};
 unsigned steps{};
 std::optional<Reset> res;
 std::optional<Time> end;
 void CopyFrom(const WorldControl& o){*this=o;}
 bool pause()const{return p;}
 auto multi_step()const{return steps;}
 bool step()const{return s;}
 bool has_reset()const{return res.has_value();}
 const Reset& reset()const{return res.value();}
 int seed()const{return 0;}
 bool has_run_to_sim_time()const{return end.has_value();}
 const Time& run_to_sim_time()const{return end.value();}
};
struct WorldControlState {
 WorldControl value{};
 bool has_state()const{return false;} // declared service without state injection
 WorldControlState* New()const{return new WorldControlState();}
 void CopyFrom(const WorldControlState& s){*this=s;}
 const WorldControl& world_control()const{return value;}
 WorldControl* mutable_world_control(){return &value;}
};
struct LogPlaybackControl {
 bool rw{};
 std::optional<Time> target;
 bool rewind()const{return rw;}
 bool pause()const{return false;}
 unsigned multi_step()const{return 0;}
 bool forward()const{return false;}
 bool has_seek()const{return target.has_value();}
 const Time& seek()const{return target.value();}
};
}
/*CONTROL*/
struct UpdateInfo {Duration dt{},simTime{},realTime{}; unsigned iterations{};bool paused{};};
struct SimulationRunner {
 UpdateInfo currentInfo;
 bool requestedRewind{},resetInitiated{},stepping{};
 std::optional<Duration> requestedSeek{},requestedRunToSimTime;
 Duration simTimeEpoch{},stepSize=1s;
 double realTimeFactor{};
 struct Watch {
  Duration ElapsedRunTime()const{return 2s;}
  void Start(){}
  void Reset(){}
 } realTimeWatch;
 struct Network {bool IsPrimary()const{return true;}} *networkMgr{};
 unsigned pendingSimIterations{};
 std::mutex msgBufferMutex;
 std::unique_ptr<msgs::WorldControlState> newWorldControlState;
 std::vector<WorldControl> worldControls;
 EntityComponentManager entityCompMgr,initialEntityCompMgr;
 struct Systems {
   unsigned completed{};
   bool currently_ready=true;
   void Reset(const UpdateInfo&,EntityComponentManager&){currently_ready=true;++completed;}
 } localSystems,*systemMgr=&localSystems;

 void UpdateCurrentInfo();
 bool OnWorldControl(const msgs::WorldControl&,msgs::Boolean&);
 bool OnWorldControlState(const msgs::WorldControlState&,msgs::Boolean&);
 bool OnPlaybackControl(const msgs::LogPlaybackControl&,msgs::Boolean&);
 void ProcessMessages();
 void ProcessWorldControl();
 void SetRunToSimTime(const Duration&);
 void SetStepping(bool x){stepping=x;}
 bool Paused()const{return currentInfo.paused;}
 void SetPaused(bool p){currentInfo.paused=p;}

 // Declared serial test wrapper around exact snippets in their source order.
 void after_controls_clock(bool& capture_open){
    this->UpdateCurrentInfo();
    if(resetInitiated)capture_open=false; // before changing actual graph
/*ECM_CUT*/
 }
 void systems(){
/*SYSTEM_CUT*/
    assert(!resetInitiated);
 }
 void finish_loop(){
    this->ProcessMessages();
    this->entityCompMgr.ProcessRemoveEntityRequests();
    this->resetInitiated=false;
 }
 void prime(){
    for(int i=0;i<10;++i)entityCompMgr.CreateEntity();
    initialEntityCompMgr.CopyFrom(entityCompMgr);
    currentInfo.simTime=4s;
    currentInfo.iterations=4;
 }
};
/*RUNNER_CODE*/

enum class Op{ResetAll,TimeOnly,ModelOnly,Play,Pause,Seek};
struct Receipt {int era;Entity id;long long tick;};
struct Probe {
 SimulationRunner sim;
 // Separately hosted model state, not copied in the native ResetTo.
 int outward_era=1;
 bool external_open=true, epoch_authority_available=true;
 Entity old() {
   const auto id=sim.entityCompMgr.CreateEntity();assert(id==11);
   sim.entityCompMgr.RequestRemoveEntity(id,false);
   sim.entityCompMgr.ProcessRemoveEntityRequests();
   return id;
 }
 bool send(Op k){
    msgs::Boolean res;
    if(k==Op::Seek){
      assert(sim.OnPlaybackControl({false,msgs::Time{0,0}},res));
    }else{
      msgs::WorldControl m;
      m.p=k==Op::Pause;
      if(k==Op::ResetAll||k==Op::TimeOnly||k==Op::ModelOnly)
          m.res=msgs::Reset{k==Op::ResetAll,k==Op::TimeOnly,k==Op::ModelOnly};
      assert(sim.OnWorldControl(m,res));
    }
    return res.v;
 }
 bool before_systems(){
   sim.after_controls_clock(external_open);
   return sim.resetInitiated;
 }
 void after_systems(bool actual){
   assert(actual==sim.resetInitiated);
   sim.systems();
   if(actual){++outward_era;external_open=true;}
 }
 std::optional<Receipt> gated_allocation(){
   if(!external_open||!epoch_authority_available)return {};
   return Receipt{outward_era,sim.entityCompMgr.CreateEntity(),sim.currentInfo.simTime.count()};
 }
 Receipt allocation(){return gated_allocation().value();}
};
bool reset(Op k){return k==Op::ResetAll||k==Op::TimeOnly;}
int main(){
 int trials=0,actual=0,false_positive=0;
 const std::vector<Op> ops{Op::ResetAll,Op::TimeOnly,Op::ModelOnly,Op::Play,Op::Pause,Op::Seek};
 for(auto a:ops)for(auto b:ops)for(auto c:ops){
   Probe p;p.sim.prime();p.old();
   for(auto k:{a,b,c})assert(p.send(k)); // acknowledged enqueues
   assert(!p.sim.requestedRewind&&p.sim.entityCompMgr.dataPtr->entityCount==11);
   p.sim.finish_loop();
   assert(p.sim.requestedRewind==reset(c));
   bool z=p.before_systems();
   assert(z==reset(c));
   assert(p.sim.entityCompMgr.dataPtr->entityCount==(z?10:11));
   assert(p.sim.localSystems.completed==0);
   assert(p.external_open!=z);
   p.after_systems(z);
   assert(p.outward_era==(z?2:1)&&p.external_open);
   assert(p.sim.localSystems.completed==int(z));
   actual+=z;false_positive+=!z&&(reset(a)||reset(b));
   ++trials;
 }
 // The same accepted request order reaches different branches when
 // the source queue groups the ordinary pause with the rewind or after it.
 for(bool flush_between:{false,true}){
   Probe g;g.sim.prime();g.old();
   assert(g.send(Op::ResetAll));
   if(flush_between){
     g.sim.finish_loop();bool z=g.before_systems();assert(z);g.after_systems(z);
   }
   assert(g.send(Op::Pause));g.sim.finish_loop();
   bool z=g.before_systems();assert(!z);g.after_systems(z);
   assert(g.outward_era==(flush_between?2:1));
   assert(g.allocation().id==(flush_between?11:12));
 }
 // A clock observer sees the same sim time and iteration in both, but
 // only one branch copied a snapshot and replaced the body lifetime.
 for(bool use_seek:{false,true}){
   Probe p;p.sim.prime();p.old();
   assert(p.send(use_seek?Op::Seek:Op::ResetAll));
   p.sim.finish_loop();auto z=p.before_systems();
   assert(z==!use_seek&&p.sim.currentInfo.simTime==0s&&p.sim.currentInfo.iterations==0);
   p.after_systems(z);
   assert(p.allocation().id==(use_seek?12:11));
 }
 // One physically selected entity-allocation completion is captured before
 // the previous world starts retiring. Delivery may take place after reset.
 Probe p;p.sim.prime();
 p.sim.currentInfo.simTime=1s;
 auto past=p.allocation();
 p.sim.entityCompMgr.RequestRemoveEntity(past.id,false);
 p.sim.entityCompMgr.ProcessRemoveEntityRequests();
 for(int k=2;k<=3;++k){
   assert(p.send(Op::ResetAll));p.sim.finish_loop();
   bool occurred=p.before_systems();assert(occurred&&!p.external_open);
   // At this cut an observer can already see rewound time and ECM, but the
   // modeled systems reset callback is not complete.
   assert(p.sim.currentInfo.simTime==0s&&p.sim.localSystems.completed==unsigned(k-2));
   assert(!p.gated_allocation()&&p.sim.entityCompMgr.dataPtr->entityCount==10);
   p.after_systems(occurred);
   p.sim.finish_loop(); // clear resetInitiated before next time advance
   assert(!p.before_systems());p.after_systems(false);
   p.epoch_authority_available=false;
   assert(!p.gated_allocation());
   p.epoch_authority_available=true;
   auto active=p.allocation();
   assert(active.era==k&&active.id==past.id&&active.tick==past.tick);
   // Stamping at delivery aligns every field even though past happened
   // in a previous allocation lifetime.
   Receipt naive{p.outward_era,past.id,past.tick};
   assert(naive.era==active.era&&past.era!=active.era);
   p.sim.entityCompMgr.RequestRemoveEntity(active.id,false);
   p.sim.entityCompMgr.ProcessRemoveEntityRequests();
 }
 std::cout<<trials<<" acknowledged control batches; "<<actual
          <<" actual rewinds; "<<false_positive<<" earlier resets overwritten\n"
          <<"same accepted reset/pause order differs when queue drain separates the calls\n"
          <<"seek aliases reset clock and iteration; reset alone restores allocator\n"
          <<"allocation capture distinguishes three eras despite same entity and tick; delivery-time stamp does not\n";
}
