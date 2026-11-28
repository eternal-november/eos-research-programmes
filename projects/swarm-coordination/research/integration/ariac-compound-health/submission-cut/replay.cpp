#include <algorithm>
#include <array>
#include <cassert>
#include <iostream>
#include <memory>
#include <mutex>
#include <string>
#include <vector>
#define RCLCPP_INFO_STREAM(...) ((void)0)
#define RCLCPP_WARN(...) ((void)0)
namespace ariac_msgs {
namespace msg {struct CompetitionState {enum {STARTED,ENDED};};}
namespace srv {struct SubmitOrder {
 struct Request {std::string order_id;};
 struct Response {bool success{};std::string message;};
};}
}
struct Order {
 std::string id,trigger;
 bool announced=false,submitted=false;
 int submission=-1,announcement=-1;
 Order(std::string i,std::string t):id(i),trigger(t){}
 auto GetId()const{return id;}
 auto GetOrderId()const{return trigger;}
 bool IsAnnounced()const{return announced;}
 void SetIsAnnounced(){announced=true;}
 void SetAnnouncedTime(int t){announcement=t;}
 void SetIsSubmitted(){submitted=true;}
 void SetSubmittedTime(int t){submission=t;}
 bool GetKittingTask()const{return true;}
 bool GetAssemblyTask()const{return false;}
 bool GetCombinedTask()const{return false;}
};
struct Challenge {
 std::string trigger;
 std::vector<std::string> scopes;
 int duration,started=-1;
 bool active=false;
 Challenge(std::string x,std::vector<std::string> s,int d):trigger(x),scopes(s),duration(d){}
 auto GetTriggerOrderId()const{return trigger;}
 auto GetDuration()const{return duration;}
 auto GetRobotsToDisable()const{return scopes;}
 auto GetSensorsToDisable()const{return scopes;}
 auto HasStarted()const{return active;}
 void SetStarted(){active=true;}
 void SetStartTime(int t){started=t;}
};
struct Message{std::string id;};
struct Publisher{
 std::vector<std::string> trace;
 void publish(const Message& m){trace.push_back(m.id);}
};
struct Impl {
 std::mutex lock_;
 int current_state_=ariac_msgs::msg::CompetitionState::STARTED;
 int elapsed_time_=0,total_orders_=1;
 std::vector<std::string> trial_orders_{"A","B"},submitted_orders_;
 std::vector<std::shared_ptr<Order>> all_orders_,on_order_submission_orders_;
 std::vector<std::shared_ptr<Challenge>> on_submission_robot_malfunctions_,
   in_progress_robot_malfunctions_,on_submission_sensor_blackouts_,in_progress_sensor_blackouts_;
 std::shared_ptr<Publisher> order_pub_=std::make_shared<Publisher>();
 bool ceiling_robot_health_=true,floor_robot_health_=true;
 bool break_beam_sensor_health_=true,proximity_sensor_health_=true,
      laser_profiler_sensor_health_=true,lidar_sensor_health_=true,
      camera_sensor_health_=true,logical_camera_sensor_health_=true;
 std::vector<std::string> scoring_invocations;
 void ScoreKittingTask(const std::shared_ptr<Order>& o,const std::string& k){
   assert(o->id==k);
   scoring_invocations.push_back(k);
 }
 void ScoreAssemblyTask(const std::shared_ptr<Order>&,const std::string&){assert(false);}
 void ScoreCombinedTask(const std::shared_ptr<Order>&,const std::string&){assert(false);}
};
struct TaskManagerPlugin{
 Impl state,*impl_=&state;
 void SetSensorsHealth(const std::vector<std::string>&);
 void SetRobotsHealth(const std::vector<std::string>&);
 void ProcessOnSubmissionOrders();
 void ProcessOnSubmissionRobotMalfunctions();
 void ProcessOnSubmissionSensorBlackouts();
 bool SubmitOrderServiceCallback(
  const std::shared_ptr<ariac_msgs::srv::SubmitOrder::Request>,
  std::shared_ptr<ariac_msgs::srv::SubmitOrder::Response>);
 Message BuildOrderMsg(const std::shared_ptr<Order>& o) {return {o->id};}
 // The order here is the source order of these selected branches of OnUpdate.
 void update(int time){
   std::lock_guard<std::mutex> lk(state.lock_);
   state.elapsed_time_=time;
   ProcessOnSubmissionOrders();
   ProcessOnSubmissionSensorBlackouts();
   ProcessOnSubmissionRobotMalfunctions();
 }
 bool submit_a(){
   using S=ariac_msgs::srv::SubmitOrder;
   auto req=std::make_shared<S::Request>();req->order_id="A";
   auto resp=std::make_shared<S::Response>();
   assert(SubmitOrderServiceCallback(req,resp));
   return resp->success;
 }
};
#include "selected.inc"
int main(){
 int n=0;
 // Healthy flags at the first cut; A is a valid announced order. Scores
 // are stubbed: only dispatch to the native scoring call site is measured.
 for(bool before:{false,true})for(bool retry:{false,true})
 for(bool robotFault:{false,true})for(bool sensorFault:{false,true})
 for(int first=1;first<=8;++first)for(int gap=1;gap<=8;++gap){
   TaskManagerPlugin p;
   auto a=std::make_shared<Order>("A","");a->announced=true;
   auto b=std::make_shared<Order>("B","A");
   auto r=std::make_shared<Challenge>("A",std::vector<std::string>{"floor_robot"},100);
   auto s=std::make_shared<Challenge>("A",std::vector<std::string>{"logical_camera"},100);
   p.state.all_orders_={a,b};p.state.on_order_submission_orders_={b};
   if(robotFault)p.state.on_submission_robot_malfunctions_={r};
   if(sensorFault)p.state.on_submission_sensor_blackouts_={s};
   p.update(0);
   if(before)assert(p.submit_a());
   // Before the world update, a plant-health-only view matches regardless.
   assert(p.state.floor_robot_health_&&p.state.logical_camera_sensor_health_&&!b->announced);
   assert(a->submitted==before);
   p.update(first);
   assert(b->announced==before);
   assert(p.state.floor_robot_health_==!(robotFault&&before));
   assert(p.state.logical_camera_sensor_health_==!(sensorFault&&before));
   if(!before)assert(p.submit_a());
   if(retry)assert(!p.submit_a());
   p.update(first+gap);
   assert((p.state.order_pub_->trace==std::vector<std::string>{"B"}));
   assert((p.state.scoring_invocations==std::vector<std::string>{"A"}));
   assert(b->announcement==first+(before?0:gap));
   assert(r->started==(robotFault?b->announcement:-1));
   assert(s->started==(sensorFault?b->announcement:-1));
   assert(p.state.ceiling_robot_health_&&p.state.camera_sensor_health_);
   assert(p.state.total_orders_==0);
   ++n;
 }

 int runs=0,cases=0,chosen=0,strict=0;
 for(bool robotFault:{false,true})for(bool sensorFault:{false,true})
 for(int oldF=1;oldF<=7;++oldF)for(int oldS=1;oldS<=7;++oldS)
 for(int end=1;end<=8;++end){
    // Specific old operations need uninterrupted availability until their own
    // effect cut. Their durations/completion are the modeled, not native, seam.
    const int best_cut=std::max(robotFault?oldF:0,sensorFault?oldS:0);
    bool any=false;
    for(int award=0;award<8;++award){
      TaskManagerPlugin p;
      auto a=std::make_shared<Order>("A","");a->announced=true;
      auto b=std::make_shared<Order>("B","A");
      p.state.all_orders_={a,b};p.state.on_order_submission_orders_={b};
      if(robotFault)p.state.on_submission_robot_malfunctions_={
        std::make_shared<Challenge>("A",std::vector<std::string>{"floor_robot"},100)};
      if(sensorFault)p.state.on_submission_sensor_blackouts_={
        std::make_shared<Challenge>("A",std::vector<std::string>{"logical_camera"},100)};
      bool f=true,s=true;
      for(int tick=0;tick<=8;++tick){
        p.update(tick);
        assert(p.state.ceiling_robot_health_);
        if(tick<=oldF)f &=p.state.floor_robot_health_;
        if(tick<=oldS)s &=p.state.logical_camera_sensor_health_;
        if(tick==award)assert(p.submit_a());
      }
      bool yields=f&&s&&b->announcement<=end;
      assert(b->announcement==award+1);
      assert(yields==(award>=best_cut && award+1<=end));
      any |= yields;
      if(award==best_cut && yields)++chosen;
      if(award==0 && !yields && best_cut+1<=end)++strict;
      ++runs;
    }
    assert(any==(best_cut+1<=end));++cases;
 }
 std::cout<<n<<" native submission, retry, and dependent-update schedules\n"
          <<runs<<" native trigger traces for "<<cases<<" old-work deadline families\n"
          <<chosen<<" positive guarded schedules; "<<strict
          <<" families exclude immediate submission but admit staged submission\n";
}
