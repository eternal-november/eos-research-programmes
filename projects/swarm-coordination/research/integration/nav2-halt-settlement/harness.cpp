#include <algorithm>
#include <cassert>
#include <chrono>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <mutex>
#include <optional>
#include <string>
#include <unordered_map>
#include <vector>
#define RCLCPP_ERROR(...) ((void)0)
#define RCLCPP_INFO(...) ((void)0)
#define RCLCPP_INFO_THROTTLE(...) ((void)0)

void ck(bool yes){ if(!yes)std::abort(); }
enum class E { Result, Zero, Reset };
struct Tape { std::vector<E> events; };
struct Action { struct Result {}; };
namespace rclcpp_action {
template<class A>struct ServerGoalHandle{
  Tape* out; bool active=true,canceling=false;
  bool is_canceling(){return canceling;}
  void canceled(std::shared_ptr<typename A::Result>){active=false;out->events.push_back(E::Result);}
  void abort(std::shared_ptr<typename A::Result>){active=false;out->events.push_back(E::Result);}
};
}
namespace geometry_msgs::msg {
struct TwistStamped {
  struct { struct { double x=1,y=1,z=1; } angular,linear; } twist;
  struct {std::string frame_id; int stamp=0;} header;
};
}
struct Drive {
  Tape* out; bool done=false;
  bool cancel(){return done;}
  void reset(){out->events.push_back(E::Reset);}
};
struct Costmap { std::string getBaseFrameID(){return "base";} };

struct StubServer {
  using ActionT=Action;
  using G = rclcpp_action::ServerGoalHandle<ActionT>;
  bool is_active(std::shared_ptr<G> x)const{return x && x->active;}
  void info_msg(const std::string&)const{}
  void error_msg(const std::string&)const{}
  void log_error_details_if_available(const std::shared_ptr<ActionT::Result>&)const{}
  mutable std::recursive_mutex update_mutex_;
  std::shared_ptr<G> current_handle_,pending_handle_;
  bool preempt_requested_=false;
#include "server.inc"
};
struct ControllerServer {
  Tape* out;
  std::shared_ptr<StubServer> action_server_;
  std::unordered_map<std::string,std::shared_ptr<Drive>> controllers_;
  std::string current_controller_="drive";
  std::shared_ptr<Costmap> costmap_ros_=std::make_shared<Costmap>();
  struct Params { bool publish_zero_velocity=false; };
  std::shared_ptr<Params> params_=std::make_shared<Params>();
  int now(){return 0;}
  void publishVelocity(geometry_msgs::msg::TwistStamped cmd){
    ck(cmd.twist.angular.x==0 && cmd.twist.angular.y==0 && cmd.twist.angular.z==0);
    ck(cmd.twist.linear.x==0 && cmd.twist.linear.y==0 && cmd.twist.linear.z==0);
    out->events.push_back(E::Zero);
  }
  void onGoalExit(bool);
  void publishZeroVelocity();
  void selected_poll(){
#include "poll.inc"
  }
};
#include "controller.inc"

namespace BT {enum class NodeStatus{IDLE,RUNNING};}
namespace action_msgs::msg {struct GoalStatus{enum{STATUS_ACCEPTED=1,STATUS_EXECUTING,STATUS_CANCELING};};}
namespace rclcpp {enum class FutureReturnCode {SUCCESS,TIMEOUT};}

using Ms=std::chrono::milliseconds;
struct Delta { int n; template<class T>T to_chrono(){return T(n);} };
struct Point {int n; Delta operator-(Point o){return {n-o.n};}};
struct Clock {int t=0;Point now(){return {t};}};
struct Goal {int state=action_msgs::msg::GoalStatus::STATUS_EXECUTING; int get_status(){return state;}};
template<class T>struct Future{int ready;T v;T get(){return v;}};
struct Transport {
  Clock* clock;
  void spin_some(){}
  template<class T>rclcpp::FutureReturnCode spin_until_future_complete(Future<T>& f,Ms dt){
    if(f.ready <= clock->t+dt.count()){
      clock->t=std::max(clock->t,f.ready);return rclcpp::FutureReturnCode::SUCCESS;
    }
    clock->t+=dt.count();return rclcpp::FutureReturnCode::TIMEOUT;
  }
};
struct Client {
  int ack=0,result=0,cancel_requests=0,goal_retrievals=0;
  Future<int> async_get_result(const std::shared_ptr<Goal>&){goal_retrievals++;return {result,0};}
  Future<int> async_cancel_goal(const std::shared_ptr<Goal>&){cancel_requests++;return {ack,0};}
};
struct BTBase { virtual void halt()=0; virtual ~BTBase()=default; };
struct Bt : BTBase {
  Clock target;
  Clock* node_ = &target;
  Transport callback_group_executor_{node_};
  Client client;
  Client* action_client_=&client;
  std::shared_ptr<Goal> goal_handle_;
  std::optional<Future<std::shared_ptr<Goal>>> future_goal_handle_;
  Point time_goal_sent_{0};
  Ms server_timeout_{5}, cancel_timeout_{7};
  int hook_calls=0;
  BT::NodeStatus mode=BT::NodeStatus::RUNNING;
  BT::NodeStatus status(){return mode;}
  void resetStatus(){mode=BT::NodeStatus::IDLE;}
  void on_cancelled(){++hook_calls;}
#include "bt.inc"
};

int main(){
  // Exact selected controller poll and termination on one scoped goal.
  Tape tape;
  auto server=std::make_shared<StubServer>();
  auto drive=std::make_shared<Drive>();
  drive->out=&tape;
  ControllerServer ctl{&tape,server,{{"drive",drive}}};
  server->current_handle_=std::make_shared<StubServer::G>(StubServer::G{&tape,true,true});
  ctl.selected_poll();
  ck(tape.events.empty());                // controller did not finish cancellation
  drive->done=true;
  ctl.selected_poll();
  ck((tape.events==std::vector<E>{E::Result,E::Zero,E::Reset}));
  ck(server->current_handle_==nullptr);
  std::cout<<"controller source order: terminal result, zero publication, reset\n";

  // Exact behavior-tree source, fixed program timeouts and chosen deliveries.
  int bt_cases=0;
  for(int begin=0;begin<=8;++begin) for(int response=0;response<=8;++response)
  for(int ack=0;ack<=11;++ack) for(int result=0;result<=18;++result){
    Bt b;
    b.target.t=begin;
    auto g=std::make_shared<Goal>();
    b.future_goal_handle_=Future<std::shared_ptr<Goal>>{response,g};
    b.client.ack=ack;b.client.result=result;
    b.halt();
    bool obtains=begin<5 && response<=5;
    ck(b.mode==BT::NodeStatus::IDLE && !b.future_goal_handle_);
    ck(b.client.cancel_requests==int(obtains));
    ck(b.client.goal_retrievals==int(obtains));
    ck(b.hook_calls==int(obtains));
    int t=begin>=5 ? begin : std::max(begin,std::min(5,response));
    if(obtains){
      t=std::max(t,std::min(t+5,ack));
      t=std::max(t,std::min(t+7,result));
    }
    ck(b.target.t==t);++bt_cases;
  }
  Bt under_cancel;
  under_cancel.goal_handle_=std::make_shared<Goal>();
  under_cancel.goal_handle_->state=action_msgs::msg::GoalStatus::STATUS_CANCELING;
  under_cancel.halt();
  ck(under_cancel.hook_calls==0&&under_cancel.client.cancel_requests==0);
  ck(under_cancel.mode==BT::NodeStatus::IDLE);
  std::cout<<"halt reset, callback, waits vs selected source formula: "<<bt_cases<<" cases\n";

  // Separate guarded physical effect. Time zero is the controller poll that
  // ordered result and zero publication above; distinct channels deliver later.
  int rows=0,overlaps=0,certificate_gain=0;
  for(int r=0;r<=8;++r)for(int z=0;z<=8;++z)for(int b=1;b<=5;++b)
  for(int observe=0;observe<=3;++observe)for(int D=0;D<=20;++D){
    int settle=z+b;      // actual brake completion under the guarded drive model
    int read=settle+observe;
    int blind=8+5;       // a sound global bound with this full envelope
    bool launch_at_result_has_old_motion=r<settle;
    if(launch_at_result_has_old_motion)++overlaps;
    bool done_with_local=std::max(r,read)+1<=D;
    bool done_with_blind=std::max(r,blind)+1<=D;
    ck(!done_with_local || read>=settle);
    if(done_with_local&&!done_with_blind)++certificate_gain;
    // Direct integer search of start times after both declared gates.
    bool direct=false;
    for(int s=0;s<D;++s)if(s>=r&&s>=read&&s>=settle)direct=true;
    ck(direct==done_with_local);
    ++rows;
  }
  std::cout<<"physical channel/deadline rows "<<rows<<"; early-result rows "<<overlaps
    <<"; local-evidence cases beating blind bound "<<certificate_gain<<"\n";
}
