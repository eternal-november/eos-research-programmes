#include <algorithm>
#include <chrono>
#include <condition_variable>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <memory>
#include <mutex>
#include <numeric>
#include <set>
#include <string>
#include <vector>
#define RCLCPP_INFO(...) ((void)0)
#define RCLCPP_ERROR(...) ((void)0)
#define RCLCPP_DEBUG(...) ((void)0)
#define RCLCPP_FATAL(...) ((void)0)
#define FMT_COMPILE(x) x

void ck(bool v){if(!v)std::abort();}
namespace rclcpp {
using Logger=int;
struct Time{Time(int=0,int=0,int=0){}};
}
namespace fmt {
std::string format(std::string x,const std::string& y){return x+y;}
}
namespace lifecycle_msgs::msg {struct State {enum{PRIMARY_STATE_ACTIVE=1,PRIMARY_STATE_INACTIVE};};}
namespace controller_interface {enum class return_type{OK,ERROR};}
namespace controller_manager_msgs::srv {struct SwitchController {struct Request{enum{STRICT=2};};};}

namespace hardware_interface {
namespace lifecycle_state_names {const char* ACTIVE="active";}
struct LoanedCommandInterface {
  std::string name;
  std::set<std::string>* owner=nullptr;
  LoanedCommandInterface(std::string s,std::set<std::string>& o):name(s),owner(&o) {
    ck(owner->insert(name).second);
  }
  LoanedCommandInterface(LoanedCommandInterface&& h):name(std::move(h.name)),owner(h.owner) {
    h.owner=nullptr;
  }
  LoanedCommandInterface& operator=(LoanedCommandInterface&&)=delete;
  ~LoanedCommandInterface(){if(owner)ck(owner->erase(name)==1);}
};
struct LoanedStateInterface {};
using Names=std::vector<std::string>;
struct ResourceManager {
  std::set<std::string> modes,claim;
  std::vector<std::string>* events;
  bool switch_ok=true,cleanup_prepare=true,cleanup_perform=true;
  int cleanup_results=0;
  bool prepare_command_mode_switch(const Names& add,const Names&) {
    ck(add.empty()); events->push_back("prepare-cleanup");
    if(!cleanup_prepare)++cleanup_results;
    return cleanup_prepare;
  }
  bool perform_command_mode_switch(const Names& add,const Names& rem) {
    bool cleanup=add.empty();
    events->push_back(cleanup?"perform-cleanup":"perform-switch");
    if(cleanup?!cleanup_perform:!switch_ok){ if(cleanup)++cleanup_results; return false; }
    for(const auto& i:rem)modes.erase(i);
    for(const auto& i:add)modes.insert(i);
    return true;
  }
  bool command_interface_is_claimed(const std::string& s)const{return claim.count(s)>0;}
  auto claim_command_interface(const std::string& s){return LoanedCommandInterface(s,claim);}
  auto claim_state_interface(const std::string&){return LoanedStateInterface{};}
  void make_controller_exported_state_interfaces_available(const std::string&){}
  void make_controller_reference_interfaces_available(const std::string&){}
  void make_controller_exported_state_interfaces_unavailable(const std::string&){}
  void make_controller_reference_interfaces_unavailable(const std::string&){}
};
}
namespace ros2_control {
void add_items(std::vector<std::string>& dst,const std::vector<std::string>& src) {
  dst.insert(dst.end(),src.begin(),src.end());  // all fixture interface names unique
}
}

using hardware_interface::Names;
struct State {
  bool active;
  int id()const{return active?1:2;}
  std::string label()const{return active?"active":"inactive";}
};
struct Ctrl {
  std::string name,mode;
  bool active,activates;
  std::vector<std::string>* events;
  std::vector<hardware_interface::LoanedCommandInterface> loans;
  Ctrl* get_node(){return this;}
  std::string get_name(){return name;}
  State activate(){
    events->push_back("activate:"+name);
    active=activates;
    return {active};
  }
  State deactivate(){
    events->push_back("deactivate:"+name);
    active=false;
    return {active};
  }
  State get_lifecycle_state(){return {active};}
  bool is_chainable(){return false;}
  bool set_chained_mode(bool){return true;}
  void release_interfaces(){loans.clear();}
  void assign_interfaces(std::vector<hardware_interface::LoanedCommandInterface> l,
                         std::vector<hardware_interface::LoanedStateInterface>){
    loans=std::move(l);
  }
};
struct Stats{void reset(){}};
namespace controller_manager {
struct ControllerSpec {
  struct Info {std::string name; Names claimed_interfaces;} info;
  std::shared_ptr<Ctrl> c;
  std::shared_ptr<rclcpp::Time> last_update_cycle_time=std::make_shared<rclcpp::Time>();
  std::shared_ptr<Stats> periodicity_statistics=std::make_shared<Stats>();
  std::shared_ptr<Stats> execution_time_statistics=std::make_shared<Stats>();
};
}
using controller_manager::ControllerSpec;
using Manager=std::unique_ptr<hardware_interface::ResourceManager>;
bool is_controller_active(const Ctrl& c){return c.active;}
bool is_controller_active(const std::shared_ptr<Ctrl>& c){return c->active;}
bool controller_name_compare(const ControllerSpec& a,const std::string& b){return a.info.name==b;}
Names get_command_interfaces_names(const std::shared_ptr<Ctrl>& c,const Manager&){return {c->mode};}
Names get_state_interfaces_names(const std::shared_ptr<Ctrl>&,const Manager&){return {};}
struct Clock {int get_clock_type(){return 0;}};
struct ControllerManager {
  struct Switch {
    std::mutex mutex;
    std::condition_variable cv;
    Names activate_request,deactivate_request,to_chained_mode_request,from_chained_mode_request;
    Names activate_command_interface_request,deactivate_command_interface_request;
    bool do_switch=true;
    int strictness=controller_manager_msgs::srv::SwitchController::Request::STRICT;
  } switch_params_;
  struct Timing {
    double switch_perform_mode_time,deactivation_time,switch_chained_mode_time,activation_time,switch_time;
  } execution_time_{};
  struct List {
    std::vector<ControllerSpec> controllers;
    auto& update_and_get_used_by_rt_list(){return controllers;}
  } rt_controllers_wrapper_;
  struct Params{bool handle_exceptions=true;};
  std::shared_ptr<Params> params_=std::make_shared<Params>();
  Manager resource_manager_=std::make_unique<hardware_interface::ResourceManager>();
  Clock c;
  auto get_trigger_clock(){return &c;}
  int get_logger(){return 0;}
  void manage_switch();
  void activate_controllers(const std::vector<ControllerSpec>&,const Names&,int);
  void deactivate_controllers(const std::vector<ControllerSpec>&,const Names&);
  void switch_chained_mode(const Names&,bool);
};
#include "selected.inc"

struct Result {
  bool failed;
  std::string message;
  std::vector<bool> active;
  std::vector<Names> claims;
  std::set<std::string> modes;
  std::vector<std::string> workflow;
};

Result trial(bool hardware,bool goodA,bool goodB,bool cleanupP,bool cleanupC) {
  std::vector<std::string> events;
  ControllerManager m;
  auto& r=*m.resource_manager_;
  auto& list=m.rt_controllers_wrapper_.controllers;
  auto add=[&](std::string n,std::string mode,bool act,bool pass){
    auto p=std::make_shared<Ctrl>();
    p->name=n;p->mode=mode;p->active=act;p->activates=pass;p->events=&events;
    if(act){r.modes.insert(mode);p->loans.emplace_back(mode,r.claim);}
    list.push_back({{n,{}},p});
  };
  r.events=&events;r.switch_ok=hardware;r.cleanup_prepare=cleanupP;r.cleanup_perform=cleanupC;
  add("old","position",true,true);
  add("newA","velocity",false,goodA);
  add("newB","guard",false,goodB);
  add("other","unrelated",true,true);
  auto& sw=m.switch_params_;
  sw.activate_request={"newA","newB"};sw.deactivate_request={"old"};
  sw.activate_command_interface_request={"velocity","guard"};
  sw.deactivate_command_interface_request={"position"};
  m.manage_switch();
  ck(!sw.do_switch);
  std::string msg;
  auto ret=evaluate_switch_result(m.resource_manager_,sw.activate_request,sw.deactivate_request,
                                  sw.strictness,0,list,msg);
  Result t{};
  t.failed=ret!=controller_interface::return_type::OK;
  t.message=msg;t.modes=r.modes;t.workflow=events;
  for(const auto& q:list){
    t.active.push_back(q.c->active);t.claims.push_back(q.info.claimed_interfaces);
  }
  ck(r.cleanup_results==static_cast<int>(hardware&&(!goodA||!goodB)&&(!cleanupP||!cleanupC)));
  for(auto& q:list)q.c->release_interfaces(); // harness objects release before mock resources destruct
  return t;
}

int main(){
  int rows=0;
  for(bool hw:{false,true})for(bool a:{false,true})for(bool b:{false,true})
  for(bool cp:{false,true})for(bool cc:{false,true}){
    auto t=trial(hw,a,b,cp,cc);
    ck(t.failed==(!hw||!a||!b));
    ck((t.active==std::vector<bool>{!hw,hw&&a&&b,hw&&a&&b,true}));
    bool left_new_modes=hw&&((a&&b)||!cp||!cc);
    for(const std::string name: {"velocity","guard"})ck(t.modes.count(name)==int(left_new_modes));
    ck(t.modes.count("position")==int(!hw)&&t.modes.count("unrelated")==1);
    if(hw)ck(t.workflow[0]=="perform-switch"&&t.workflow[1]=="deactivate:old");
    ++rows;
  }
  auto cleaned=trial(true,true,false,true,true);
  auto retained=trial(true,true,false,true,false);
  ck(cleaned.failed && retained.failed);
  ck(cleaned.message==retained.message && cleaned.active==retained.active && cleaned.claims==retained.claims);
  ck(cleaned.modes!=retained.modes);
  auto outright=trial(false,true,false,true,true);
  ck(outright.failed && outright.active.front() && !cleaned.active.front());
  std::cout<<"selected strict switch states "<<rows<<"\n";
  std::cout<<"same completed error and controller/claim states: cleanup cleared new modes vs retained them\n";
  std::cout<<"early switch failure leaves prior controller active; late failure does not restore it\n";
}
