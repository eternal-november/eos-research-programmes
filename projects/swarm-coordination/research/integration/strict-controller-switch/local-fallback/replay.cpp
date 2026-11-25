#include <algorithm>
#include <atomic>
#include <cassert>
#include <chrono>
#include <condition_variable>
#include <functional>
#include <future>
#include <iostream>
#include <memory>
#include <mutex>
#include <string>
#include <thread>
#include <vector>

#define RCLCPP_ERROR(...) ((void)0)
#define RCLCPP_DEBUG(...) ((void)0)
#define RCLCPP_INFO_EXPRESSION(...) ((void)0)
#define RCLCPP_ERROR_EXPRESSION(...) ((void)0)
using Names=std::vector<std::string>;
namespace ros2_control {
bool has_item(const Names &a,const std::string& v) {
  return std::find(a.begin(),a.end(),v)!=a.end();
}
void add_item(Names &a,const std::string &v) {
  if (!has_item(a,v)) a.push_back(v);
}
}
namespace controller_interface {
enum class return_type {ERROR,OK};
}
namespace controller_manager_msgs::srv {
struct SwitchController {
  struct Request {
    static constexpr int STRICT=2;
    Names activate_controllers,deactivate_controllers;
    int strictness{1};
    bool activate_asap{false};
    int timeout{1};
  };
  struct Response {bool ok{false}; std::string message;};
};
}
using Service=controller_manager_msgs::srv::SwitchController;
namespace controller_manager {
struct Ctrl {
  Names interfaces;
  bool active, error;
};
struct ControllerSpec {
  struct Info {std::string name; Names fallback_controllers_names;} info;
  std::shared_ptr<Ctrl> c;
  Names controllers_chain_group;
};
}
using controller_manager::ControllerSpec;
bool is_controller_active(const std::shared_ptr<controller_manager::Ctrl> &c) {
  return c->active;
}
bool is_controller_inactive(const std::shared_ptr<controller_manager::Ctrl> &c) {
  return !c->active;
}
namespace rclcpp {
struct Time {};
struct Duration { double seconds() const {return 1;} };
}
namespace hardware_interface {
enum class return_type {OK,ERROR};
struct ResourceManager {
  bool succeeds{true};
  int attempted{0}, accepted{0};
  Names starts, stops, failed_devices;
  std::pair<return_type,Names> read(const rclcpp::Time&,const rclcpp::Duration&) {
    return {failed_devices.empty()?return_type::OK:return_type::ERROR,failed_devices};
  }
  Names get_cached_controllers_to_hardware(const std::string& dev) {
    return dev=="B_device"?Names{"B_drive"}:Names{};
  }
  bool prepare_command_mode_switch(const Names&,const Names&) {return true;}
  bool perform_command_mode_switch(const Names& start,const Names& stop) {
    starts=start; stops=stop;
    ++attempted;
    if(succeeds) ++accepted;
    return succeeds;
  }
  void enforce_command_limits(int) {}
};
}
using RM=hardware_interface::ResourceManager;
Names get_command_interfaces_names(const std::shared_ptr<controller_manager::Ctrl> &c,
                                  const std::unique_ptr<RM> &) {
  return c->interfaces;
}
struct Params {
  std::atomic_bool do_switch{true}, ready_to_switch{false};
  bool activate_asap{false};
  Names activate_request,deactivate_request,to_chained_mode_request,from_chained_mode_request;
#include "skip_member.inc"
};
struct RTBuffer {
  Names deactivate_controllers_list,fallback_controllers_list,
        activate_controllers_using_interfaces_list,interfaces_to_start,interfaces_to_stop;
};
struct ControllerManager {
  std::mutex services_lock_, sim_mu;
  std::condition_variable cv;
  bool old_waiting{false}, release_old{false};
  int callback_entries{0};
  Params switch_params_;
  RTBuffer rt_buffer_;
  std::unique_ptr<RM> resource_manager_=std::make_unique<RM>();
  std::vector<ControllerSpec> specs;
  int activity_calls{0};
  struct Wrapper {
    std::vector<ControllerSpec> &specs;
    std::vector<ControllerSpec>& update_and_get_used_by_rt_list(){ return specs; }
  } rt_controllers_wrapper_{specs};
  struct Stats {void add_measurement(double) {}} periodicity_stats_;
  struct ExecTime {double read_time{};} execution_time_;
  controller_interface::return_type switch_controller_cb(const Names &names,
    const Names&,int,bool,int,std::string&) {
    std::unique_lock<std::mutex> l(sim_mu);
    ++callback_entries;
    if(ros2_control::has_item(names,"A_old_request")) {
      old_waiting=true;
      cv.notify_all();
      cv.wait(l,[&]{return release_old;});
      assert(switch_params_.ready_to_switch);
    }
    return controller_interface::return_type::OK;
  }
  void switch_controller_service_cb(const std::shared_ptr<Service::Request>,
                                    std::shared_ptr<Service::Response>);
  void perform_hardware_command_mode_change(const std::vector<ControllerSpec>&,
                                            const Names&,const Names&,const std::string&);
  void deactivate_controllers(std::vector<ControllerSpec>&s,const Names& names) {
    for(auto&v:s) if(ros2_control::has_item(names,v.info.name)) v.c->active=false;
  }
  void activate_controllers(std::vector<ControllerSpec>&s,const Names& names,int strict) {
    assert(strict==Service::Request::STRICT);
    for(auto&v:s) if(ros2_control::has_item(names,v.info.name)) v.c->active=true;
  }
  void publish_activity() {++activity_calls;}
  void manage_switch() {assert(false && "select non-ASAP placement only");}
  void read(const rclcpp::Time&,const rclcpp::Duration&);
  void one_tick();
};
#include "upstream.inc"
void ControllerManager::one_tick() {
  auto &rt_controller_list=specs;
  int period=1;
  auto ret=controller_interface::return_type::OK;
  rt_buffer_.deactivate_controllers_list.clear();
  // The mock supplies the chosen update result only when this selected native
  // skip guard allows the update. It has no chain or asynchronous controller.
  for(const auto &loaded_controller:rt_controller_list) {
#include "skip_guard.inc"
    if(!loaded_controller.c->active) continue;
    auto controller_ret=loaded_controller.c->error?controller_interface::return_type::ERROR:
        controller_interface::return_type::OK;
#include "collect_error.inc" 
  }
#include "update_tail.inc"
}
ControllerSpec spec(std::string n,Names fall,Names cmds,bool active,bool error=false) {
  return {{n,fall},std::make_shared<controller_manager::Ctrl>(
         controller_manager::Ctrl{cmds,active,error}),{n}};
}

void check(const std::string &scenario,bool overlaps,bool accepted,bool skip,bool hardware_reports=false) {
  ControllerManager c;
  c.resource_manager_->succeeds=accepted;
  if(hardware_reports) c.resource_manager_->failed_devices={"B_device"};
  c.switch_params_.deactivate_request={"A_drive"};
  if(skip) c.switch_params_.deactivate_request.push_back("B_drive");
  c.specs={spec("A_drive",{},{"a"},true), spec("B_drive",{"B_hold"},{"b"},true,true),
           spec("B_hold",{},overlaps?Names{"b","c"}:Names{"b"},false),
           spec("C_using",{},{"c"},true)};
  auto req=std::make_shared<Service::Request>();
  req->activate_controllers={"A_old_request"};
  auto resp=std::make_shared<Service::Response>();
  std::thread old([&]{c.switch_controller_service_cb(req,resp);});
  {
    std::unique_lock<std::mutex> l(c.sim_mu);
    c.cv.wait(l,[&]{return c.old_waiting;});
  }
  auto next=std::make_shared<Service::Request>();
  next->deactivate_controllers={"B_drive"};
  auto answer=std::make_shared<Service::Response>();
  std::promise<void> asked;
  auto asked_future=asked.get_future();
  std::thread later([&]{asked.set_value(); c.switch_controller_service_cb(next,answer);});
  asked_future.get();
  if(hardware_reports) c.read(rclcpp::Time{},rclcpp::Duration{});
  c.one_tick();
  assert(c.switch_params_.ready_to_switch);
  int entered;
  {
    std::lock_guard<std::mutex> l(c.sim_mu);
    entered=c.callback_entries;
  }
  bool a=c.specs[0].c->active, b=c.specs[1].c->active, hold=c.specs[2].c->active,
       other=c.specs[3].c->active;
  assert(entered==1 && a && b==(skip&&!hardware_reports) && hold==!skip && other==!overlaps);
  assert(c.resource_manager_->attempted==int(!skip||hardware_reports));
  assert(c.resource_manager_->accepted==int(accepted&&(!skip||hardware_reports)));
  assert(c.activity_calls==int(!skip));
  Names interfaces=skip?Names{}:overlaps?Names{"b","c"}:Names{"b"};
  assert(c.resource_manager_->starts==interfaces);
  assert(c.resource_manager_->stops==(hardware_reports?Names{"b"}:interfaces));
  {
    std::lock_guard<std::mutex> l(c.sim_mu);
    c.release_old=true;
    c.cv.notify_all();
  }
  old.join(); later.join();
  assert(c.callback_entries==2 && resp->ok && answer->ok);
  std::cout<<scenario<<' '<<entered<<' '<<b<<' '<<hold<<' '<<other<<' '
           <<c.resource_manager_->attempted<<' '<<c.resource_manager_->accepted<<'\n';
}
int main() {
  std::cout<<"case service_entries_at_cut B_drive B_hold C_active mode_attempts mode_accepted\n";
  check("separate_scopes",false,true,false);
  check("fallback_uses_C_interface",true,true,false);
  check("hardware_refuses",false,false,false);
  check("pending_switch_skips_B_update",false,true,true);
  check("pending_switch_with_B_read_error",false,true,true,true);
}
