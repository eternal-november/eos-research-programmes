#include <algorithm>
#include <cassert>
#include <cmath>
#include <condition_variable>
#include <functional>
#include <future>
#include <iostream>
#include <map>
#include <memory>
#include <mutex>
#include <string>
#include <thread>
#include <vector>
#define RCLCPP_DEBUG(...) ((void)0)
#define RCLCPP_ERROR(...) ((void)0)
#define RCLCPP_INFO(...) ((void)0)
#define RCLCPP_WARN_EXPRESSION(...) ((void)0)
#define RCL_CLOCK_UNINITIALIZED 0
using Names=std::vector<std::string>;
namespace rclcpp {
struct Duration {double seconds() const {return 0.01;} static Duration from_seconds(double) {return {};}};
struct Time {int get_clock_type()const{return 1;}};
Duration operator-(Time,Time){return {};}
struct Clock {Time now() const {return {};}};
}
namespace lifecycle_msgs::msg {
struct State {
  static constexpr int PRIMARY_STATE_UNCONFIGURED=1,PRIMARY_STATE_INACTIVE=2,
                       PRIMARY_STATE_ACTIVE=3,PRIMARY_STATE_FINALIZED=4;
};
}
namespace lifecycle_state_names {
constexpr const char *UNCONFIGURED="unconfigured", *INACTIVE="inactive",
                     *ACTIVE="active", *FINALIZED="finalized";
}
namespace rclcpp_lifecycle {
struct State {
  int value;std::string text;
  State(int a,const char*b):value(a),text(b){}
  int id()const{return value;}
  const auto&label()const{return text;}
};
}
enum class return_type {OK,ERROR,DEACTIVATE};
struct HardwareReadWriteStatus { return_type result{}; Names failed_hardware_names; };
struct Metrics {
  struct Stat {void update_statistics(int){}};
  Stat execution_time,periodicity;
};
struct Stopwatch {int execution_time{},periodicity{};};
struct Device {
  std::string name,group;
  std::shared_ptr<std::recursive_mutex> lock=std::make_shared<std::recursive_mutex>();
  return_type simulated_read{return_type::OK};
  int reads{},writes{},errors{};
  auto& get_mutex() {return *lock;}
  const auto& get_name() const {return name;}
  const auto& get_group_name() const {return group;}
  return_type read(rclcpp::Time,rclcpp::Duration){++reads;return simulated_read;}
  return_type write(rclcpp::Time,rclcpp::Duration){++writes;return return_type::OK;}
  rclcpp::Time get_last_read_time()const{return{};}
  rclcpp::Time get_last_write_time()const{return{};}
  const Stopwatch& get_read_statistics()const{static Stopwatch s;return s;}
  const Stopwatch& get_write_statistics()const{static Stopwatch s;return s;}
  void error(){++errors;}
};
using Actuator=Device; using System=Device; using Sensor=Device;
struct ResourceStorage {
  struct Info {double rw_rate{0};std::shared_ptr<Metrics> read_statistics,write_statistics;};
  std::map<std::string,Info> hardware_info_map_{{"A",{}},{"B",{}}};
  std::vector<Device> actuators_{{"A",""},{"B",""}}, sensors_,systems_;
  std::shared_ptr<rclcpp::Clock> clock=std::make_shared<rclcpp::Clock>();
  std::map<std::string,return_type> hw_group_state_;
  int cm_update_rate_{100},limiter_calls{};
  std::map<std::string,std::map<std::string,std::shared_ptr<int>>> joint_limiters_interface_{
    {"A",{{"a",std::make_shared<int>(1)}}},{"B",{{"b",std::make_shared<int>(1)}}}
  };
  std::mutex sim;
  std::condition_variable cv;
  bool in_transition{},release_transition{};
  Names removed;
  auto get_clock() {return clock;}
  void remove_all_hardware_interfaces_from_available_list(const std::string&s){removed.push_back(s);}
  bool enforce_command_limits(const std::string&,int,rclcpp::Duration){++limiter_calls;return true;}
  template<class Component> bool set_component_state(Component&,const rclcpp_lifecycle::State&) {
    std::unique_lock<std::mutex> l(sim);
    in_transition=true;
    cv.notify_all();
    cv.wait(l,[&]{return release_transition;});
    return true;
  }
#include "group.inc"
};
struct ResourceManager {
  HardwareReadWriteStatus read_write_status;
  std::unique_ptr<ResourceStorage> resource_storage_=std::make_unique<ResourceStorage>();
  std::recursive_mutex resources_lock_,joint_limiters_lock_;
  struct Params {bool handle_exceptions{true};} params_;
  bool return_failed_hardware_names_on_return_deactivate_write_cycle_{true};
  return_type set_component_state(const std::string&,rclcpp_lifecycle::State&);
  bool enforce_command_limits(const rclcpp::Duration&);
  HardwareReadWriteStatus read(const rclcpp::Time&,const rclcpp::Duration&);
  HardwareReadWriteStatus write(const rclcpp::Time&,const rclcpp::Duration&);
};
#include "manager.inc"
void show(std::string tag,const HardwareReadWriteStatus&r,const HardwareReadWriteStatus&w,
          const ResourceStorage&s,bool l){
  std::cout<<tag<<' '<<int(r.result)<<' '<<(r.failed_hardware_names.empty()?"-":r.failed_hardware_names.at(0))
      <<' '<<int(w.result)<<' '<<s.actuators_[0].reads<<' '<<s.actuators_[1].reads<<' '
      <<s.actuators_[0].writes<<' '<<s.actuators_[1].writes<<' '<<l<<' '<<s.limiter_calls<<'\n';
}
int main(){
  rclcpp::Time t;
  rclcpp::Duration period;
  std::cout<<"case read_result first_failure write_result A_reads B_reads A_writes B_writes limits_return limit_calls\n";
  {
    ResourceManager m;auto&s=*m.resource_storage_;
    auto r=m.read(t,period),w=m.write(t,period);auto l=m.enforce_command_limits(period);
    assert(r.result==return_type::OK&&w.result==return_type::OK&&l);
    assert(s.actuators_[0].reads==1&&s.actuators_[1].reads==1&&s.limiter_calls==2);
    show("ordinary_healthy_cycle",r,w,s,l);
  }
  {
    ResourceManager m;auto&s=*m.resource_storage_;
    s.actuators_[1].simulated_read=return_type::ERROR;
    rclcpp_lifecycle::State target(2,"inactive");
    std::thread th([&]{assert(m.set_component_state("A",target)==return_type::OK);});
    {
      std::unique_lock<std::mutex> l(s.sim);
      s.cv.wait(l,[&]{return s.in_transition;});
    }
    HardwareReadWriteStatus r,w;
    bool l=true;
    for(int j=0;j<3;++j){
      r=m.read(t,period);w=m.write(t,period);l=m.enforce_command_limits(period);
      assert(r.result==return_type::OK&&r.failed_hardware_names.empty());
      assert(w.result==return_type::OK&&w.failed_hardware_names.empty()&&!l);
    }
    assert(r.result==return_type::OK&&r.failed_hardware_names.empty());
    assert(w.result==return_type::OK&&w.failed_hardware_names.empty()&&!l);
    assert(s.actuators_[0].reads==0&&s.actuators_[1].reads==0&&s.actuators_[1].writes==0);
    show("A_transition_masks_B",r,w,s,l);
    {
      std::lock_guard<std::mutex> g(s.sim);
      s.release_transition=true;s.cv.notify_all();
    }
    th.join();
    r=m.read(t,period);
    assert(r.result==return_type::ERROR&&r.failed_hardware_names==Names{"B"});
    assert(s.removed==Names{"B"}&&s.actuators_[1].errors==1);
    std::cout<<"first_unlocked_read "<<int(r.result)<<' '<<r.failed_hardware_names.at(0)
             <<' '<<s.actuators_[0].reads<<' '<<s.actuators_[1].reads<<'\n';
  }
  {
    ResourceManager m;auto&s=*m.resource_storage_;
    s.actuators_[1].simulated_read=return_type::ERROR;
    std::promise<void> locked,done;auto lock_future=locked.get_future();auto done_future=done.get_future();
    std::thread th([&]{
      std::lock_guard<std::recursive_mutex> g(s.actuators_[0].get_mutex());
      locked.set_value();done_future.wait();
    });
    lock_future.get();
    auto r=m.read(t,period),w=m.write(t,period);auto l=m.enforce_command_limits(period);
    assert(r.result==return_type::ERROR&&r.failed_hardware_names==Names{"B"}&&l);
    assert(s.actuators_[0].reads==0&&s.actuators_[1].reads==1&&s.actuators_[1].writes==1);
    show("only_A_device_locked",r,w,s,l);
    done.set_value();th.join();
  }
}
