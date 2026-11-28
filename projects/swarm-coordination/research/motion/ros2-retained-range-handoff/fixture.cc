#include <algorithm>
#include <cassert>
#include <cmath>
#include <iostream>
#include <limits>
#include <mutex>
#include <optional>
#include <string>
#include <vector>
#define RCLCPP_WARN_EXPRESSION(...) ((void)0)
#define RCLCPP_ERROR_ONCE(...) ((void)0)
namespace rclcpp {struct Duration{ double t; double seconds()const{return t;} };}
namespace joint_limits {
struct JointLimits {
 bool has_position_limits=true,has_velocity_limits=true,has_acceleration_limits=true;
 double min_position=-8,max_position=8,max_velocity=8,max_acceleration=1,max_jerk=1;
};
struct VelocityLimits { double lower_limit,upper_limit; VelocityLimits(double l,double h):lower_limit(l),upper_limit(h){} };
using PositionLimits=VelocityLimits;using AccelerationLimits=VelocityLimits;using EffortLimits=VelocityLimits;
// Unused in the velocity-only slice.
template<class... Args> PositionLimits compute_position_limits(Args&&...){assert(false);return {0,0};}
template<class... Args> EffortLimits compute_effort_limits(Args&&...){assert(false);return {0,0};}
template<class... Args> AccelerationLimits compute_acceleration_limits(Args&&...){assert(false);return {0,0};}
struct JointControlInterfacesData{
 std::optional<double> position,velocity,effort,acceleration,jerk;
 std::string joint_name;
 bool has_position()const{return position.has_value();}
 bool has_velocity()const{return velocity.has_value();}
 bool has_effort()const{return effort.has_value();}
 bool has_acceleration()const{return acceleration.has_value();}
 bool has_jerk()const{return jerk.has_value();}
 bool has_data()const{return has_position()||has_velocity()||has_effort()||has_acceleration()||has_jerk();}
};
template<class T> struct JointSaturationLimiter{
 std::mutex mutex_;
 std::vector<JointLimits> joint_limits_{JointLimits{}};
 std::vector<std::string> joint_names_{"joint"};
 T prev_command_;
 bool on_enforce(const T&,T&,const rclcpp::Duration&);
};
namespace internal { constexpr double POSITION_BOUNDS_TOLERANCE=0.01; }
#include "slice.inc"
}
using namespace joint_limits;
int main(){
 for(int p=-6;p<=6;++p) for(int v=-3;v<=3;++v) for(int maxp=0;maxp<=5;++maxp)
 for(int r=1;r<=3;++r) for(int cmd=-6;cmd<=6;++cmd) for(int mode:{0,1,2}){
  JointSaturationLimiter<JointControlInterfacesData> node;
  JointControlInterfacesData before,request,actual,desired;
  before.position=0;before.velocity=p;request.velocity=p;
  node.on_enforce(before,request,{1});
  assert(request.velocity==p);
  if(mode!=0)node.prev_command_=JointControlInterfacesData{};
  actual.position=0; if(mode!=2)actual.velocity=v;
  desired.velocity=cmd;
  auto &limits=node.joint_limits_[0];limits.max_position=maxp;limits.max_acceleration=r;
  bool clamped=node.on_enforce(actual,desired,{1});
  std::cout<<p<<" "<<v<<" "<<maxp<<" "<<r<<" "<<cmd<<" "<<mode<<" "
   <<desired.velocity.value()<<" "<<clamped<<"\n";
 }
}
