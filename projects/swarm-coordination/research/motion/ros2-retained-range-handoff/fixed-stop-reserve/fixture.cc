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
double demand(JointSaturationLimiter<JointControlInterfacesData>& n,double x,double d){
 JointControlInterfacesData actual,desired;
 actual.position=x;actual.velocity=n.prev_command_.velocity.value_or(0);
 desired.velocity=d;
 n.on_enforce(actual,desired,{1});
 return desired.velocity.value();
}
double reserve(double p,double r){
 double s=0;
 for(double u=std::max(0.,p-r);u>0;u=std::max(0.,u-r))s+=u;
 return s;
}
int main(){
 // A constant configured range, without a live reconfiguration.
 for(int W=4;W<=40;++W)for(int R=1;R<=4;++R)for(int D=1;D<=10;++D)
 for(int gate:{0,1}){
  JointSaturationLimiter<JointControlInterfacesData> n;
  n.joint_limits_[0].max_position=W;
  n.joint_limits_[0].max_velocity=15;
  n.joint_limits_[0].max_acceleration=R;
  double x=0;
  std::cout<<W<<" "<<R<<" "<<D<<" "<<gate;
  for(int k=0;k<12;++k){
   const double p=n.prev_command_.velocity.value_or(0.);
   double d=D;
   if(gate){
    int best=-1;
    for(int u=0;u<=15;u++)
       if(std::abs(u-p)<=R&&u+reserve(u,R)<=W-x)
            best=u;
    assert(best>=0);
    int lowest=std::max(0,int(p)-R);
    d=std::clamp(int(d),lowest,best);
   }
   double u=demand(n,x,d);
   std::cout<<" "<<u;
   if(u<0||x+u>W||std::abs(u-p)>R){std::cout<<" E";break;}
   x+=u;
  }
  std::cout<<"\n";
 }
 // Interior request at the first empty intersection.
 JointSaturationLimiter<JointControlInterfacesData> n;
 n.joint_limits_[0].max_position=7;
 double x=0;
 for(double d:{1.,2.,3.}) x+=demand(n,x,d);
 assert(x==6.&&demand(n,x,1.5)==1.5);
}
