#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <string>
#include <vector>
#define RCLCPP_DEBUG(...) ((void)0)

void ck(bool v){if(!v)std::abort();}
namespace std_msgs::msg {
struct Bool {using ConstSharedPtr=std::shared_ptr<const Bool>; bool data=false;};
}
namespace geometry_msgs::msg {
struct Twist {using ConstSharedPtr=std::shared_ptr<const Twist>; int source=0;};
}
struct Time {double t;double seconds()const{return t;}};
struct LockTopicHandle;
struct VelocityTopicHandle;
struct TwistMux{
  double clock=0;
  std::shared_ptr<std::vector<LockTopicHandle>> lock_hs_;
  std::shared_ptr<std::vector<VelocityTopicHandle>> velocity_hs_;
  std::vector<int> emitted;
  Time now()const{return Time{clock};}
  void publishTwist(geometry_msgs::msg::Twist::ConstSharedPtr m){emitted.push_back(m->source);}
  int getLockPriority();
  bool hasPriority(const VelocityTopicHandle&);
};
template <class T> struct Base {
  using priority_type=int;
  TwistMux* mux_;
  std::string name_;
  Time timeout_,stamp_;
  int priority_;
  T msg_{};
  int getPriority()const{return priority_;}
  const T& getMessage()const{return msg_;}
  const auto& getName()const{return name_;}
#include "expiry.inc"
};
struct LockTopicHandle:Base<std_msgs::msg::Bool> {
#include "lock.inc"
  LockTopicHandle(TwistMux* m,int p,int timeout,int stamp,bool state):
    Base{m,"lock",Time{double(timeout)},Time{double(stamp)},p,std_msgs::msg::Bool{state}}{}
};
struct VelocityTopicHandle:Base<geometry_msgs::msg::Twist>{
#include "movement.inc"
  VelocityTopicHandle(TwistMux* m,int p,const std::string& name,int timeout,int stamp):
    Base{m,name,Time{double(timeout)},Time{double(stamp)},p,{}}{}
};
#include "mux.inc"

int main(){
  int trials=0;
  for(int pa=1;pa<=4;++pa)for(int pb=1;pb<=4;++pb)
  for(int p=1;p<=4;++p)for(int other=1;other<=4;++other)
  for(int age=0;age<=2;++age)for(int timeout=0;timeout<=2;++timeout)
  for(int state=0;state<4;++state)for(bool competing:{false,true}){
    TwistMux m; m.clock=3;
    m.lock_hs_=std::make_shared<std::vector<LockTopicHandle>>();
    m.velocity_hs_=std::make_shared<std::vector<VelocityTopicHandle>>();
    auto& a=*m.lock_hs_; auto& v=*m.velocity_hs_;
    a.emplace_back(&m,pa,timeout,3-age,state&1);
    a.emplace_back(&m,pb,0,0,state&2);
    v.emplace_back(&m,p,"subject",1,0);
    v.emplace_back(&m,other,"other",1,competing?3:0);
    auto th=std::max((state&1)||(timeout>0&&age>timeout)?pa:0,(state&2)?pb:0);
    const bool should_emit=p>=th&&!(competing&&other>=th&&other>p);
    v[0].callback(std::make_shared<const geometry_msgs::msg::Twist>(geometry_msgs::msg::Twist{7}));
    ck(m.getLockPriority()==th);
    ck(m.emitted.size()==unsigned(should_emit));
    if(should_emit)ck(m.emitted[0]==7);
    // An observed lock changes gate state, not necessarily a motor command.
    auto old=m.emitted.size();
    a[0].callback(std::make_shared<const std_msgs::msg::Bool>(std_msgs::msg::Bool{true}));
    ck(m.emitted.size()==old);
    ++trials;
  }
  int tail_tests=0;
  for(int timeout=0;timeout<=5;++timeout)
  for(int delay=0;delay<=5;++delay)for(int period=1;period<=5;++period)
  for(int block=0;block<=3;++block){
    TwistMux m; m.clock=0;
    m.lock_hs_=std::make_shared<std::vector<LockTopicHandle>>();
    m.velocity_hs_=std::make_shared<std::vector<VelocityTopicHandle>>();
    if(block)m.lock_hs_->emplace_back(&m,block,0,0,true);
    auto& v=*m.velocity_hs_;
    v.emplace_back(&m,1,"replacement",1,0);
    v.emplace_back(&m,2,"incumbent",timeout,0);
    v[1].callback(std::make_shared<const geometry_msgs::msg::Twist>(geometry_msgs::msg::Twist{8}));
    auto old=m.emitted.size();
    int first=-1;
    for(int t=delay;t<=25;t+=period){
      m.clock=t;
      v[0].callback(std::make_shared<const geometry_msgs::msg::Twist>(geometry_msgs::msg::Twist{7}));
      if(m.emitted.size()>old){first=t;ck(m.emitted.back()==7);break;}
    }
    int expected=-1;
    if(block<=1 && timeout>0) {
      expected=delay;
      while(expected<=timeout)expected+=period;
    }
    ck(first==expected);
    ++tail_tests;
  }
  std::cout<<"retired producer with cached priority vs direct publication cutoff "<<tail_tests<<" cases\n";
  std::cout<<"native gate/callback vs direct threshold "<<trials<<" cases\n";
}
