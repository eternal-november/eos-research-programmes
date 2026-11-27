#include <cassert>
#include <chrono>
#include <cmath>
#include <iostream>
#define IGN_PROFILE(...) ((void)0)
namespace gz::common {
struct Time {
 long long ns{};
 Time()=default;
 explicit Time(double s):ns(std::llround(s*1000000000.0)){}
 static Time N(long long v){Time t;t.ns=v;return t;}
 bool operator<(const Time& o)const{return ns<o.ns;}
 Time& operator+=(const Time& t){ns+=t.ns;return *this;}
 double Double()const{return double(ns)/1000000000.;}
};
}
struct Sensor {
 struct State {
    gz::common::Time nextUpdateTime;
    double updateRate=20;
 } data,*dataPtr=&data;
 unsigned receives{};
 bool EnableMetrics(){return false;}
 void PublishMetrics(std::chrono::duration<double>){assert(false);}
 bool Update(const gz::common::Time&){++receives;return true;}
 bool Update(const gz::common::Time&,bool);
};
#include "native.inc"
int main(){
  int phase,force;
  while(std::cin>>phase>>force){
    Sensor s;
    s.data.nextUpdateTime=gz::common::Time::N(phase);
    // Candidate nominal ticks are offered from a synthetic exact clock.
    int captured=-1;
    for(int i=0;i<=50000000;i+=50000){
      if(s.Update(gz::common::Time::N(i),force&&i==0)){captured=i;break;}
    }
    assert(captured>=0&&s.receives==1);
    std::cout<<captured<<' '<<s.data.nextUpdateTime.ns<<'\n';
  }
}
