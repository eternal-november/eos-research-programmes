#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cmath>
#include <iostream>
#include <map>
#include <memory>
#include <vector>
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
struct Work {
 int totals{};
 std::array<int,3> em{};
 std::array<int,3> first{};
 void done(int id,int cost){
    totals+=cost;
    if(em[id]++==0)first[id]=totals;
 }
};
struct Sensor {
 struct State{
  double updateRate=20;
  gz::common::Time nextUpdateTime;
 } data,*dataPtr=&data;
 Work* work;
 int role,cost;
 Sensor(Work* w,int r,int c,bool due):work(w),role(r),cost(c) {
   data.nextUpdateTime=gz::common::Time::N(due?0:1000000);
 }
 bool EnableMetrics(){return false;}
 void PublishMetrics(std::chrono::duration<double>){assert(false);}
 bool Update(const gz::common::Time&){work->done(role,cost);return true;}
 bool Update(const gz::common::Time&,bool);
 const auto& next()const{return data.nextUpdateTime;}
};
using SensorId=int;
struct Manager {
 struct State{std::map<SensorId,std::unique_ptr<::Sensor>> sensors;};
 State owned,*dataPtr=&owned;
 ::Sensor* Sensor(SensorId);
 void RunOnce(const gz::common::Time&,bool);
};
#include "selected.inc"

int main(){
 int tests=0,forces=0,duplicates=0,ready_only=0;
 std::array<int,3> ids{0,1,2};
 const auto now=gz::common::Time::N(0);
 do{
  for (int mask=0;mask<8;++mask)
  for (int code=0;code<8;++code) {
    std::array<bool,3> due{};std::array<int,3> cost{};
    int budget=0;
    for(int i=0;i<3;++i){
      due[i]=(mask>>i)&1;cost[i]=1+((code>>i)&1);
      if(i==0||due[i])budget+=cost[i];
    }
    for(int strategy=0;strategy<4;++strategy){
      Work w;Manager m;
      for(int i=0;i<3;++i)m.owned.sensors.emplace(ids[i],std::make_unique<Sensor>(&w,i,cost[i],due[i]));
      assert(m.Sensor(3)==nullptr);
      const auto initial=m.Sensor(ids[0])->next().ns;
      if(strategy==0)m.RunOnce(now,false);
      if(strategy==1)m.RunOnce(now,true);
      if(strategy==2){m.RunOnce(now,false);if(w.em[0]==0)m.Sensor(ids[0])->Update(now,true);}
      if(strategy==3){m.Sensor(ids[0])->Update(now,true);m.RunOnce(now,false);}
      for(int i=0;i<3;++i)assert(w.em[i]>0||!due[i]);
      if(strategy==0)assert(w.em[0]==int(due[0]));
      if(strategy==1){
        assert((w.em==std::array<int,3>{1,1,1}));
        forces+=w.totals>budget;
        int latest=w.first[0];
        for(int i=1;i<3;++i)if(due[i])latest=std::max(latest,w.first[i]);
        if(latest<=budget&&w.totals>budget)++ready_only;
      }
      if(strategy==2)assert(w.totals==budget&&w.em[0]==1&&w.em[1]==int(due[1])&&w.em[2]==int(due[2]));
      if(strategy==3){assert(w.em[0]==1+int(due[0]));duplicates+=due[0];}
      // The forced call does not consume a nominal due slot.
      assert(m.Sensor(ids[0])->next().ns==initial+
                        (due[0]&&strategy!=1?50000000:0));
      ++tests;
    }
  }
 }while(std::next_permutation(ids.begin(),ids.end()));
 std::cout<<tests<<" selected gate and manager cases\n"<<forces<<" wide calls exceeded the minimal return-bound workload\n"
      <<ready_only<<" of these still supply the named data by the budget via early callbacks\n"
      <<duplicates<<" unconditional targeted-before-regular duplicates\n";
}
