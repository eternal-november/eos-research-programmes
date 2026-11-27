#include <algorithm>
#include <array>
#include <assert.h>
#include <chrono>
#include <cmath>
#include <condition_variable>
#include <cstdint>
#include <iostream>
#include <map>
#include <memory>
#include <mutex>
#include <set>
#include <utility>
#include <vector>
#define IGN_PROFILE(...) ((void)0)
auto& igndbg=std::cerr;
auto& ignwarn=std::cerr;
namespace gz::common {
struct Time {
 long long ns{};
 Time()=default;
 explicit Time(double seconds):ns(std::llround(seconds*1e9)){}
 Time(long long sec,long long nsec):ns(sec*1000000000+nsec){}
 auto operator+(const Time& o)const{return Time(0,ns+o.ns);}
 auto& operator+=(const Time& o){ns+=o.ns;return *this;}
 bool operator<(const Time& o)const{return ns<o.ns;}
 bool operator<=(const Time& o)const{return ns<=o.ns;}
 double Double()const{return ns/1e9;}
};
}
namespace common=gz::common;
namespace math {
auto durationToSecNsec(std::chrono::nanoseconds n){return std::pair{0LL,n.count()};}
}
namespace sensors {
using SensorId=int;
struct Sensor {
 struct State{double updateRate=20;common::Time nextUpdateTime;};
 State state,*dataPtr=&state;
 std::vector<long long> captures;
 explicit Sensor(long long due){state.nextUpdateTime=common::Time(0,due);}
 virtual ~Sensor()=default;
 double UpdateRate()const{return state.updateRate;}
 SensorId Id()const{return id;}
 SensorId id{};
 bool EnableMetrics()const{return false;}
 void PublishMetrics(std::chrono::duration<double>){assert(false);}
 bool Update(const common::Time& now){captures.push_back(now.ns);return true;}
 bool Update(const common::Time&,bool);
 common::Time NextUpdateTime()const;
};
struct RenderingSensor:Sensor{using Sensor::Sensor;};
struct Manager {
 struct State{std::map<SensorId,std::unique_ptr<::sensors::Sensor>> sensors;};
 State owned,*dataPtr=&owned;
 ::sensors::Sensor* Sensor(SensorId);
 void RunOnce(const common::Time&,bool=false);
};
}
using sensors::Sensor;
using sensors::SensorId;
using sensors::Manager;
namespace components {
struct Camera{static constexpr int typeId=0;};
using DepthCamera=Camera;using GpuLidar=Camera;using RgbdCamera=Camera;using ThermalCamera=Camera;
}
namespace events {struct PreRender{};struct PostRender{};}
struct EventManager {template<class T>void Emit(){}};
struct Scene{int calls=0;void PreRender(){++calls;}};
struct UpdateInfo{std::chrono::nanoseconds dt{0},simTime{0};};
struct EntityComponentManager{bool HasComponentType(int)const{return false;}};
struct RenderUtil{
 int pending{},calls{};
 void Update(){++calls;}
 void UpdateFromECM(const UpdateInfo&,const EntityComponentManager&){}
 int PendingSensors()const{return pending;}
};
struct SensorsPrivate {
 std::mutex renderMutex,sensorMaskMutex;
 std::condition_variable renderCv;
 bool running=true,initialized=true,updateAvailable=false,doInit=false;
 RenderUtil renderUtil;
 Scene ownedScene,*scene=&ownedScene;
 EventManager ownEventManager,*eventManager=&ownEventManager;
 std::vector<sensors::RenderingSensor*> activeSensors;
 std::map<SensorId,common::Time> sensorMask;
 std::set<SensorId> sensorIds;
 Manager sensorManager;
 common::Time updateTime;
 void RunOnce();
};
struct Sensors {
 SensorsPrivate owned,*dataPtr=&owned;
 void PostUpdate(const UpdateInfo&,const EntityComponentManager&);
};
#include "selected.inc"

constexpr long long ms=1000000, origin=1000*ms, q=origin+10*ms, late=q+ms, early=q-ms, period=50*ms;
struct Case {
 Sensors system;
 void make(int id,long long t){
   auto s=std::make_unique<sensors::RenderingSensor>(t);
   s->id=id;
   system.owned.sensorManager.owned.sensors.emplace(id,std::move(s));
   system.owned.sensorIds.insert(id);
 }
 Sensor& get(int id){return *system.owned.sensorManager.Sensor(id);}
 void tick(long long t,bool pending=false){
   system.owned.renderUtil.pending=pending;
   UpdateInfo info;info.simTime=std::chrono::nanoseconds(t);
   system.PostUpdate(info,{});
   if(system.owned.updateAvailable)system.owned.RunOnce();
 }
 long long mask(int id){return system.owned.sensorMask.at(id).ns;}
};
struct Outcome{int earlyA,lateA,oldB,renderPasses;long long aNext,aMask;};
Outcome witness(bool bDue,bool cDue,bool pending){
 Case x;
 x.make(0,origin-48*ms);
 x.make(1,bDue?late:late+period);
 x.make(2,cDue?early:late+period);
 x.tick(origin);
 assert(x.mask(0)==origin+45*ms && x.get(0).NextUpdateTime().ns==origin+2*ms);
 x.tick(early,pending);
 x.tick(late,pending);
 auto count=[&](int i,long long t){const auto& v=x.get(i).captures;return int(std::count(v.begin(),v.end(),t));};
 return {count(0,early),count(0,late),count(1,late),x.system.owned.ownedScene.calls,x.get(0).NextUpdateTime().ns,x.mask(0)};
}
int main(){
 for(bool b:{false,true})for(bool c:{false,true})for(bool p:{false,true}){
   auto r=witness(b,c,p);
   assert(r.earlyA==int(c)&&r.lateA==int(b&&!c)&&r.oldB==int(b));
   assert(r.renderPasses==1+int(b)+int(c));
   assert(r.aMask==origin+45*ms);
   assert(r.aNext==origin+2*ms+(b||c?period:0));
 }
 int runs=0, ticks=0, nontriggered=0, atExpiry=0, atDue=0;
 std::vector<int> ids{0,1,2};
 const std::vector<long long> times{origin,origin+2*ms,early,q,late,origin+45*ms-1,origin+45*ms,origin+52*ms,origin+90*ms,origin+95*ms};
 const std::vector<long long> shifts{-100*ms,-50*ms,-48*ms,-40*ms,0,1,10*ms,45*ms,52*ms,100*ms};
 do {
  for(long long aa:shifts)for(long long bb:shifts)for(long long cc:shifts)for(int pp=0;pp<4;++pp){
    Case x;
    const std::array<long long,3> shifts3{aa,bb,cc};
    std::array<long long,3> next{};
    std::array<long long,3> masks{};
    std::array<std::vector<long long>,3> captures;
    int renders=0,sceneUpdates=0;
    for(int i=0;i<3;++i){
      next[i]=origin+shifts3[i];
      x.make(ids[i],next[i]);
    }
    int tickNum=0;
    for(long long t:times){
      bool pending=bool(pp & (1<<(tickNum++%2)));
      // Independent oracle: union of unmasked due wake times; membership in
      // the regular manager is not membership in this union.
      std::array<bool,3> witness{};
      for(int i=0;i<3;++i){
        if(masks[i]==t)++atExpiry;
        if(next[i]==t)++atDue;
        witness[i]=(next[i]<=t && masks[i]<=t);
      }
      bool render=witness[0]||witness[1]||witness[2];
      sceneUpdates+=render||pending;
      if(render){
        ++renders;
        for(int i=0;i<3;++i)if(next[i]<=t){
          captures[i].push_back(t);next[i]+=period;
          nontriggered+=!witness[i];
        }
      }
      for(int i=0;i<3;++i)if(witness[i])masks[i]=t+45*ms;
      x.tick(t,pending);
      assert(x.system.owned.ownedScene.calls==renders);
      assert(x.system.owned.renderUtil.calls==sceneUpdates);
      for(int i=0;i<3;++i){
        auto& s=x.get(ids[i]);
        assert(s.captures==captures[i]&&s.NextUpdateTime().ns==next[i]);
        const auto& m=x.system.owned.sensorMask;
        assert(masks[i]>t ? m.at(ids[i]).ns==masks[i] : m.count(ids[i])==0);
      }
      ++ticks;
    }
    ++runs;
  }
 }while(std::next_permutation(ids.begin(),ids.end()));
 std::cout<<runs<<" source traces, "<<ticks<<" tick comparisons\n"
          <<nontriggered<<" regular updates of sensors outside the active set\n"
          <<atExpiry<<" exact mask-expiry checks, "<<atDue<<" exact nominal-due checks\n"
          <<"Old B triggers a useful A frame at q+1 ms with or without a pending scene update\n"
          <<"One optional capture trigger at q-1 ms consumes that A slot but preserves old B\n";
}
