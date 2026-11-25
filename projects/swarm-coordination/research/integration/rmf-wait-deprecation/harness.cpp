#include <iostream>
#include <chrono>
#include <cassert>
#include <memory>
#include <functional>
#include <unordered_map>
#include <vector>
#include <map>
#include <mutex>
#include <optional>
#include <cstdint>
#include "rmf_utils/Modular.hpp"
namespace rmf_utils {
template<class T> auto make_unique_impl() {return std::make_unique<T>();}
}
namespace rmf_traffic {
namespace schedule {
using ParticipantId=uint64_t;
using PlanId=uint64_t;
using RouteId=uint64_t;
using CheckpointId=uint64_t;
struct Dependency {
 ParticipantId on_participant; PlanId on_plan; RouteId on_route;
 CheckpointId on_checkpoint;
};
struct ItineraryViewer {
 struct DependencySubscription {
   class Implementation;
   std::unique_ptr<Implementation> _pimpl;
   bool reached() const;
   bool deprecated() const;
   bool finished() const;
   Dependency dependency() const;
 };
};
}
namespace time {
template<class T> double to_seconds(T t) {return std::chrono::duration<double>(t).count();}
}
}
#include "schema.inc"
#include "tracker.inc"
namespace rmf_traffic {
namespace schedule {
#include "viewer.inc"
struct Mirror {
 using DependencySubscription=ItineraryViewer::DependencySubscription;
 struct State {
  PlanId current_plan_id=4;
  std::vector<int> storage={1};
  struct {std::vector<CheckpointId> reached_checkpoints={0};} progress;
 };
 struct Imp {
  std::unordered_map<ParticipantId,State> states={{1,{}}};
  DependencyTracker dependencies;
 };
 std::unique_ptr<Imp> _pimpl=std::make_unique<Imp>();
 DependencySubscription watch_dependency(Dependency,std::function<void()>,std::function<void()>) const;
 // These are controlled state/tracker inputs, not Mirror::update or Database execution.
 void report(ParticipantId p,PlanId plan,CheckpointId checkpoint)
 {
  if (_pimpl->states.at(p).current_plan_id==plan)
    _pimpl->states.at(p).progress.reached_checkpoints[0]=checkpoint;
  _pimpl->dependencies.reached(p,plan,{checkpoint});
 }
 void replace(ParticipantId p)
 {
  auto& s=_pimpl->states.at(p);
  ++s.current_plan_id;
  s.progress.reached_checkpoints={0};
  _pimpl->dependencies.deprecate_dependencies_before(p,s.current_plan_id);
 }
 void clear(ParticipantId p)
 {
  auto& s=_pimpl->states.at(p);
  s.storage.clear();
  _pimpl->dependencies.deprecate_dependencies_before(p,s.current_plan_id+1);
 }
};
#include "watch.inc"
}
}
#undef RCLCPP_INFO
#define RCLCPP_INFO(...) ((void)0)
#define RCLCPP_WARN(...) ((void)0)
namespace example {
using namespace rmf_traffic::schedule;
using Clock=std::chrono::steady_clock;
enum class Status{Waiting,Completed,Delayed};
struct Logger { void info(const char*) {} };
struct State {
 Status status=Status::Waiting;
 void update_status(Status s) {status=s;}
 Logger update_log() {return {};}
};
struct Context {
 Clock::time_point t{};
 std::optional<Clock::duration> delay;
 size_t replans=0, adjustments=0;
 Clock::time_point now() {return t;}
 Context& itinerary() {return *this;}
 auto cumulative_delay(PlanId) {return delay;}
 void cumulative_delay(PlanId, Clock::duration d, std::chrono::milliseconds) {delay=d;++adjustments;}
};
struct WaitForTraffic {
 struct Active {
  std::optional<Clock::time_point> _decision_made;
  std::vector<Mirror::DependencySubscription> _dependencies;
  std::shared_ptr<State> _state=std::make_shared<State>();
  std::shared_ptr<Context> _context=std::make_shared<Context>();
  Clock::time_point _expected_time{};
  PlanId _plan_id=70;
  int completed=0;
  std::function<void()> _finished=[this]{++completed;};
  void _replan(){++_context->replans;}
  void _consider_going();
 };
};
#include "wait.inc"
}
using namespace rmf_traffic::schedule;
using example::WaitForTraffic;
using example::Status;

static void events(Mirror& m, int x)
{
 if(x==1)m.report(1,4,1);
 if(x==2)m.report(1,4,3);
 if(x==3)m.replace(1);
 if(x==4)m.clear(1);
 if(x==5)m.report(1,5,3);
}
int main()
{
 size_t checked=0, earlies=0, latest=0, dep=0, after=0;
 for(int x=0;x<6;++x) for(int y=0;y<6;++y) for(int z=0;z<6;++z)
 for(int checkpoint=1;checkpoint<=4;++checkpoint)
 for(int route=0;route<=1;++route) for(int initial=0;initial<2;++initial)
 {
  Mirror m; WaitForTraffic::Active wait; int r=0,d=0;
  Dependency key{1,4,uint64_t(route),uint64_t(checkpoint)};
  if(initial)m.report(1,4,2);
  auto callbacks=[&](){return m.watch_dependency(key,[&]{++r;},[&]{++d;});};
  wait._dependencies.emplace_back(callbacks());
  const bool immediate=initial&&route==0&&checkpoint<=2;
  bool reached=immediate, deprecated=false, older=false, empty=false;
  int reported=initial?2:0;
  for(int k : {x,y,z})
  {
   events(m,k);
   if(!reached&&!deprecated)
   {
    if(k==3||k==4)deprecated=true;
    else if(route==0 && ((k==1&&checkpoint<=1)||(k==2&&checkpoint<=3)))reached=true;
   }
   older|=k==3;
   empty|=k==4;
   if(k==1||k==2)reported=k==1?1:3; // last asserted value in this harness, not Database merge
   assert(wait._dependencies.front().reached()==reached);
   assert(wait._dependencies.front().deprecated()==deprecated);
  }
  wait._consider_going();
  assert(wait.completed==int(reached || deprecated));
  assert(r==int(reached) && d==int(deprecated));
  auto late=callbacks();
  assert(late.deprecated()==(older||empty));
  assert(late.reached()==(!older&&!empty&&route==0&&reported>=checkpoint));
  earlies+=reached; dep+=deprecated;
  latest+=late.reached(); after+=reached&&late.deprecated();
  ++checked;
 }
 std::cout<<"status / callback / receiver cases "<<checked<<"\n"
          <<"early reached "<<earlies<<" early deprecated "<<dep<<"\n"
          <<"late reached "<<latest<<" earlier reached and late deprecated "<<after<<"\n";
 // Replacement alone can finish this wait; an unrelated unresolved dependency
 // keeps it waiting; its own live timeout is a distinct reason to request replan.
 {
  Mirror m;
  m._pimpl->states.emplace(2,Mirror::State{});
  WaitForTraffic::Active w;
  for(int p : {1,2})w._dependencies.push_back(m.watch_dependency({uint64_t(p),4,0,1},[]{},[]{}));
  m.replace(1);
  w._context->t+=std::chrono::seconds(30);
  w._context->delay=std::chrono::seconds(0);
  w._consider_going();
  assert(w.completed==0 && w._context->replans==0 && w._context->adjustments==1);
  w._context->t+=std::chrono::milliseconds(1);
  w._consider_going();
  assert(w.completed==0 && w._context->replans==1 && w._state->status==Status::Delayed);
 }
 {
  Mirror m;
  WaitForTraffic::Active w;
  w._dependencies.push_back(m.watch_dependency({1,4,0,3},[]{},[]{}));
  m.replace(1);
  w._context->t+=std::chrono::seconds(31);
  w._consider_going();
  assert(w.completed==1 && w._context->replans==0 && !w._dependencies.front().reached());
 }
 std::cout<<"multi-participant and timeout controls passed\n";
}
