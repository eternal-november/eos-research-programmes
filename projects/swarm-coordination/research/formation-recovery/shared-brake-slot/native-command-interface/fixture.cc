#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cmath>
#include <iostream>
#include <limits>
#include <map>
#include <memory>
#include <mutex>
#include <string>
#include <vector>
#include <type_traits>
#define IGN_FP_VOLATILE volatile
#define IGN_PROFILE(s) ((void)0)
#define ignwarn std::cerr

namespace ignition { namespace math {} }
namespace gz = ignition;
namespace ignition::math {
#include "native_helpers.inc"
struct Vector3d { double x, y, z; };
}
#include "native_limiter_decl.inc"
#include "native_limiter.inc"

namespace msgs {
struct Vec {
  double a{}, b{}, c{};
  double x() const { return a; }
  double z() const { return c; }
};
struct Twist {
  Vec L, A;
  const Vec &linear() const { return L; }
  const Vec &angular() const { return A; }
  Vec *mutable_linear() { return &L; }
  Vec *mutable_angular() { return &A; }
};
struct Boolean { bool b; bool data() const { return b; } };
void Set(Vec *out, const gz::math::Vector3d &v) { *out = {v.x,v.y,v.z}; }
}
using Entity = int;
constexpr int kNullEntity = -1;
namespace components {
struct JointVelocityCmd {
  explicit JointVelocityCmd(const std::vector<double>& v): data(v) {}
  std::vector<double> data;
};
struct JointPosition {};
}
struct EntityComponentManager {
  std::map<Entity, components::JointVelocityCmd> jointVelocityCommands;
  std::map<Entity, components::JointPosition> positions;
  bool HasEntity(Entity e) const { return e == 1 || e == 2; }
  template<class C> auto &table() {
    if constexpr (std::is_same_v<C, components::JointPosition>) return positions;
    else return jointVelocityCommands;
  }
  template<class C> C *Component(Entity e) {
    auto &t = table<C>();
    auto i = t.find(e);
    return i == t.end() ? nullptr : &i->second;
  }
  template<class C> void CreateComponent(Entity e, C c) { table<C>().emplace(e,c); }
};
struct UpdateInfo {
  std::chrono::steady_clock::duration dt{std::chrono::seconds(1)};
  bool paused{};
};
#include "native_commands.inc"
struct DiffDrivePrivate {
  void OnCmdVel(const msgs::Twist &);
  void OnEnable(const msgs::Boolean &);
  void UpdateVelocity(const UpdateInfo &, const EntityComponentManager &);
  void UpdateOdometry(const UpdateInfo &, const EntityComponentManager &) {}
  struct { Entity JointByName(EntityComponentManager &, const std::string &) const {
    return kNullEntity;
  } } model;
  std::vector<Entity> leftJoints{1}, rightJoints{2};
  std::vector<std::string> leftJointNames, rightJointNames;
  double leftJointSpeed{}, rightJointSpeed{}, wheelSeparation{1}, wheelRadius{.2};
  std::unique_ptr<math::SpeedLimiter> limiterLin{new math::SpeedLimiter};
  std::unique_ptr<math::SpeedLimiter> limiterAng{new math::SpeedLimiter};
  Commands last0Cmd, last1Cmd;
  msgs::Twist targetVel;
  bool enabled{true};
  std::mutex mutex;
};
struct DiffDrive {
  std::unique_ptr<DiffDrivePrivate> dataPtr{new DiffDrivePrivate};
  void PreUpdate(const UpdateInfo &, EntityComponentManager &);
  void PostUpdate(const UpdateInfo &, const EntityComponentManager &);
};
#include "native_drive.inc"

struct Run {
  DiffDrive dd;
  EntityComponentManager e;
  UpdateInfo info;
  DiffDrivePrivate &state() { return *dd.dataPtr; }
  explicit Run(bool limited = true) {
    if (limited) {
      auto &l = *state().limiterLin;
      l.SetMinVelocity(0); l.SetMaxVelocity(8);
      l.SetMinAcceleration(-2); l.SetMaxAcceleration(2);
      l.SetMinJerk(-1); l.SetMaxJerk(1);
    }
  }
  void set(double v) { state().OnCmdVel({{v,0,0},{0,0,0}}); }
  void disable() { state().OnEnable({false}); }
  void enable() { state().OnEnable({true}); }
  void pre() { dd.PreUpdate(info,e); }
  void post() { dd.PostUpdate(info,e); }
  void cycle() { pre(); post(); }
  int output() {
    auto val = e.jointVelocityCommands.at(1).data.at(0);
    assert(val == e.jointVelocityCommands.at(2).data.at(0));
    return static_cast<int>(std::lround(val * state().wheelRadius));
  }
};

int main() {
  // All examples are reached from cold state by ordinary commands.
  Run up, flat, down;
  up.set(8);
  for (int t=0;t<3;++t) up.cycle(); // 1,3,5
  flat.set(5);
  for (int t=0;t<8;++t) flat.cycle();
  down.set(8);
  for (int t=0;t<8;++t) down.cycle();
  down.set(0);
  down.cycle(); down.cycle(); // 7,5
  for (Run *r : {&up,&flat,&down}) {
    r->pre();
    assert(r->output()==5);
    r->disable();
    assert(r->state().targetVel.linear().x()==0);
    assert(!r->state().enabled);
    assert(r->output()==5);
    r->post();
    assert(r->output()==5);
    r->pre();
  }
  assert(up.output()==6 && flat.output()==4 && down.output()==3);
  std::cout<<"same applied command, then explicit disable: rising=6 steady=4 falling=3\n";

  Run keepUp, keepDown, keepFlat, unlimited;
  keepUp.set(8);
  for(int t=0;t<3;++t) keepUp.cycle();
  keepUp.cycle(); keepUp.pre();
  assert(keepUp.output()==7);
  keepDown.set(8);
  for(int t=0;t<8;++t) keepDown.cycle();
  keepDown.set(0); keepDown.cycle(); keepDown.cycle();
  keepDown.cycle(); keepDown.pre();
  assert(keepDown.output()==3);
  keepFlat.set(5);
  for(int t=0;t<8;++t) keepFlat.cycle();
  keepFlat.pre();
  assert(keepFlat.output()==5);
  std::cout<<"omitted replacement callback: rising=7 steady=5 falling=3\n";

  Run immediate(false), late(false), paused;
  for (Run *r : {&immediate,&late}) { r->set(5); r->cycle(); r->pre(); }
  immediate.disable(); immediate.post(); immediate.pre();
  late.post(); late.disable(); late.pre();
  assert(immediate.output()==0 && late.output()==5);
  late.post(); late.pre(); assert(late.output()==0);
  paused.set(8);
  for(int t=0;t<3;++t) paused.cycle();
  paused.pre(); paused.info.paused=true; paused.disable();
  paused.cycle(); paused.cycle();
  assert(paused.output()==5 && paused.state().last1Cmd.lin==3);
  paused.info.paused=false; paused.pre(); assert(paused.output()==5);
  paused.post(); paused.pre(); assert(paused.output()==6);
  std::cout<<"unlimited early/late disable: 0 versus 5 at next write; pause preserves history\n";

  unsigned count=0;
  // Differential replay of the scalar recurrence for fixed dt=1, no reverse,
  // velocity [0,8], acceleration +/-2, jerk +/-1, and straight commands.
  // These state rows are an exhaustive finite superset, not a reachability claim.
  for (int p=0;p<=8;++p) for (int q=0;q<=8;++q) {
    if (std::abs(p-q)>2) continue;
    for (int u=0;u<=8;++u) for (int event=0;event<4;++event)
      for (bool paused : {false,true}) {
      Run r;
      r.state().last0Cmd.lin=p; r.state().last1Cmd.lin=q;
      r.state().leftJointSpeed=r.state().rightJointSpeed=p/r.state().wheelRadius;
      r.pre();
      r.set(u);
      r.info.paused=paused;
      if (event==1) r.set(0);
      if (event==2) { r.disable(); r.set(8); }
      if (event==3) r.set(8);
      const int target=event==3 ? 8 : (event==0 ? u : 0);
      const int lo=std::max(-2,p-q-1), hi=std::min(2,p-q+1);
      int expected=std::max(0,std::min(8,std::max(p+lo,std::min(target,p+hi))));
      r.post();
      assert(r.output()==p);
      r.pre();
      assert(r.output()==(paused ? p : expected));
      assert(r.state().last1Cmd.lin==(paused ? q : p));
      assert(r.state().last0Cmd.lin==(paused ? p : expected));
      assert(r.state().targetVel.linear().x()==target);
      ++count;
    }
  }
  std::cout<<count<<" exhaustive straight-channel comparisons including pause\n";
  auto longer_step = [](int plateau, int descend, int seconds) {
    Run r;
    r.set(plateau);
    for (int t=0;t<8;++t) r.cycle();
    r.set(0);
    for (int t=0;t<descend;++t) r.cycle();
    r.pre();
    assert(r.output()==0 && r.state().last1Cmd.lin==(plateau==8 ? 1 : 2));
    r.info.dt=std::chrono::seconds(seconds);
    r.set(8); r.post(); r.pre();
    return r.output();
  };
  assert(longer_step(8,5,1)==0 && longer_step(5,3,1)==0);
  assert(longer_step(8,5,2)==3 && longer_step(5,3,2)==2);
  std::cout<<"fixed-step-equivalent histories: 0 versus 0 at dt=1, 3 versus 2 at dt=2\n";

  auto step = [](int p, int q, int requested) {
    Run r;
    r.state().last0Cmd.lin=p; r.state().last1Cmd.lin=q;
    r.set(requested); r.post(); r.pre();
    return r.output();
  };
  unsigned pairs=0, matches=0, separates=0;
  for (int p=0;p<=8;++p) for (int q=0;q<=8;++q) for (int z=q+1;z<=8;++z) {
    if (std::abs(p-q)>2 || std::abs(p-z)>2) continue;
    const auto rangeQ=std::pair{step(p,q,0),step(p,q,8)};
    const auto rangeZ=std::pair{step(p,z,0),step(p,z,8)};
    bool same=true;
    for (int u=0;u<=8;++u) same = (step(p,q,u)==step(p,z,u)) && same;
    assert(same==(rangeQ==rangeZ));
    ++pairs;
    same ? ++matches : ++separates;
  }
  std::cout<<pairs<<" history pairs at equal p: "<<matches<<" can collapse, "
           <<separates<<" separated by an endpoint command\n";
}
