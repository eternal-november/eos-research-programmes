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

struct Wheel {
 Run r{false};
 explicit Wheel(bool box){
  r.state().wheelRadius=1;
  r.state().wheelSeparation=2;
  cmd(4,0);
  if(box) {
   for (auto *limiter : {r.state().limiterLin.get(),r.state().limiterAng.get()}){
    limiter->SetMinAcceleration(-1.);
    limiter->SetMaxAcceleration(1.);
   }
  }
 }
 std::pair<double,double> out(){
  return {r.e.jointVelocityCommands.at(1).data.at(0),r.e.jointVelocityCommands.at(2).data.at(0)};
 }
 void receive(double v, double z) { r.state().OnCmdVel({{v,0,0},{0,0,z}}); }
 void cmd(double v, double z){
  receive(v,z);
  r.post();r.pre();
 }
};
int main(){
 Wheel separate(true);
 separate.receive(3,1);
 separate.r.pre();
 assert(separate.out()==std::make_pair(4.,4.)); // hasn't consumed latest target
 separate.r.post(); separate.r.pre();
 assert(separate.out()==std::make_pair(2.,4.)); // two independent scalar bounds passed
 Wheel coupled(true);
 coupled.cmd(3.5,.5);
 assert(coupled.out()==std::make_pair(3.,4.));
 int cases=0,writes=0;
 int w,d;
 while(std::cin>>w>>d){
  assert((w==0||w==1)&&d>=0&&d<=3);
  const int weak=1,strong=2;
  Wheel c(false);
  int l=4,r=4,ls=0,rs=0;
  for(int t=0;t<5;t++){
   int a,b;assert(std::cin>>a>>b);
   assert(a>=0&&b>=0&&a<=l&&b<=r);
   assert(l-a<=(w==0?weak:strong)&&r-b<=(w==1?weak:strong));
   c.cmd((a+b)/2.,(b-a)/2.);
   const auto [outL,outR]=c.out();
   assert(outL==a&&outR==b);
   ls+=l+a;rs+=r+b;l=a;r=b;++writes;
  }
  assert(l==0&&r==0&&rs-ls==(w==0?0:4));
  assert(ls+rs<=(d==3?36:32));
  ++cases;
 }
 assert(cases==8&&writes==40);
 std::cout<<cases<<" stopping profiles, "<<writes<<" native paired wheel writes\n";
 std::cout<<"scalar-axis controlled request outputs (2,4); coupled compatible request (3,4)\n";
}
