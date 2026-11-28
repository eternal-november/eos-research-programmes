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

void* setup_radio(int cap,double stamp);
int note_radio(void*,int,int,int,double);
int raw_radio(void*);
int charged_radio(void*);
int exact_old_progress(void*);
void end_radio(void*);

int main(){
 using Pair=std::pair<int,int>;
 const Pair early[2][5]={{{3,3},{2,2},{1,1},{0,0},{0,0}},
                         {{3,3},{2,2},{0,1},{0,1},{0,0}}};
 const Pair late[2][5]={{{3,3},{2,2},{1,2},{1,0},{0,0}},
                        {{3,3},{2,2},{1,2},{0,1},{0,0}}};
 for(int cap:{4,5})for(int gap:{7,8,9})for(int alternate:{0,1})
  for(int when:{0,1,2})for(int mode:{0,1,2})for(int budget:{8,9})for(int w:{0,1}){
   const int source=when==2?3:2;
   auto* r=setup_radio(cap,source-gap/8.);
   Wheel drive(false);
   int hint=-1,usable=-1,sum=0,turn=0,accepted_charge=-1;
   int l=4,h=4,early_choice=-1,late_choice=-1;
   auto notify=[&](int k){
    hint=note_radio(r,w,alternate,mode,source);
    if(hint>=0)usable=k;
    accepted_charge=charged_radio(r);
   };
   for(int i=0;i<5;i++){
    if(i==source&&when==0)notify(i);
    if(i==2)early_choice=hint;
    if(i==3)late_choice=hint;
    const Pair p=early_choice>=0?early[early_choice][i]:
                     budget==8?early[0][i]:late[late_choice>=0?late_choice:1][i];
    drive.receive((p.first+p.second)/2.,(p.second-p.first)/2.);
    drive.r.post();
    if(i==source&&when!=0)notify(i+1);
    // Only the native pre-update writes can reach the fixture plant.
    drive.r.pre();
    const auto [x,y]=drive.out();
    assert(x==p.first&&y==p.second);
    assert(l>=x&&h>=y&&l-x<=(w==0?1:2)&&h-y<=(w==1?1:2));
    sum+=l+h+x+y;turn+=h+y-l-x;l=x;h=y;
   }
   assert(l==0&&h==0&&sum<=4*budget&&exact_old_progress(r)==1);
   std::cout<<cap<<" "<<gap<<" "<<alternate<<" "<<when<<" "<<mode<<" "<<budget<<" "<<w
            <<" "<<raw_radio(r)<<" "<<usable<<" "<<accepted_charge<<" "<<sum<<" "<<turn<<"\n";
   end_radio(r);
  }
}
