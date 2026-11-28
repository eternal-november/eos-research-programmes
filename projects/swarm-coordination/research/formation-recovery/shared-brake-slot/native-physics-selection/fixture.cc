#include <algorithm>
#include <cassert>
#include <chrono>
#include <cstddef>
#include <iostream>
#include <mutex>
#include <optional>
#include <string>
#include <type_traits>
#include <vector>
#define IGN_PROFILE(s) ((void)0)
#define ignwarn std::cerr
using Entity = int;
constexpr Entity kNullEntity = -1;
namespace components {
template<class Tag> struct Vec {
  explicit Vec(const std::vector<double>& v) : data(v) {}
  std::vector<double> data;
  auto &Data() {return data;}
  const auto &Data() const {return data;}
};
struct FR; struct VC; struct VR; struct PR;
using JointForceCmd=Vec<FR>; using JointVelocityCmd=Vec<VC>;
using JointVelocityReset=Vec<VR>; using JointPositionReset=Vec<PR>;
struct Name { std::string Data() const {return "test joint";} };
}
struct EntityComponentManager {
  std::optional<components::JointForceCmd> force;
  std::optional<components::JointVelocityCmd> velocity;
  std::optional<components::JointVelocityReset> reset;
  std::optional<components::JointPositionReset> position;
  template<class C> auto &slot() {
    if constexpr(std::is_same_v<C,components::JointForceCmd>) return force;
    else if constexpr(std::is_same_v<C,components::JointVelocityCmd>) return velocity;
    else if constexpr(std::is_same_v<C,components::JointVelocityReset>) return reset;
    else return position;
  }
  template<class C> C *Component(Entity) {
    auto &v=slot<C>(); return v ? &*v : nullptr;
  }
  template<class C> void CreateComponent(Entity e,C c) { assert(e==1);slot<C>()=c; }
  template<class C, class CB> void Each(CB cb) {
    if (auto p=Component<C>(1)) cb(1,p);
  }
};
struct UpdateInfo {
  std::chrono::steady_clock::duration dt{std::chrono::seconds(1)};
  bool paused{};
};
namespace msgs { struct Double {double x; double data() const {return x;} }; }
struct ApplyJointForcePrivate {
  Entity jointEntity{1};
  struct {Entity JointByName(EntityComponentManager&,const std::string&) {return 1;}} model;
  std::string jointName{"test joint"};
  std::mutex jointForceCmdMutex;
  double jointForceCmd{0};
  void OnCmdForce(const msgs::Double &);
};
struct ApplyJointForce {
  ApplyJointForcePrivate data;
  ApplyJointForcePrivate *dataPtr{&data};
  void PreUpdate(const UpdateInfo &,EntityComponentManager &);
};
#include "force_writer.inc"

struct Joint {
  std::vector<std::string> calls;
  std::size_t GetDegreesOfFreedom() const {return 1;}
  void SetVelocity(std::size_t i,double v) {assert(i==0);calls.push_back("reset:"+std::to_string(v));}
  void SetForce(std::size_t i,double v) {assert(i==0);calls.push_back("force:"+std::to_string(v));}
  void SetVelocityCommand(std::size_t i,double v) {assert(i==0);calls.push_back("velocity:"+std::to_string(v));}
  void SetPosition(std::size_t i,double v) {assert(i==0);calls.push_back("position:"+std::to_string(v));}
};
struct JointVelocityCommandFeatureList {};
struct PhysicsChoice {
  Joint joint;
  struct {
    Joint *j;
    bool supports{true};
    template<class F> Joint *EntityCast(Entity) {return supports ? j : nullptr;}
  } entityJointMap{&joint};
  bool apply(EntityComponentManager &_ecm) {
    Entity _entity=1;
    components::Name name;
    const auto *_name=&name;
    auto *jointPhys=&joint;
#include "physics_choice.inc"
  }
  void clean(EntityComponentManager &_ecm) {
#include "physics_clean.inc"
  }
};

int main() {
  EntityComponentManager a,b,c;
  ApplyJointForce writer;
  PhysicsChoice pa,pb,pc;

  // One world has the stock force writer; without any received command it
  // already leaves a zero-valued component. The other world lacks the writer.
  UpdateInfo info;
  writer.PreUpdate(info,b);
  assert(b.force && b.force->Data()==std::vector{0.});
  a.CreateComponent(1,components::JointVelocityCmd({5.}));
  b.CreateComponent(1,components::JointVelocityCmd({5.}));
  assert(a.velocity->Data()==b.velocity->Data());
  pa.apply(a); pb.apply(b);
  assert(pa.joint.calls==std::vector<std::string>{"velocity:5.000000"});
  assert(pb.joint.calls==std::vector<std::string>{"force:0.000000"});
  std::cout<<"same velocity command: native branch emits velocity 5 without force component, force 0 with it\n";

  // A distinct earlier force command reaches its authorized source. Cleanup
  // zeroes its data; do not call the writer again in the serial replacement test.
  writer.data.OnCmdForce({4.});
  writer.PreUpdate(info,c);
  assert(c.force->Data()==std::vector{4.});
  pc.apply(c);
  assert(pc.joint.calls.back()=="force:4.000000");
  pc.clean(c);
  for(int k=0;k<10;++k) {
    c.CreateComponent(1,components::JointVelocityCmd({5.}));
    pc.apply(c); pc.clean(c);
    assert(c.force && c.force->Data()==std::vector{0.});
    assert(c.velocity && c.velocity->Data()==std::vector{0.});
    assert(pc.joint.calls.back()=="force:0.000000");
  }
  // Explicit component removal is a fixture intervention, not a proven
  // stock handoff operation or cancellation of a backend actuator.
  c.force.reset();
  c.CreateComponent(1,components::JointVelocityCmd({5.}));
  pc.apply(c);
  assert(pc.joint.calls.back()=="velocity:5.000000");
  std::cout<<"ten post-cleanup writes still shadowed; explicit fixture removal restores dispatch\n";

  c.reset.emplace(std::vector{2.});
  pc.apply(c);
  assert(pc.joint.calls.back()=="reset:2.000000");
  c.reset.reset();
  pc.entityJointMap.supports=false;
  const auto before=pc.joint.calls.size();
  pc.apply(c);
  assert(pc.joint.calls.size()==before);
  std::cout<<"reset suppresses velocity; missing backend feature also suppresses it\n";
  int combinations=0;
  for(int f=0;f<4;++f) for (int z=0;z<3;++z) for(int v=0;v<3;++v)
    for(bool supported : {false,true}) {
      EntityComponentManager e;
      PhysicsChoice p;
      p.entityJointMap.supports=supported;
      if(f==1) e.force.emplace(std::vector<double>{});
      if(f>=2) e.force.emplace(std::vector{f==2?0.:4.});
      if(z==1) e.reset.emplace(std::vector<double>{});
      if(z==2) e.reset.emplace(std::vector{2.});
      if(v==1) e.velocity.emplace(std::vector<double>{});
      if(v==2) e.velocity.emplace(std::vector{5.});
      p.apply(e);
      std::vector<std::string> expected;
      if(z==2) expected.push_back("reset:2.000000");
      if(f>=2) expected.push_back(f==2 ? "force:0.000000" : "force:4.000000");
      if(f==0 && z==0 && v==2 && supported) expected.push_back("velocity:5.000000");
      assert(expected==p.joint.calls);
      p.clean(e);
      assert(e.force.has_value()==(f!=0));
      if (f>=2) assert(e.force->Data()==std::vector{0.});
      ++combinations;
    }
  std::cout<<combinations<<" combinations of presence, payload and backend capability\n";
}
