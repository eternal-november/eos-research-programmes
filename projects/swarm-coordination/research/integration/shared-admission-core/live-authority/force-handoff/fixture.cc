#include <map>
#include <memory>
#include <set>
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


using ComponentTypeId=int;
using ComponentId=int;
using ComponentKey=std::pair<ComponentTypeId,ComponentId>;
class NativeStore {
public:
  struct ForceStorage {
    EntityComponentManager *ecm;
    void Remove(ComponentId id) {
      assert(id==1);
      ecm->force.reset();
    }
  };
  struct Data {
    std::map<int,std::unique_ptr<ForceStorage>> components;
    std::map<int,std::map<int,int>> entityComponents;
    std::set<ComponentKey> oneTimeChangedComponents,periodicChangedComponents;
    bool entityComponentsDirty{};
  };
  std::unique_ptr<Data> dataPtr{new Data};
  EntityComponentManager ecm;
  static constexpr ComponentTypeId effort=7;
  NativeStore() {dataPtr->components.emplace(effort,std::make_unique<ForceStorage>(ForceStorage{&ecm}));}
  void afterWriter() {
    assert(ecm.force);
    dataPtr->entityComponents[1][effort]=1;
  }
  bool HasEntity(Entity e) const {return e==1;}
  void UpdateViews(Entity) {} // caches not consumed in this selected fixture
  bool RemoveComponent(Entity,const ComponentTypeId&);
  bool RemoveComponent(Entity,const ComponentKey&);
  bool EntityHasComponent(Entity,const ComponentKey&) const;
  ComponentId EntityComponentIdFromType(Entity,ComponentTypeId) const;
};
#include "native_remove.inc"

struct Stage {
  void (*fn)();
  void PreUpdate(int, int) {fn();}
  void Update(int, int) {fn();}
};
struct Barrier {void Wait(){}};
struct SimulationRunner {
  std::vector<Stage*> systemsPreupdate, systemsUpdate;
  int currentInfo{},entityCompMgr{};
  Barrier *postUpdateStartBarrier{}, *postUpdateStopBarrier{};
  void UpdateSystems();
};
#include "native_runner.inc"

struct Trial {
  NativeStore p;
  EntityComponentManager q, side;
  ApplyJointForce old;
  PhysicsChoice ep,eq,es;
  UpdateInfo info;
  bool runWriter, lateWriter;
  bool backup, installP;
  int release; // 0 none, 1 before Pre writers, 2 inline before Physics
  bool removeAck{};
  void prior(bool perform) {
    if (perform) {
      old.data.OnCmdForce({4.});
      old.PreUpdate(info,p.ecm);p.afterWriter();
      ep.apply(p.ecm);ep.clean(p.ecm);
    }
  }
  void clear() {removeAck=p.RemoveComponent(1,p.effort);}
  void writer() {
    if(runWriter){
      old.data.OnCmdForce({4.});
      old.PreUpdate(info,p.ecm);p.afterWriter();
    }
  }
  void velocities() {
    if(installP) p.ecm.CreateComponent(1,components::JointVelocityCmd({5.}));
    if(backup) q.CreateComponent(1,components::JointVelocityCmd({6.}));
    side.CreateComponent(1,components::JointVelocityCmd({2.}));
  }
  void apply() {
    ep.apply(p.ecm);eq.apply(q);es.apply(side);
    ep.clean(p.ecm);eq.clean(q);es.clean(side);
  }
};
Trial *current{};
Stage early{[]{if (current->release==1) current->clear();}};
Stage writer{[]{current->writer();}};
Stage cmds{[]{current->velocities();}};
Stage inlineRelease{[]{if (current->release==2) current->clear();}};
Stage recreate{[]{if(current->lateWriter) current->writer();}};
Stage physics{[]{current->apply();}};

int main(){
  std::cout<<"prior,writer,release,installP,backup,late,ack,past,pforce,pvel,qvel,side\n";
  for(bool prior:{false,true})for(bool writerActive:{false,true})
    for(int release=0;release<3;++release)for(bool ip:{false,true})for(bool backup:{false,true})
      for(bool late:{false,true}){
      if(late && !(prior && writerActive && release==2 && ip && !backup)) continue;
      Trial r;
      r.runWriter=writerActive;r.backup=backup;r.release=release;r.installP=ip;r.lateWriter=late;
      r.prior(prior);
      const bool past=r.ep.joint.calls==std::vector<std::string>{"force:4.000000"};
      assert(past==prior);
      r.ep.joint.calls.clear();
      current=&r;
      SimulationRunner sim{{&early,&writer,&cmds},{&inlineRelease,&recreate,&physics}};
      sim.UpdateSystems();
      auto has=[](const Joint &j,const std::string &s){
        return std::find(j.calls.begin(),j.calls.end(),s)!=j.calls.end();
      };
      bool of=has(r.ep.joint,"force:4.000000"),pv=has(r.ep.joint,"velocity:5.000000");
      bool qv=has(r.eq.joint,"velocity:6.000000"),iv=has(r.es.joint,"velocity:2.000000");
      assert(iv && qv==backup && !(of&&pv));
      std::cout<<prior<<','<<writerActive<<','<<release<<','<<ip<<','<<backup<<','<<late<<','<<r.removeAck
        <<','<<past<<','<<of<<','<<pv<<','<<qv<<','<<iv<<'\n';
    }
}
