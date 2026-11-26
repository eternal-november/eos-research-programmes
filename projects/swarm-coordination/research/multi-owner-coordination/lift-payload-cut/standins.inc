#include <cassert>
#include <iostream>
#include <map>
#include <memory>
#include <optional>
#include <sstream>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>
#define RCLCPP_INFO(...) ((void)0)
static std::ostringstream gzwarn;
using Entity = int;
constexpr Entity kNullEntity=0;
namespace gz::math {
struct Vector3d {
  double x{},y{},z{};
  bool operator==(const Vector3d&) const = default;
};
Vector3d operator+(Vector3d p,Vector3d q) {return {p.x+q.x,p.y+q.y,p.z+q.z};}
Vector3d operator-(Vector3d p,Vector3d q) {return {p.x-q.x,p.y-q.y,p.z-q.z};}
struct AxisAlignedBox {
  Vector3d l,r;
  bool Contains(Vector3d p) const {return l.x<=p.x&&p.x<=r.x&&l.y<=p.y&&p.y<=r.y&&l.z<=p.z&&p.z<=r.z;}
  AxisAlignedBox operator+(Vector3d d) const {return {l+d,r+d};}
};
}
struct Pos {
  gz::math::Vector3d p;
  auto PosVal() const {return p;}
  auto CoordPositionSub(Pos q) const {return p-q.p;}
};
struct PoseData : Pos {
  auto Pos() const {return p;}
};
struct LiftRequest {
  using UniquePtr=std::unique_ptr<LiftRequest>;
  enum {REQUEST_END_SESSION=0,REQUEST_AGV_MODE=1,DOOR_CLOSED=0,DOOR_OPEN=2};
  std::string lift_name="L",session_id,destination_floor="A";
  int request_time=0,request_type=REQUEST_AGV_MODE,door_state=DOOR_CLOSED;
  bool operator==(const LiftRequest&) const=default;
};
struct LiftState {
  using UniquePtr=std::unique_ptr<LiftState>;
  enum{MODE_AGV=1,MOTION_STOPPED=0};
  std::vector<std::string> available_floors;
  std::string lift_name="L",session_id,current_floor,destination_floor;
  int door_state=0,motion_state=0,current_mode=0;
  bool operator==(const LiftState&) const=default;
};
struct Pub {
  std::vector<LiftRequest> sent;
  void publish(const LiftRequest& r){sent.push_back(r);}
};
namespace rmf_fleet_adapter::lift_supervisor {
struct Node{
  std::map<std::string,LiftRequest::UniquePtr> _active_sessions;
  std::shared_ptr<Pub> _lift_request_pub=std::make_shared<Pub>();
  int clock=0;
  int now(){return ++clock;}
  void _adapter_lift_request_update(LiftRequest::UniquePtr);
  void _lift_state_update(LiftState::UniquePtr);
};
}
enum class DoorModeCmp {OPEN,CLOSE};
struct LiftCommand {
  int request_type=LiftRequest::REQUEST_AGV_MODE;
  std::string destination_floor="A",session_id="";
  DoorModeCmp door_state=DoorModeCmp::CLOSE;
};
struct LiftData {
  std::map<std::string,int> floors{{"A",0},{"B",1}};
};
namespace components{
template<class T> struct Box {
  T val{};
  Box()=default;
  explicit Box(T v):val(v){}
  T& Data(){return val;}
  const T& Data()const{return val;}
};
struct Lift : Box<LiftData>{};
struct LiftCmd : Box<LiftCommand>{using Box::Box;};
struct Pose : Box<PoseData>{using Box::Box;};
struct Model {};
struct LinearVelocityCmd : Box<std::vector<double>> {
  LinearVelocityCmd():Box({0,0,0}){}
  int TypeId() const{return 1;}
};
}
struct EntityComponentManager {
  components::Lift lift;
  std::optional<components::LiftCmd> active;
  components::Model model;
  std::map<Entity,components::Pose> poses;
  std::map<Entity,components::LinearVelocityCmd> vels;
  template<class T> T* Component(Entity e) {
    if constexpr(std::is_same_v<T,components::Lift>) return e==1?&lift:nullptr;
    else if constexpr(std::is_same_v<T,components::LiftCmd>) return e==1&&active ? &*active : nullptr;
    else if constexpr(std::is_same_v<T,components::Pose>) return &poses.at(e);
    else if constexpr(std::is_same_v<T,components::LinearVelocityCmd>) return &vels.at(e);
  }
  template<class T> void CreateComponent(Entity e,const T& v){assert(e==1);active=v;}
  template<class M,class P,class Fn> void Each(Fn f) {
    for (const auto& [e,p]:poses) assert(f(e,&model,&p));
  }
  bool EntityHasComponentType(Entity e,int key) const {assert(key==1);return vels.count(e)>0;}
};
struct LiftPlugin {
  std::map<Entity,PoseData> _initial_poses;
  std::map<Entity,gz::math::AxisAlignedBox> _initial_aabbs;
  std::map<Entity,LiftCommand> _last_lift_command;
  static Entity entity_by_name(EntityComponentManager&,const std::string& n){return n=="L"?1:kNullEntity;}
  std::vector<Entity> get_payloads(EntityComponentManager&,const Entity&);
  LiftState get_current_state(const Entity&,EntityComponentManager&,const LiftData&,const components::LiftCmd*);
  void apply(EntityComponentManager*,LiftRequest::UniquePtr);
  void velocity(EntityComponentManager&,const Entity&,double);
  std::vector<std::string> get_available_floors(const LiftData& x) {std::vector<std::string> r;for(auto& [n,_]:x.floors)r.push_back(n);return r;}
  std::string get_current_floor(Entity,EntityComponentManager&,const LiftData&){return "A";}
  int get_door_state(Entity,EntityComponentManager&,const LiftData&){return LiftState::MOTION_STOPPED;}
  int get_motion_state(Entity,EntityComponentManager&,const LiftData&,std::string floor){return floor!="A";}
};
