#include <algorithm>
#include <cassert>
#include <cmath>
#include <iostream>
#include <map>
#include <memory>
#include <string>
#include <vector>
namespace rmf_door_msgs::msg {
struct Time {
  int sec=0, nanosec=0;
  bool operator==(Time const&) const=default;
};
struct DoorMode {
  enum {MODE_OPEN=1,MODE_CLOSED,MODE_MOVING};
  int value=0;
  bool operator==(DoorMode const&) const=default;
};
struct DoorState {
  using SharedPtr=std::shared_ptr<DoorState>;
  std::string door_name;
  Time door_time;
  DoorMode current_mode;
  bool operator==(DoorState const&) const=default;
};
struct Session {std::string requester_id;Time request_time;};
struct DoorSessions {
  std::string door_name;
  std::vector<Session> sessions;
};
struct SupervisorHeartbeat {
  using SharedPtr=std::shared_ptr<SupervisorHeartbeat>;
  std::vector<DoorSessions> all_sessions;
  Time time;
};
}
using namespace rmf_door_msgs::msg;
using Entity=int;
const Entity kNullEntity=0;
#define gzwarn std::cerr
namespace components {
struct JointPosition {
 std::vector<double> data;
 const std::vector<double>& Data() const {return data;}
};
}
struct EntityComponentManager {
 std::map<std::pair<Entity,std::string>,Entity> names;
 std::map<Entity,components::JointPosition> positions;
 Entity ParentEntity(Entity) const {return 20;}
 template<class T> const T* Component(Entity j) const {
    return &positions.at(j);
 }
};
struct Model {
 Entity id;
 Model(Entity x):id(x){}
 Entity JointByName(const EntityComponentManager& cm,const std::string& name) const {
    const auto x=cm.names.find({id,name});
    return x==cm.names.end()?kNullEntity:x->second;
 }
};
enum class DoorModeCmp {OPEN,CLOSE,MOVING};
struct DoorData {
 struct Joint {std::string name;double open_position,closed_position;};
 struct Params {double dx_min;};
 std::vector<Joint> joints;
 Params params;
};
struct Publisher {
  DoorState record;
  void publish(DoorState s){record=std::move(s);}
};
struct Gz {
  Publisher sink,*_door_state_pub=&sink;
JOINT_SRC
WITHIN_SRC
MODE_SRC
PUBLISH_SRC
};
struct LegacyTask {
 struct StatusMsg {
  enum {STATE_ACTIVE,STATE_COMPLETED};
  int state=STATE_ACTIVE;
  std::string status;
 };
};
struct DoorOpen {struct ActivePhase {
 std::string _door_name="gate",_request_id="crew";
 LegacyTask::StatusMsg _status;
 void _update_status(const DoorState::SharedPtr&,const SupervisorHeartbeat::SharedPtr&);
};};
SESSION_SRC
UPDATE_SRC

bool phase(const DoorState& report,const SupervisorHeartbeat& hb){
 DoorOpen::ActivePhase p;
 p._update_status(std::make_shared<DoorState>(report),std::make_shared<SupervisorHeartbeat>(hb));
 return p._status.state==LegacyTask::StatusMsg::STATE_COMPLETED;
}
bool exact_known_open(const Gz&gz,Entity e,const EntityComponentManager& cm,const DoorData& door){
  if(door.joints.empty()) return false;
  for(const auto&j:door.joints){
    const auto id=gz.get_joint_entity(cm,e,j.name);
    if(id==kNullEntity || !gz.is_joint_at_position(
        cm.Component<components::JointPosition>(id)->Data()[0],door.params.dx_min,j.open_position))
      return false;
  }
  return true;
}
int main(){
  Gz gz;
  EntityComponentManager complete, hidden, narrow, none, nested;
  const DoorData two{{{"left",1.,0.},{"right",1.,0.}},{.02}};
  complete.names={{{10,"left"},1},{{10,"right"},2}};
  complete.positions={{1,{{1.}}},{2,{{1.}}}};
  narrow=complete;
  narrow.positions.at(2).data[0]=0.;
  hidden=narrow; // oracle keeps the obstructing right leaf in the fixture
  hidden.names.erase({10,"right"}); // job cannot resolve it by name
  nested=complete;
  nested.names.erase({10,"right"});
  nested.names[{20,"right"}]=2;
  const SupervisorHeartbeat hb={{{"gate",{{"crew",{8,0}}}}},{9,0}};
  auto sample=[&](EntityComponentManager& cm,double t) {
    const auto mode=gz.get_current_mode(10,cm,two);
    gz.publish_state(t,"gate",mode);
    return gz.sink.record;
  };
  const auto a=sample(complete,9),b=sample(hidden,9),c=sample(narrow,9);
  assert(a==b && b.current_mode.value==DoorMode::MODE_OPEN);
  assert(c.current_mode.value==DoorMode::MODE_MOVING);
  assert(phase(a,hb) && phase(b,hb) && !phase(c,hb));
  assert(exact_known_open(gz,10,complete,two));
  assert(!exact_known_open(gz,10,hidden,two));
  assert(!exact_known_open(gz,10,narrow,two));
  assert(sample(nested,9)==a);
  // Compare an empty declared list separately; missing joints remain explicit.
  DoorData empty{{},{.02}};
  assert(gz.get_current_mode(10,none,empty)==DoorModeCmp::OPEN);
  assert(!exact_known_open(gz,10,none,empty));
  const auto old=sample(complete,2);
  assert(phase(old,hb) && !phase(c,hb));
  const SupervisorHeartbeat no_session={{},{9,0}};
  assert(!phase(a,no_session));
  // The next missing-joint call is a repeat, not hidden by our wrapper.
  assert(sample(hidden,9)==a);
  std::cout<<"visible open vs unresolved closed leaf: same OPEN report and phase completion\n";
  std::cout<<"visible closed control not OPEN; parent lookup resolves nested visible leaf\n";
  std::cout<<"empty configured list returns OPEN; complete-leaf guard refuses\n";
  std::cout<<"old fully open report plus new matching session completes; no session does not\n";
}
