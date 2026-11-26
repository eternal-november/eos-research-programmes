#include <cassert>
#include <cstddef>
#include <deque>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

namespace Eigen {
struct Vector2d {
  double xx,yy;
  double x() const {return xx;}
  double y() const {return yy;}
  Vector2d operator-(Vector2d b) const {return {xx-b.xx,yy-b.yy};}
  double dot(Vector2d b) const {return xx*b.xx+yy*b.yy;}
};
struct Vector3d {double x,y,z;};
}
struct Waypoint {
  std::size_t i;
  Eigen::Vector2d p;
  auto index() const {return i;}
  auto get_location() const {return p;}
};
struct LaneEnd {
  std::size_t i;
  auto waypoint_index() const {return i;}
};
struct Lane {
  std::size_t i,a,b;
  LaneEnd entry() const {return {a};}
  LaneEnd exit() const {return {b};}
  auto index() const {return i;}
};
struct Graph {
  std::vector<Waypoint> wp{{0,{0,0}},{1,{10,0}},{2,{20,0}}};
  std::vector<Lane> lanes{{0,0,1},{1,1,0},{2,1,2},{3,2,0}};
  const auto& get_waypoint(std::size_t n) const {return wp.at(n);}
  const auto& get_lane(std::size_t n) const {return lanes.at(n);}
  const Lane* lane_from(std::size_t a,std::size_t b) const {
    for (const auto& l:lanes) if (l.a==a && l.b==b) return &l;
    return nullptr;
  }
};
struct RobotContext {
  struct GraphChange {std::vector<std::size_t> lanes;};
  int replans=0, graph_changes=0;
  void notify_graph_change(GraphChange p) {assert(!p.lanes.empty());++graph_changes;}
  void request_replan() {++replans;}
};
struct RobotUpdateHandle {
  struct Impl {
    std::shared_ptr<RobotContext> c=std::make_shared<RobotContext>();
    auto get_context() {return c;}
  };
  std::unique_ptr<Impl> _pimpl=std::make_unique<Impl>();
  std::vector<std::size_t> reverse;
  std::vector<std::size_t> return_wp;
  void replan();
  // Count update requests, not application, tracking, or actuator effects.
  void update_position(const Eigen::Vector3d&,const std::vector<std::size_t>& ids) {reverse=ids;}
  void update_position(const Eigen::Vector3d&,std::size_t w) {return_wp={w};}
};
/*REPLAN*/
struct PlanWaypoint {
  std::vector<std::size_t> lanes;
  const auto& approach_lanes() const {return lanes;}
};
struct Robot {
  struct Travel {
    std::optional<std::size_t> target_plan_index=0;
    std::vector<PlanWaypoint> waypoints;
    std::shared_ptr<const Graph> graph;
    std::shared_ptr<RobotUpdateHandle> updater=std::make_shared<RobotUpdateHandle>();
  } _travel_info;
  struct State {struct {double x,y,yaw;} location;};
  std::shared_ptr<State> _last_known_state;
  /*ROBOT*/
};
struct Worker {
  std::deque<std::function<void()>> todo;
  template<class F> void schedule(F f) {todo.emplace_back([f=std::move(f)]{f(0);});}
  void drain() {while(!todo.empty()){auto f=std::move(todo.front());todo.pop_front();f();}}
};
namespace rmf_traffic::agv {
struct LaneClosures {
  std::set<std::size_t> ids;
  void open(std::size_t i) {ids.erase(i);}
  void close(std::size_t i) {ids.insert(i);}
};
struct Config {
  LaneClosures l;
  auto& lane_closures() {return l;}
};
struct Planner {
  struct Options {explicit Options(std::nullptr_t) {}};
  Config config;
  Planner(Config c,Options) : config(std::move(c)) {}
  auto get_configuration() const {return config;}
};
}
struct TaskParameters {
  int installs=0;
  void planner(const std::shared_ptr<const rmf_traffic::agv::Planner>&) {++installs;}
};
struct FleetUpdateHandle : std::enable_shared_from_this<FleetUpdateHandle> {
  using Planner=rmf_traffic::agv::Planner;
  struct Impl {
    Worker worker;
    bool emergency_active=false;
    int publications=0;
    std::set<std::size_t> closed_lanes;
    std::shared_ptr<std::shared_ptr<const Planner>> planner =
      std::make_shared<std::shared_ptr<const Planner>>(
        std::make_shared<const Planner>(rmf_traffic::agv::Config{},Planner::Options(nullptr)));
    std::shared_ptr<TaskParameters> task_parameters=std::make_shared<TaskParameters>();
    std::vector<std::pair<std::shared_ptr<RobotContext>,int>> task_managers;
    void publish_lane_states() {++publications;}
    void update_emergency_planner() {assert(false);}
  };
  std::unique_ptr<Impl> _pimpl=std::make_unique<Impl>();
  void open_lanes(std::vector<std::size_t>);
  void close_lanes(std::vector<std::size_t>);
};
/*CLOSE*/
/*OPEN*/

namespace rmf_fleet_msgs::msg {
struct LaneRequest {
  using UniquePtr=std::unique_ptr<LaneRequest>;
  std::string fleet_name;
  std::vector<std::size_t> open_lanes,close_lanes;
};
struct ClosedLanes {std::string fleet_name; std::vector<std::size_t> closed_lanes;};
}
struct Publisher {
  std::vector<rmf_fleet_msgs::msg::ClosedLanes> seen;
  void publish(const rmf_fleet_msgs::msg::ClosedLanes& s){seen.push_back(s);}
};
struct Connections : std::enable_shared_from_this<Connections> {
  std::shared_ptr<FleetUpdateHandle> fleet=std::make_shared<FleetUpdateHandle>();
  std::unordered_set<std::size_t> closed_lanes;
  std::vector<std::pair<int,std::shared_ptr<Robot>>> robots;
  std::shared_ptr<Publisher> closed_lanes_pub=std::make_shared<Publisher>();
};

int main() {
  const std::string fleet_name="fixture";
  int total=0;
  for (bool reverse_exists: {false,true}) {
    for (bool selected_lane: {false,true}) {
      for (bool inside: {false,true}) {
        auto connections=std::make_shared<Connections>();
        auto graph=std::make_shared<Graph>();
        if(!reverse_exists) graph->lanes[1].a=2;
        auto robot=std::make_shared<Robot>();
        robot->_travel_info.graph=graph;
        robot->_travel_info.waypoints={{{selected_lane?0u:2u}},{{3}},{{0}}};
        robot->_last_known_state=std::make_shared<Robot::State>(
          Robot::State{{inside?5.0:-1.0,0.0,0.0}});
        auto& effect=*robot->_travel_info.updater;
        auto& plant=*connections->fleet->_pimpl;
        auto& ctx=*effect._pimpl->c;
        plant.task_managers.emplace_back(effect._pimpl->c,0);
        connections->robots.emplace_back(1,robot);
        auto callback=/*CALLBACK*/;
        callback(std::make_unique<rmf_fleet_msgs::msg::LaneRequest>(
          rmf_fleet_msgs::msg::LaneRequest{fleet_name,{}, {0}}));
        assert(connections->closed_lanes_pub->seen.size()==1);
        const auto& msg=connections->closed_lanes_pub->seen[0];
        assert(msg.fleet_name==fleet_name && msg.closed_lanes==std::vector<std::size_t>{0});
        assert((*plant.planner)->config.l.ids.empty() && plant.publications==0);
        assert(ctx.graph_changes==0 && ctx.replans==1);
        assert((!effect.reverse.empty())==(selected_lane&&inside&&reverse_exists));
        assert((!effect.return_wp.empty())==(selected_lane&&inside&&!reverse_exists));
        if(!effect.reverse.empty()) assert(effect.reverse.front()==1);
        if(!effect.return_wp.empty()) assert(effect.return_wp.front()==0);
        plant.worker.drain();
        assert((*plant.planner)->config.l.ids==std::set<std::size_t>{0});
        assert(plant.publications==1 && ctx.graph_changes==1);
        assert(plant.task_parameters->installs==1);
        std::cout<<"reverse="<<reverse_exists<<" current="<<selected_lane<<" on_lane="<<inside
          <<" announced_closed=0 replan=1 planner:open->closed"
          <<" reverse_update="<<!effect.reverse.empty()<<" waypoint_update="<<!effect.return_wp.empty()<<'\n';
        ++total;
      }
    }
  }
  std::cout<<"selected callback/worker fixtures: "<<total<<'\n';
}
