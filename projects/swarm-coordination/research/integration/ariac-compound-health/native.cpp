#include <iostream>
#include <memory>
#include <string>
#include <vector>

#define RCLCPP_INFO_STREAM(a,b) ((void)0)
struct BeforeErase {};
struct Event {
  int trigger, duration, start{-1};
  std::vector<std::string> mask;
  bool started{false}, complete{false};
  int GetTriggerTime() const { return trigger; }
  int GetDuration() const { return duration; }
  int GetStartTime() const { return start; }
  bool HasStarted() const { return started; }
  bool HasCompleted() const { return complete; }
  void SetStartTime(int t) { start = t; }
  void SetStarted() { started = true; }
  void SetCompleted() { complete = true; }
  const auto &GetRobotsToDisable() const { return mask; }
  const auto &GetSensorsToDisable() const { return mask; }
};
namespace ariac_msgs::msg {
struct Robots { bool ceiling_robot, floor_robot; };
struct Sensors { bool break_beam, proximity, laser_profiler, lidar, camera, logical_camera; };
}
template<class T> struct Pub {
  T latest{};
  void publish(const T &m) { latest = m; }
};
struct State {
  bool floor_robot_health_{true}, ceiling_robot_health_{true};
  bool break_beam_sensor_health_{true}, proximity_sensor_health_{true};
  bool laser_profiler_sensor_health_{true}, lidar_sensor_health_{true};
  bool camera_sensor_health_{true}, logical_camera_sensor_health_{true};
  Pub<ariac_msgs::msg::Robots> rp;
  Pub<ariac_msgs::msg::Sensors> sp;
  Pub<ariac_msgs::msg::Robots> *robot_health_pub_{&rp};
  Pub<ariac_msgs::msg::Sensors> *sensor_health_pub_{&sp};
  int elapsed_time_{-1};
  std::vector<std::shared_ptr<Event>> time_based_robot_malfunctions_, in_progress_robot_malfunctions_;
  std::vector<std::shared_ptr<Event>> time_based_sensor_blackouts_, in_progress_sensor_blackouts_;
};
struct TaskManagerPlugin {
  State *impl_;
  void SetSensorsHealth(const std::vector<std::string>&);
  void SetRobotsHealth(const std::vector<std::string>&);
  void ProcessTemporalRobotMalfunctions();
  void ProcessTemporalSensorBlackouts();
  void ProcessInProgressRobotMalfunctions();
  void ProcessInProgressSensorBlackouts();
  void UpdateSensorsHealth();
  void UpdateRobotsHealth();
};
#include "upstream_extract.inc"

int main() {
  // Each trace stops at its first expiry; the newer record has not completed.
  for (int second=0;second<3;++second) {
    State s;
    TaskManagerPlugin p{&s};
    s.time_based_robot_malfunctions_.push_back(
      std::make_shared<Event>(Event{0,2,-1,{"ceiling_robot"}}));
    s.time_based_sensor_blackouts_.push_back(
      std::make_shared<Event>(Event{0,2,-1,{"camera"}}));
    std::shared_ptr<Event> jr, js;
    if(second) {
      jr=std::make_shared<Event>(Event{second,5,-1,{"floor_robot"}});
      js=std::make_shared<Event>(Event{second,5,-1,{"logical_camera"}});
      s.time_based_robot_malfunctions_.push_back(jr);
      s.time_based_sensor_blackouts_.push_back(js);
    }
    for (int t=-1;t<=2;++t) {
      s.elapsed_time_ = t;
      p.ProcessTemporalSensorBlackouts();
      p.ProcessTemporalRobotMalfunctions();
      int stopped_r=0, stopped_s=0;
      try { p.ProcessInProgressSensorBlackouts(); }
      catch (const BeforeErase&) { stopped_s=1; }
      try { p.ProcessInProgressRobotMalfunctions(); }
      catch (const BeforeErase&) { stopped_r=1; }
      p.UpdateRobotsHealth();
      p.UpdateSensorsHealth();
      std::cout<<second<<' '<<t<<' '<<s.rp.latest.ceiling_robot<<' '
        <<s.rp.latest.floor_robot<<' '<<s.sp.latest.camera<<' '
        <<s.sp.latest.logical_camera<<' '<<stopped_r<<' '<<stopped_s<<' '
        <<bool(jr&&jr->started&&!jr->complete)<<' '
        <<bool(js&&js->started&&!js->complete)<<'\n';
      if(stopped_r||stopped_s) break;
    }
  }
}
