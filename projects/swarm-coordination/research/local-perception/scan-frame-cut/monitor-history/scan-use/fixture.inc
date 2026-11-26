#include <algorithm>
#include <array>
#include <cassert>
#include <cmath>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <vector>
using std::size_t;
#define RCLCPP_WARN(...) ((void)0)
#define RCLCPP_ERROR(...) ((void)0)
namespace rclcpp {
struct Duration {
  int x;
  int seconds() const {return x;}
  bool operator>(const Duration& other) const {return x>other.x;}
};
struct Time {
  int x;
  Duration operator-(const Time& other) const {return {x-other.x};}
};
}
namespace std_msgs::msg {struct Header {std::string frame_id; rclcpp::Time stamp;};}
namespace geometry_msgs::msg {
struct Twist {struct V{double x{},y{},z{};} linear,angular;};
struct TwistStamped {
  using ConstSharedPtr=std::shared_ptr<const TwistStamped>;
  Twist twist{};
  std_msgs::msg::Header header{};
};
}
namespace nav2_util {
bool validateTwist(const geometry_msgs::msg::Twist&) {return true;} // valid input only
}
namespace tf2 {
struct Vector3 {
  double xx,yy,zz;
  double x() const {return xx;}
  double y() const {return yy;}
  double z() const {return zz;}
};
struct Transform {
  double translation=0;
  Vector3 operator*(const Vector3& q) const {return {q.x()+translation,q.y(),q.z()};}
};
void fromMsg(double in,Transform& out) {out.translation=in;}
}
namespace sensor_msgs::msg {
struct LaserScan {
  using ConstSharedPtr=std::shared_ptr<const LaserScan>;
  std_msgs::msg::Header header{"laser",{0}};
  float angle_min=0,angle_increment=0,range_min=0,range_max=12;
  std::vector<float> ranges;
};
}
namespace nav2_collision_monitor {
struct Point {double x,y,z=0;std::string source{};};
struct Reply {double transform;};
struct TF {
  std::array<double,8> xp{};
  std::optional<Reply> getStampedTransform(std::string dst,rclcpp::Time td,
      std::string src,rclcpp::Time ts,std::string fixed,double,std::string*) {
    assert(dst=="base"&&src=="laser"&&fixed=="motion");
    assert(0<=ts.x&&ts.x<=td.x&&td.x<8);
    return Reply{xp[ts.x]-xp[td.x]};
  }
  std::optional<Reply> getLatestTransform(std::string,std::string,int,std::string*) {
    assert(false); return std::nullopt;
  }
};
struct Source {
  TF *tf_manager_{};
  bool base_shift_correction_=true;
  std::string base_frame_id_="base",global_frame_id_="motion",source_name_="laser";
  double transform_tolerance_=0;
  int transform_staleness_threshold_=0;
  rclcpp::Duration source_timeout_{2};
  bool sourceValid(const rclcpp::Time&,const rclcpp::Time&) const;
  bool getTransform(const rclcpp::Time&, const std_msgs::msg::Header&,tf2::Transform&) const;
};
struct Scan : Source {
  sensor_msgs::msg::LaserScan::ConstSharedPtr data_;
  bool getSourceData(const rclcpp::Time&,std::vector<Point>&);
  void dataCallback(sensor_msgs::msg::LaserScan::ConstSharedPtr msg);
};
struct Polygon {
  std::vector<Point> poly_{{0,-1},{1,-1},{1,1},{0,1}};
  int min_points_=1,trigger_consecutive_points_=2,release_consecutive_points_=2;
  bool trigger_active_=false;
  int trigger_hits_=0,release_hits_=0;
  bool isTriggeredInternal(int);
  int getPointsInside(const std::vector<Point>&,std::vector<Point>&) const;
};
struct Velocity {double x,y,r;};
struct CollisionMonitor {
  Scan* scan;
  Polygon polygon{};
  int now=0;
  std::vector<bool> processed,activated;
  std::vector<int> counts;
  void cmdVelInCallbackStamped(const geometry_msgs::msg::TwistStamped::ConstSharedPtr&);
  void process(Velocity,const std_msgs::msg::Header&) {
    // Selected contiguous behavior only, not the complete node's process method.
    std::vector<Point> points,trigger;
    if (!scan->getSourceData({now},points)) {
      processed.push_back(false);
      return;
    }
    processed.push_back(true);
    counts.push_back(polygon.getPointsInside(points,trigger));
    activated.push_back(polygon.isTriggeredInternal(counts.back()));
  }
};
}
