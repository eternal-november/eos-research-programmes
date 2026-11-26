#include <cassert>
#include <cmath>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <vector>
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
namespace nav2_collision_monitor {
struct Point {double x,y,z;std::string source;};
struct Reply {double transform;};
struct TF {
  int p0,p1,b0,b1; // declared provider in a stationary-wall scene
  bool called=false;
  std::optional<Reply> getStampedTransform(std::string dst,rclcpp::Time td,
      std::string src,rclcpp::Time ts,std::string fixed,double,std::string*) {
    assert(dst=="base"&&src=="laser"&&td.x==1&&(ts.x==0||ts.x==1));
    assert(fixed=="map"||fixed=="motion_reference");
    called=true;
    // Source and target extrinsics coincide in the fixture.
    // Motion reference has no common frame discontinuity.
    int bias=fixed=="map" ? (ts.x==0?b0:b1)-b1 : 0;
    int translation=(ts.x==0?p0:p1)-p1;
    return Reply{double(bias+translation)};
  }
  std::optional<Reply> getLatestTransform(std::string dst,std::string src,int,std::string*) {
    assert(dst=="base"&&src=="laser");
    called=true;return Reply{0};
  }
};
struct Source {
  TF *tf_manager_{};
  bool base_shift_correction_{};
  std::string base_frame_id_="base",global_frame_id_="map",source_name_="laser";
  double transform_tolerance_=0;
  int transform_staleness_threshold_=0;
  rclcpp::Duration source_timeout_{2};
  bool sourceValid(const rclcpp::Time&,const rclcpp::Time&) const;
  bool getTransform(const rclcpp::Time&, const std_msgs::msg::Header&,tf2::Transform&) const;
};
struct Laser {
  std_msgs::msg::Header header{"laser",{0}};
  float angle_min=0,angle_increment=0,range_min=0,range_max=12;
  std::vector<float> ranges;
};
struct Scan : Source {
  std::shared_ptr<Laser> data_=std::make_shared<Laser>();
  bool getSourceData(const rclcpp::Time&,std::vector<Point>&);
};
}
