#include <cassert>
#include <cstddef>
#include <iostream>
#include <vector>
using std::size_t;

namespace nav2_collision_monitor {
struct Point {double x,y;};
struct Polygon {
  std::vector<Point> poly_{{0,0},{1,0},{1,1},{0,1}};
  int min_points_,trigger_consecutive_points_,release_consecutive_points_;
  bool trigger_active_;
  int trigger_hits_,release_hits_;
  bool isTriggeredInternal(int);
  int getPointsInside(const std::vector<Point>&,std::vector<Point>&) const;
};
}
