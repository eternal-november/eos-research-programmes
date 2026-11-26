#!/usr/bin/env python3
"""Run selected pinned Scan, Source, polygon and velocity callback functions."""
import hashlib,subprocess,tempfile,sys
from pathlib import Path
base=Path(sys.argv[1]);here=Path(__file__).resolve().parent
def src(n,sha):
    x=(base/n).read_bytes()
    assert hashlib.sha1(b'blob '+str(len(x)).encode()+b'\0'+x).hexdigest()==sha,n
    return x.decode()
def pull(s,key):
    i=s.index(key)
    return s[i:s.index('\n}',i)+2]
so=src('source.cpp','b0c387754822aa4b880f14187643d9221aa6e32d')
sc=src('scan.cpp','bd1f5ae5620a852543e9ec83e8651def087e205d')
gl=src('geometry_utils.hpp','3869fbb9c4916e42d196c74cf74baf992f37a11c')
po=src('polygon.cpp','5d6fcde164621b97798d3bf44de836674b8b389c')
cm=src('collision_monitor_node.cpp','785c13a56688f0f3d9c8db19f78a02fbe54c4147')
assert 'rclcpp::Time curr_time = this->now();' in cm
assert 'source->getData(curr_time,' in cm
assert 'polygon->isTriggered(sources_collision_points_map, triggering_points)' in cm
assert 'return isTriggeredInternal(points_inside);' in po
assert 'getSourceData(curr_time,' in so
with tempfile.TemporaryDirectory() as d:
    p=Path(d)
    (p/'run.cc').write_text('\n'.join([(here/'fixture.inc').read_text(),
        'namespace nav2_util::geometry_utils {',pull(gl,'template<class PointT>\ninline bool isPointInsidePolygon('),'}',
        'namespace nav2_collision_monitor {',
        pull(so,'bool Source::sourceValid('),pull(so,'bool Source::getTransform('),
        pull(sc,'bool Scan::getSourceData('),pull(sc,'void Scan::dataCallback('),
        pull(po,'bool Polygon::isTriggeredInternal('),
        pull(po,'int Polygon::getPointsInside(\n  const std::vector<Point> & points,\n  std::vector<Point> &'),
        pull(cm,'void CollisionMonitor::cmdVelInCallbackStamped('),
        '}',(here/'test.inc').read_text()]))
    subprocess.run(['c++','-std=c++20','-Wall','-Wextra','-Werror','-o',p/'run',p/'run.cc'],check=True)
    subprocess.run([p/'run'],check=True)
