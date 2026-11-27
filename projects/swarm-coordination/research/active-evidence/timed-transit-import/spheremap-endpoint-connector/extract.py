from pathlib import Path
import re,sys
s=(Path(sys.argv[1])/'spheremap.cpp').read_text()
def fn(pattern):
    m=re.search(pattern,s)
    start=m.start()
    p=s.index('{',m.end())+1
    d=1
    while d:
        d+=(s[p]=='{')-(s[p]=='}');p+=1
    return s[start:p]
Path('source.inc').write_text('\n\n'.join([
  fn(r'std::optional<std::pair<float, octomap::OcTreeKey>> SphereMap::getNearestNodeKey\(octomap::point3d test_point, float max_point_dist\)'),
  fn(r'std::vector<std::pair<float, octomap::OcTreeKey>> SphereMap::getNearestNodeKeysForEachSegment\('),
  fn(r'std::optional<std::vector<SphereMapPath>> SphereMap::computePathsToGoalsWithConnectingToGraph\(')
]))
