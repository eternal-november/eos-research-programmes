using namespace nav2_collision_monitor;
int main() {
  int n;
  assert(std::cin>>n);
  while(n--){
    int m,tr,rl,act,h,r,frames;
    assert(std::cin>>m>>tr>>rl>>act>>h>>r>>frames);
    Polygon q{{{0,0},{1,0},{1,1},{0,1}},m,tr,rl,!!act,h,r};
    while(frames--){
      int z,k,native_count,native_active,native_hits,native_release;
      assert(std::cin>>z>>k>>native_count>>native_active>>native_hits>>native_release);
      std::vector<Point> points,trigger;
      while(k--){
        int x,y;assert(std::cin>>x>>y);
        points.push_back({double(x+z)/16,double(y)/16});
      }
      int seen=q.getPointsInside(points,trigger);
      assert(seen==native_count);
      assert(q.isTriggeredInternal(seen)==bool(native_active));
      assert((tr==1&&rl==1)||(std::min(tr,q.trigger_hits_)==native_hits &&
                              std::min(rl,q.release_hits_)==native_release));
    }
  }
  std::cout<<"native finite sequences match\n";
}
