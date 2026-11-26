using namespace nav2_collision_monitor;
using Laser=sensor_msgs::msg::LaserScan;
using Twist=geometry_msgs::msg::TwistStamped;
int main(){
  TF tf;
  auto scan=[&](float range,int epoch) {
    auto p=std::make_shared<Laser>();p->header.stamp={epoch};p->ranges={range};return p;
  };
  auto cmd=std::make_shared<Twist>();
  {
    Scan source;
    source.tf_manager_=&tf;
    const auto same=scan(.5,0);
    source.dataCallback(same);
    CollisionMonitor op{&source,{},0,{},{},{}};
    op.now=0;op.cmdVelInCallbackStamped(cmd);
    op.now=1;op.cmdVelInCallbackStamped(cmd);
    assert((op.activated==std::vector<bool>{false,true}));
    assert((op.counts==std::vector<int>{1,1}));
    op.now=3;op.cmdVelInCallbackStamped(cmd);
    assert(!op.processed.back()&&op.counts.size()==2); // age limit is still effective
    std::cout<<"one acquisition, two admitted evaluations: native trigger on evaluation two\n";
  }
  {
    Scan source;
    source.tf_manager_=&tf;
    source.dataCallback(scan(1.25,0));
    CollisionMonitor op{&source,{},0,{},{},{}};
    op.polygon.trigger_active_=true;
    op.now=0;op.cmdVelInCallbackStamped(cmd);
    op.now=1;op.cmdVelInCallbackStamped(cmd);
    assert((op.activated==std::vector<bool>{true,false}));
    assert((op.counts==std::vector<int>{0,0}));
    std::cout<<"one acquisition, two admitted misses: native release on evaluation two\n";
  }
  {
    Scan source;
    source.tf_manager_=&tf;
    source.dataCallback(scan(.5,0));
    tf.xp={0,.75,0,0,0,0,0,0}; // wall at .5, observer moves past and returns
    CollisionMonitor op{&source,{},0,{},{},{}};
    for(int t:{0,1,2}){op.now=t;op.cmdVelInCallbackStamped(cmd);}
    assert((op.counts==std::vector<int>{1,0,1}));
    assert((op.activated==std::vector<bool>{false,false,false}));
    std::cout<<"same acquisition at three use cuts: projected membership is 1,0,1\n";
  }
  {
    TF other;
    other.xp={0,.5,0,0,0,0,0,0};
    Scan source;
    source.tf_manager_=&other;
    source.dataCallback(scan(1.25,0));
    CollisionMonitor op{&source,{},0,{},{},{}};
    op.polygon.trigger_active_=true;
    op.now=0;op.cmdVelInCallbackStamped(cmd);
    op.now=1;op.cmdVelInCallbackStamped(cmd);
    source.dataCallback(scan(1.25,2));
    op.now=2;op.cmdVelInCallbackStamped(cmd);
    assert((op.counts==std::vector<int>{0,1,0}));
    assert((op.activated==std::vector<bool>{true,true,true}));
    std::cout<<"two acquisition IDs and use votes 0,1,0: middle cached projection still matters\n";
  }
}
