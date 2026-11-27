#include <iomanip>
int main(){
  double x,z,pitch;
  while(std::cin>>x>>z>>pitch){
    Tr t;
    t.publish(1);
    t.latch();
    t.robot.use(t.ecs);
    t.lift.write(t.ecs,1,.625);
    // Authored separate scope and current-slot restoration candidate.
    // It uses the same selected native vector writer.
    t.robot.cached.linearVelocity={x,0,z};
    t.robot.use(t.ecs);
    t.ecs.poses.at(2).value.rot.pitch=pitch;
    t.phys.consume9(t.ecs);
    std::cout<<std::setprecision(16)<<t.x()<<' '<<t.z()<<'\n';
    cleanup9(t.ecs);
  }
}
