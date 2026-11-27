#include <memory>
int main(){
  std::unique_ptr<Tr> t;
  std::string action;
  while(std::cin>>action){
    if(action=="begin"){
      t=std::make_unique<Tr>();
      t->publish(1); t->latch(); t->robot.use(t->ecs); t->lift.write(t->ecs,1,.625);
    }else if(action=="mail"){
      t->publish(0);
    }else if(action=="latch"){
      t->latch();
    }else if(action=="rewrite"){
      t->robot.use(t->ecs);
    }else if(action=="restore"){
      t->lift.write(t->ecs,1,.625);
    }else if(action=="setter"){
      t->phys.consume9(t->ecs);
      std::cout<<"setter "<<t->x()<<' '<<t->z()<<std::endl;
      cleanup9(t->ecs);
      continue;
    }else assert(false);
    const auto &v=t->ecs.commands.at(2).Data();
    std::cout<<action<<' '<<v.x<<' '<<v.z<<std::endl;
  }
}
