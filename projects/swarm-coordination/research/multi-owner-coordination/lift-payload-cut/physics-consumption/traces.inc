struct Trace {
  int version;
  ECS ecs;
  Lift lift;
  Physics phys;
  explicit Trace(int v,bool rotate=false):version(v) {
    ecs.poses[1].value={{0,0,0},{}};
    ecs.poses[2].value={{.25,0,0},{rotate}};
    ecs.poses[3].value={{3,0,0},{}};
    ecs.commands[2]={};
    lift._initial_poses[1]=ecs.poses[1].value;
    lift._initial_aabbs[1]={{-1,-1,-1},{1,1,1}};
    phys.entityModelMap.bodies[2]={};
    phys.topLevelModelMap[2]=2;
  }
  void use(double speed) {lift.write(ecs,1,speed);}
  void consume(){if(version==8)phys.consume8(ecs);else phys.consume9(ecs);}
  void clean(){if(version==8)cleanup8(ecs);else cleanup9(ecs);}
  size_t n()const{return phys.entityFreeGroupMap.calls.size();}
  auto last()const{return phys.entityFreeGroupMap.calls.back();}
  bool present()const{return ecs.commands.contains(2);}
};
int main(){
  for(int v:{8,9}){
    Trace p(v,true);
    p.use(.625);p.consume();
    assert(p.n()==1&&p.last().x==.625&&p.last().z==0);
    p.clean();
    assert(p.present()==(v==8));
    p.use(.75);p.consume();
    assert(p.n()==size_t(v==8?2:1));
    if(v==8)assert(p.last().x==.75);
    p.clean();
    if(v==9){
      p.ecs.commands[2]={};  // Explicit other component producer.
      p.use(.875);p.consume();
      assert(p.n()==2&&p.last().x==.875);
    }
    Trace z(v);
    z.use(.625);z.consume();z.clean();
    z.use(0);z.consume();
    if(v==8)assert(z.n()==2&&z.last().z==0);
    else assert(z.n()==1&&z.last().z==.625);
    for(int m=0;m<4;m++){
      Trace q(v);
      if(m==0)q.phys.entityModelMap.bodies.erase(2);
      if(m==1)q.phys.topLevelModelMap[2]=1;
      if(m==2)q.phys.entityModelMap.bodies[2].free=false;
      if(m==3)q.phys.entityFreeGroupMap.feature=false;
      q.use(.625);q.consume();
      assert(q.n()==0);
      q.clean();
      assert(q.present()==(v==8));
    }
  }
  std::cout<<"both pins: compatible first write reaches the selected setter in world coordinates\n"
           <<"v8 retains zero and accepts the next write; v9 needs explicit recreation in this fixture\n"
           <<"no fresh lift write: v8 calls the setter with zero; v9 makes no setter call\n"
           <<"all four unsupported recipient controls clean up despite no setter call\n";
}
