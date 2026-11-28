enum Arm { generation, fullPose, projected, direct, recompute };
int main() {
  std::array<int,5> calls{}, wrong{}, valid{}, missed{};
  int n=0;
  auto near=[](auto a,auto b){return std::abs(a.x-b.x)<1.e-12&&
      std::abs(a.y-b.y)<1.e-12&&std::abs(a.z-b.z)<1.e-12;};
  for(int st=-1;st<=1;++st)for(int use=-1;use<=1;++use)
  for(int sy=0;sy<=1;++sy)for(int uy=0;uy<=1;++uy)
  for(int request:{1,-1,0})       // zero does not require frame equality
  for(bool split:{false,true})
  for(bool freshFrame:{false,true})
  for(bool wide:{false,true})    // additional authority to rederive, not to extend deadline
  for(bool engine:{false,true})
  for(int a=generation;a<=recompute;++a) {
    graph::Trial life;
    life.start();
    const auto g0=life.claim();
    act::Tr t(static_cast<int>(g0.id));
    const act::math::Rotation atStage{st,sy},atUse{use,uy};
    t.ecs.poses.at(t.watched).value.rot=atStage;
    const auto px=atStage.up();
    const auto compose=[request](std::array<int,3> p) -> act::math::Vector3d {
      return {request*p[0]/5.,request*p[1]/5.,request*p[2]/5.};
    };
    const auto c=compose(px);
    // Full-vector composition at staging is granted in every arm. The lift's
    // slot overwrite has separately been exercised; it is not run after this.
    t.ecs.CreateComponent(t.watched,act::components::LinearVelocityCmd{c});
    life.submit(true);
    if(split)assert(!life.drain()&&!life.r.entityCompMgr.HasEntity(life.watched));
    life.submit(false);
    assert(life.drain()==split);
    const auto g1=life.claim();
    assert(g0.id==g1.id&&g0.world_gen==g1.world_gen);
    // The staged envelope was outside the graph and can outlive the body;
    // the stub ECS entry represents re-materializing that envelope by address.
    const bool same=g0.allocation_gen==g1.allocation_gen;
    t.ecs.poses.at(t.watched).value.rot=atUse;
    t.phys.entityFreeGroupMap.feature=engine;
    const act::math::Vector3d reference{0.,0.,double(request)};
    const bool sameProjected=px==atUse.up();
    const bool realized=near(atUse*c,reference);
    assert(realized==(request==0||sameProjected));
    const bool knowledge=!(request!=0&&!freshFrame);
    const bool feasible=same&&knowledge&&realized&&engine;
    bool permit=false;
    if(a==generation)permit=same;
    if(a==fullPose)permit=same&&knowledge&&(request==0||atStage==atUse);
    if(a==projected)permit=same&&knowledge&&(request==0||sameProjected);
    if(a==direct)permit=same&&knowledge&&realized;
    if(a==recompute) {
      permit=same&&knowledge&&(realized||wide);
      if(permit&&!realized) t.ecs.commands.at(t.watched).v=compose(atUse.up());
    }
    if(!permit)t.ecs.RemoveComponent<act::components::LinearVelocityCmd>(t.watched);
    t.phys.consume9(t.ecs);
    const bool sent=!t.phys.entityFreeGroupMap.calls.empty();
    if(sent) {
      assert(t.phys.entityFreeGroupMap.calls.size()==1);
      calls[a]++;
      const bool correct=same&&near(t.phys.entityFreeGroupMap.calls.at(0),reference);
      if(correct)valid[a]++;
      else wrong[a]++;
    }
    missed[a]+=feasible&&!sent;
    if(a==projected||a==direct)assert(sent==feasible);
    if(a==recompute)assert(sent==(same&&knowledge&&(realized||wide)&&engine));
    act::cleanup9(t.ecs);
    assert(!t.ecs.commands.contains(t.watched));
    ++n;
  }
  // Local z=1 from native lift is incompatible with exact world z=1
  // at the tested tilt unless it can be superseded. Test one offered input.
  act::Tr lift(2);
  lift.ecs.poses.at(2).value.rot={1,0};
  lift.ecs.CreateComponent(2,act::components::LinearVelocityCmd{{-.75,0.,0.}});
  lift.lift.write(lift.ecs,1,1.);
  lift.phys.consume9(lift.ecs);
  assert(near(lift.phys.entityFreeGroupMap.calls.at(0),act::math::Vector3d{0.,0.,1.25}));
  // Same projected-up row under a world yaw is not enough for a signed
  // horizontal consumer, even at equal allocation and target bits.
  const act::math::Rotation r0{1,0},r1{1,1};
  const act::math::Vector3d right{0.,1.,0.};
  assert(r0.up()==r1.up()&&!near(r0*right,r1*right));
  std::cout<<"cases "<<n<<"\n";
  for(int a=0;a<5;++a)std::cout<<a<<" "<<calls[a]<<" "<<valid[a]<<" "<<wrong[a]<<" "<<missed[a]<<"\n";
}
