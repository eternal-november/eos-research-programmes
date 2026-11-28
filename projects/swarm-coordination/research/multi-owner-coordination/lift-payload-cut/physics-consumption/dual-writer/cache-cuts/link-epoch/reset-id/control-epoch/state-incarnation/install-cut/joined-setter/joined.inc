enum Arm { blind, skip, seed, direct, unqualified, mailbox };
int main() {
  std::array<int,6> agreement{}, wrong{}, vertical{}, calls{};
  int total=0;
  for(bool split:{false,true})
  for(bool neutral:{false,true})
  for(bool payload:{false,true})
  for(bool engineFeature:{false,true})
  for(int update=0;update<4;update++) // 0 silence; 1 after-cut mailbox; 2 after-cut latch; 3 late latch
  for(double old:{1.,-1.,0.})
  for(double replacement:{0.,2.})
  for(int arm=blind;arm<=mailbox;++arm) {
    graph::Trial life;
    life.start();
    const auto g0=life.claim();
    const auto unrelated=life.r.entityCompMgr.CreateEntity();
    life.r.entityCompMgr.ClearNewlyCreatedEntities();
    act::Tr t(static_cast<int>(g0.id));
    t.publish(old);
    t.latch();
    int sampleEpoch=g0.allocation_gen, mailboxEpoch=sampleEpoch;
    life.submit(true);
    if(split)assert(!life.drain()&&!life.r.entityCompMgr.HasEntity(life.watched));
    life.submit(false);
    assert(life.drain()==split);
    const auto g1=life.claim();
    assert(g1.id==g0.id&&g1.world_gen==g0.world_gen);
    assert(life.r.entityCompMgr.HasEntity(g1.id)&&life.r.entityCompMgr.HasEntity(unrelated));
    if(update) {
      t.publish(replacement);
      mailboxEpoch=g1.allocation_gen;
    }
    if(update==2) {
      t.latch();
      sampleEpoch=mailboxEpoch;
    }
    const bool valid=sampleEpoch==g1.allocation_gen;
    const double expectedX=valid?(update==2?replacement:old):0.;
    const double expectedZ=payload?.625:0.;
    const bool lawful=valid||neutral;
    const bool reference=lawful&&engineFeature;
    const bool stagedNative=arm==blind||valid||(arm==mailbox&&mailboxEpoch==g1.allocation_gen);
    const bool stagedNeutral=!stagedNative&&((arm==seed&&neutral)||arm==unqualified);
    assert(!t.ecs.commands.contains(t.watched));
    if(stagedNative)t.robot.use(t.ecs);
    if(stagedNeutral) {
      const auto saved=t.robot.cached.linearVelocity;
      t.robot.cached.linearVelocity={}; // authored authorized neutral supplier
      t.robot.use(t.ecs);              // actual set-or-create path
      t.robot.cached.linearVelocity=saved;
    }
    if(arm==direct&&!valid&&neutral)
      t.ecs.CreateComponent(t.watched,act::components::LinearVelocityCmd{{0.,0.,0.}});
    t.ecs.poses.at(t.watched).value.pos.x=payload?.25:2.;
    t.lift.write(t.ecs,1,.625);
    t.phys.entityFreeGroupMap.feature=engineFeature;
    t.phys.consume9(t.ecs);
    if(update==3)t.latch(); // cannot retroactively modify a delivered setter call
    const bool sent=!t.phys.entityFreeGroupMap.calls.empty();
    if(sent) {
      assert(t.phys.entityFreeGroupMap.calls.size()==1);
      ++calls[arm];
      vertical[arm]+=t.z()==.625;
      wrong[arm]+=!lawful||(!valid&&stagedNative);
    }
    const bool exact=sent==reference&&(!sent||(t.x()==expectedX&&t.z()==expectedZ&&lawful&&(valid||!stagedNative)));
    agreement[arm]+=exact;
    if(arm==seed||arm==direct)assert(exact);
    act::cleanup9(t.ecs);
    assert(!t.ecs.commands.contains(t.watched));
    if(sent)assert(t.phys.entityFreeGroupMap.calls.size()==1);
    ++total;
  }
  assert(total==2304);
  assert(agreement[seed]==384&&agreement[direct]==384);
  assert(vertical[seed]-vertical[skip]==18&&wrong[seed]==0&&wrong[skip]==0);
  std::cout<<"cases "<<total<<"\n";
  for(int a=0;a<6;++a)std::cout<<a<<" "<<agreement[a]<<" "<<wrong[a]<<" "<<vertical[a]<<" "<<calls[a]<<"\n";
}
