struct Plant {
  EntityComponentManager e;
  PhysicsPrivate phy;
  VelocityControl retained;
  Plant(){
    e.poses[1]={};e.poses[2]={};e.parents.emplace(2,components::ParentEntity{1});
    e.models.insert(2);phy.entityModelMap.refs[2]={};phy.topLevelModelMap[2]=2;
    link(10,2,"shoe");
    link(30,2,"port");
    send(retained,"shoe",1);
    send(retained,"port",3);
    sample(retained);
    assert(perform(retained).at(10).x==1);
    assert(e.resolves==2);
  }
  void link(Entity id,Entity parent,std::string n){
    e.poses[id]={};e.linkIds.insert(id);e.parents[id]={parent};e.names[id]=n;
    phy.entityLinkMap.refs[id]={};
  }
  void replacement(bool old_remains,int a){
    const Entity prior=(a==11?10:11);
    if (old_remains) {
      e.poses[3]={};e.models.insert(3);e.parents[3]={1};
      e.parents[prior]={3}; // authored reconfiguration before the cut
    } else{
      e.poses.erase(prior);e.linkIds.erase(prior);e.parents.erase(prior);e.names.erase(prior);
      phy.entityLinkMap.refs.erase(prior);
    }
    link(a,2,"shoe");
    assert(retained.p.model.LinkByName(e,"shoe")==a);
  }
  static void send(VelocityControl& v,const std::string& s,double x){
    v.p.OnLinkCmdVel({{x,0,0},{}},{"/model/carrier/link/"+s+"/cmd_vel"});
  }
  void sample(VelocityControl& v){v.p.UpdateLinkVelocity({},e);}
  std::map<Entity,math::Vector3d> perform(VelocityControl& v){
    v.PreUpdate({},e);
    return eat();
  }
  std::map<Entity,math::Vector3d> eat(){
    phy.entityFreeGroupMap.calls.clear();
    phy.consume(e);
    std::map<Entity,math::Vector3d> c;
    for(const auto& q:phy.entityFreeGroupMap.calls)assert(c.emplace(q.id,q.v).second);
    // The fixture collapses the existing v9 post-step cleanup to clearing
    // the command store between cuts, not source callbacks or cache reset.
    e.linear.clear();e.angular.clear();
    return c;
  }
};
// Authored proposal, not stock Gazebo. serialized with callback/snapshot and
// writes in this test; authority for the namespace and entity supplied by
// the case. Leaving a cached command while changing its recipient is distinct.
void migrate(VelocityControl& v,Entity e,bool clear) {
  v.p.links["shoe"]=e;
  if(!clear)return;
  v.p.linkVels.erase("shoe");
  v.p.linearVelocities.erase("shoe");
  v.p.angularVelocities.erase("shoe");
}

// Old and new delivery endpoints can carry equal values. The stock callback
// receives only link-scoped topic name and Twist. Selective continuation
// assumes an authored admission point on this source with proven scope.
struct Effect {
  int generation; Entity link; double x;
};
bool admit(Plant& a,int generation,Entity target,Effect e){
  if(e.generation!=generation||e.link!=target)return false;
  Plant::send(a.retained,"shoe",e.x);
  return true;
}
bool fenced(Plant& a,Entity old_link){
  // Authored pre-consumption inhibition of a known exclusive command slot.
  // This does not stop any setter already called on the old entity.
  bool old=a.e.linear.erase(old_link)>0;
  a.e.angular.erase(old_link);
  return old;
}
void counterexamples(){
  // The first unread entry for one name wins, e.g., delay from an older
  // appointment (a normal schedule in the model) can beat the newer one.
  for(bool stale_first:{false,true}){
    Plant a;
    Plant::send(a.retained,"shoe",stale_first?5:2);
    Plant::send(a.retained,"shoe",stale_first?2:5);
    a.sample(a.retained);
    assert(a.perform(a.retained).at(10).x==(stale_first?5:2));
  }
  // A verified rebind of stored source-side maps cannot recall a command
  // produced before the cut. New topology changes the native link transform.
  for(bool gate:{false,true}){
    Plant a;
    a.retained.PreUpdate({},a.e);
    a.replacement(true,11);
    a.e.poses.at(3).value.r.q=1;
    migrate(a.retained,11,true);
    if(gate)assert(fenced(a,10));
    auto observed=a.eat();
    assert(observed.contains(10)==!gate&&observed.at(30).x==3);
    if(!gate)assert(observed.at(10).x==0&&observed.at(10).y==1);
    assert(!observed.contains(11));
  }
  // Identical values do not certify different adoption laws: one acted-on
  // callback carries generation 0, the other carries generation 1.
  for(bool generation_agrees:{false,true}){
    Plant blind,guarded;
    for(Plant* a:{&blind,&guarded}){
      a->replacement(false,11);
      migrate(a->retained,11,true);
    }
    Effect e{generation_agrees?1:0,11,2};
    Plant::send(blind.retained,"shoe",e.x);
    assert(admit(guarded,1,11,e)==generation_agrees);
    blind.sample(blind.retained);guarded.sample(guarded.retained);
    auto b=blind.perform(blind.retained),g=guarded.perform(guarded.retained);
    assert(b.at(11).x==2&&b.at(30).x==3&&g.at(30).x==3);
    assert(g.contains(11)==generation_agrees);
  }
}
int sweep(){
  int n=0;
  // All corners for two successive replacements, an independently viable
  // unchanged partner, and scoped fault at each update. The environment may
  // retain the prior entity and may deliver after the sampled cut.
  for(int v=0;v<256;++v){
    Plant a; Entity prior=10;
    for(int g=1;g<=2;++g){
      int offset=4*(g-1);
      bool remains=(v>>offset)&1;
      bool in_flight=(v>>(offset+1))&1;
      bool timely=(v>>(offset+2))&1;
      bool old_first=(v>>(offset+3))&1;
      Entity candidate=10+g; // non-reusable logical body identity
      if(in_flight)a.retained.PreUpdate({},a.e);
      // Gazebo entity conditions are authored here and checked by the native
      // selected lookup and setter paths, not by a deployed spawn/reparent run.
      if(remains){
        a.e.models.insert(3);a.e.poses[3]={};a.e.parents[3]={1};
        a.e.parents[prior]={3};
      }else{
        a.e.poses.erase(prior);a.e.linkIds.erase(prior);a.e.parents.erase(prior);
        a.e.names.erase(prior);a.phy.entityLinkMap.refs.erase(prior);
      }
      a.link(candidate,2,"shoe");
      const auto actual=a.retained.p.model.LinkByName(a.e,"shoe");
      assert(actual==candidate);
      migrate(a.retained,actual,true);
      fenced(a,prior);
      auto old=[&](){assert(!admit(a,g,actual,{g-1,prior,5}));};
      auto live=[&](){assert(admit(a,g,actual,{g,actual,2}));};
      if(old_first)old();
      if(timely)live();
      if(!old_first)old();
      a.sample(a.retained);
      if(!timely)live(); // callback happened, but after the native latch
      const auto hits=a.perform(a.retained);
      assert(hits.contains(actual)==timely&& !hits.contains(prior));
      assert(hits.at(30).x==3);
      if(timely)assert(hits.at(actual).x==2);
      // If the first deadline was missed, the next unpaused cut settles it.
      a.sample(a.retained);
      const auto next=a.perform(a.retained);
      assert(next.at(actual).x==2&&next.at(30).x==3);
      prior=actual;++n;
    }
  }
  return n;
}
int main(){
  counterexamples();
  std::cout<<"two-replacement cut checks "<<sweep()<<"\n";
  for(bool remains:{false,true}){
    Plant a;a.replacement(remains,11);
    const auto r=a.e.resolves;
    Plant::send(a.retained,"shoe",2);
    a.sample(a.retained);
    auto got=a.perform(a.retained);
    assert(!got.contains(11)&&got.at(30).x==3&&r==a.e.resolves);
    if (remains) assert(got.at(10).x==2);
    else assert(!got.contains(10)&&a.e.missingCreates==2);

    Plant b;b.replacement(remains,11);
    migrate(b.retained,11,false);
    got=b.perform(b.retained);
    assert(got.at(11).x==1&&got.at(30).x==3); // old cached intent crosses new target

    Plant c;c.replacement(remains,11);
    Plant::send(c.retained,"shoe",5); // old message pending, before change recognized
    migrate(c.retained,11,true);
    c.sample(c.retained);got=c.perform(c.retained);
    assert(!got.contains(11)&&!got.contains(10)&&got.at(30).x==3);
    Plant::send(c.retained,"shoe",2);c.sample(c.retained);got=c.perform(c.retained);
    assert(got.at(11).x==2&&got.at(30).x==3&&!got.contains(10));

    // Full new plugin in the same state, configured with the same link names;
    // give it the same one new receipt, not a refreshed independent command.
    VelocityControl fresh;Plant::send(fresh,"shoe",2);c.sample(fresh);got=c.perform(fresh);
    assert(got.at(11).x==2&&!got.contains(30));
    std::cout<<"old_still_in_physics="<<remains
             <<": stale-bound writer misses new; retarget alone migrates old intent; "
             <<"selective reset earns new accepted write while retaining independent port\n";
  }
}
