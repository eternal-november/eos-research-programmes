struct SerializedState {
 struct Part{
   std::string component()const{assert(false);return {};}
   int type()const{assert(false);return 0;}
   bool remove()const{assert(false);return false;}
 };
 struct Row {
   Entity identity;
   bool deleted;
   Entity id()const{return identity;}
   bool remove()const{return deleted;}
   int components_size()const{return 0;} // graph-only cases
   const Part& components(int)const{assert(false);static Part p;return p;}
 };
 std::vector<Row> source;
 int entities_size()const{return int(source.size());}
 const Row& entities(int e)const{return source.at(e);}
};
/*TEST BODY*/
struct EpochKey {
  int world_gen;
  Entity id;
  int operation;
  int allocation_gen;
};
bool accept(const EpochKey& old,const EpochKey& cur,bool lifetime){
  return old.world_gen==cur.world_gen&&old.id==cur.id&&old.operation==cur.operation
      &&(!lifetime||old.allocation_gen==cur.allocation_gen);
}
struct Trial {
  SimulationRunner r;
  bool open=true;
  int gen=1; // qualified, source-local per entity, not supplied by Gazebo
  Entity watched;
  void start(){
    r.prime();
    r.currentInfo.paused=true;
    watched=r.entityCompMgr.CreateEntity();
    r.entityCompMgr.ClearNewlyCreatedEntities();
  }
  void submit(bool removed){
    msgs::WorldControlState w;
    w.value.p=true;
    w.desired=msgs::SerializedState{{{watched,removed}}};
    msgs::Boolean response;
    assert(r.OnWorldControlState(w,response)&&response.v);
  }
  bool drain(){
    r.after_controls_clock(open);
    assert(open&&!r.resetInitiated&&r.currentInfo.simTime==4s);
    r.ProcessNewWorldControlState();
    r.systems();
    bool birth=r.entityCompMgr.dataPtr->newlyCreatedEntities.contains(watched);
    if(birth)++gen;
    r.ProcessMessages();
    r.entityCompMgr.ClearNewlyCreatedEntities();
    r.entityCompMgr.ProcessRemoveEntityRequests();
    return birth;
  }
  EpochKey claim()const{return {1,watched,7,gen};}
};
// Only the source-side lifecycle binding is synchronous; install messages are not.
enum Mode { cache, highWater, writerEpoch, scoped, freezeAll };
int main() {
  unsigned rows=0, passed[5]={}, settle[5]={}, wrong[5]={}, independent[5]={};
  // Each episode includes two admissible state application cuts. The graph-only
  // fixture defers all tested writer requests to the second cut or later.
  for(bool split:{false,true})
  for(int ready=0;ready<=5;++ready)     // 5 means current install misses all five opportunities
  for(int old=0;old<=5;++old)          // duplicated old install; 5 means after all useful ticks
  for(int issue=0;issue<=4;++issue)
  for(bool sendNew:{false,true})
  for(int mode=cache;mode<=freezeAll;++mode) {
    if(sendNew&&!split)continue;       // no proof for an incarnation that never existed
    Trial t;t.start();
    const auto carried=t.claim();
    const auto other=t.r.entityCompMgr.CreateEntity();
    t.r.entityCompMgr.ClearNewlyCreatedEntities();
    t.submit(true);
    if(split) assert(!t.drain()&&!t.r.entityCompMgr.HasEntity(t.watched));
    t.submit(false);
    const auto born=t.drain();
    assert(born==split&&t.r.entityCompMgr.HasEntity(t.watched));
    assert(t.r.entityCompMgr.HasEntity(other));
    assert(!t.r.entityCompMgr.dataPtr->newlyCreatedEntities.contains(t.watched));
    assert(t.r.currentInfo.simTime==4s&&t.claim().world_gen==carried.world_gen);
    assert(carried.id==t.claim().id);
    const int trueEpoch=t.claim().allocation_gen;
    const int request=sendNew?trueEpoch:carried.allocation_gen;
    int installed=carried.allocation_gen;
    bool writerQualified=!split;
    int independentWrites=0;
    bool agreement=true,fired=false,expectedFired=false;
    for(int now=0;now<5;++now) {
      auto install=[&](int candidate) {
        if(mode==cache)installed=candidate;
        if(mode==highWater)installed=std::max(installed,candidate);
        if(mode==writerEpoch&&candidate==trueEpoch)writerQualified=true;
        if((mode==scoped||mode==freezeAll)&&candidate==trueEpoch)installed=candidate;
      };
      if(now==ready)install(trueEpoch);
      if(now==old)install(carried.allocation_gen);
      const bool seenCurrent=now>=ready||!split;
      const bool ref=!expectedFired&&now>=issue&&request==trueEpoch&&seenCurrent;
      const bool admit=!fired&&now>=issue&&(mode==writerEpoch?request==trueEpoch&&writerQualified:
        request==installed&&((mode!=scoped&&mode!=freezeAll)||installed==trueEpoch));
      if(admit&&request!=trueEpoch)++wrong[mode];
      expectedFired|=ref;
      fired|=admit;
      if(admit!=ref)agreement=false;
      // Independently named native entity is live at every writer opportunity.
      assert(t.r.entityCompMgr.HasEntity(other));
      if(mode!=freezeAll||installed==trueEpoch)++independentWrites;
    }
    if(mode==writerEpoch||mode==scoped)assert(agreement&&independentWrites==5);
    if(mode==scoped){
      assert(fired==(request==trueEpoch&&(!split||ready<=4)));
      if(split&&ready==5)assert(!fired&&independentWrites==5);
    }
    if(agreement&&independentWrites==5)++passed[mode];
    if(fired&&request==trueEpoch)++settle[mode];
    independent[mode]+=independentWrites;
    ++rows;
  }
  std::cout<<"episodes "<<rows<<"\n";
  for(int m=0;m<=4;++m)std::cout<<m<<" "<<passed[m]<<" "<<settle[m]<<" "<<wrong[m]<<" "<<independent[m]<<"\n";
}
