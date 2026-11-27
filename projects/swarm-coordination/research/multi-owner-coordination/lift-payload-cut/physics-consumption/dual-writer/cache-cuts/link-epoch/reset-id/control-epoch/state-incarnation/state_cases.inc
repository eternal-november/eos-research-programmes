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
int main(){
  unsigned batches=0,branches=0;
  for(int lead=0;lead<4;++lead)
  for(int rounds=1;rounds<=5;++rounds)
  for(int schedule=0;schedule<(1<<rounds);++schedule){
    Trial t;t.start();
    auto e=t.claim();
    for(int k=0;k<lead;++k)t.r.entityCompMgr.CreateEntity();
    t.r.entityCompMgr.ClearNewlyCreatedEntities();
    unsigned lives=1;
    for(int k=0;k<rounds;++k){
      const bool split=(schedule>>k)&1;
      t.submit(true);
      if(split){
        assert(!t.drain()&&!t.r.entityCompMgr.HasEntity(t.watched));
      }
      t.submit(false);
      assert(t.drain()==split);
      lives+=split;
      assert(t.r.entityCompMgr.HasEntity(t.watched));
      assert(!t.r.entityCompMgr.dataPtr->newlyCreatedEntities.contains(t.watched));
      assert(t.r.entityCompMgr.dataPtr->entityCount==t.watched+lead+k);
      const auto other=t.r.entityCompMgr.CreateEntity(); // independently owed allocation
      assert(other==t.watched+lead+k+1);
      assert(t.r.entityCompMgr.HasEntity(other));
      t.r.entityCompMgr.ClearNewlyCreatedEntities();
      // Effective restoration is possible while an independent entity stays live.
      if(lead)assert(t.r.entityCompMgr.HasEntity(t.watched+lead));
      assert(accept(e,t.claim(),false));
      assert(accept(e,t.claim(),true)==(lives==1));
      assert(t.claim().allocation_gen==int(lives));
      ++branches;
    }
    ++batches;
  }
  std::cout<<batches<<" control schedules, "<<branches<<" live-state update pairs and unrelated allocations\n"
     <<"same queued deletion/restoration: coalescing leaves original, distinct application cuts recreate same number\n"
     <<"newly-created witness is transient; world era and clock remain unchanged across qualified explicit-ID creation\n";
}
