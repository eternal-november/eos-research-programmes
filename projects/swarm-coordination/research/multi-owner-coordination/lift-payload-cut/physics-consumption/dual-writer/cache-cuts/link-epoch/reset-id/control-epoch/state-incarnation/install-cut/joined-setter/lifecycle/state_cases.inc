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
int main(){return 0;}
