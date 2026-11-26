struct Episode {
 std::shared_ptr<TaskManager> m=std::make_shared<TaskManager>();
 std::shared_ptr<TaskManager::Interruption> a=std::make_shared<TaskManager::Interruption>();
 std::shared_ptr<TaskManager::Interruption> b=std::make_shared<TaskManager::Interruption>();
 int ready_a=0,ready_b=0;
 explicit Episode(int mode){
   m->_active_task.v=std::make_unique<Task>("work");
   if(mode&1)m->_emergency_pullover.v=std::make_unique<Task>("pullover");
   if(mode&2)m->_waiting.v=std::make_unique<Task>("wait");
   a->w_mgr=m;b->w_mgr=m;
   m->interrupt_robot(a,{"operator task handoff"},[this]{ready_a++;});
   m->interrupt_robot(b,{"independent valid hold"},[this]{ready_b++;});
 }
 bool paused()const{
    for(auto* t:{&m->_active_task,&m->_emergency_pullover,&m->_waiting})
      if(*t&&!t->is_interrupted())return false;
    return true;
 }
 void internally_ready(){
    for(auto* t:{&m->_active_task,&m->_emergency_pullover,&m->_waiting})
      if(*t)t->v->internally_ready();
    m->_context->worker().drain();
    assert(ready_a==1&&ready_b==1&&paused());
 }
 bool retain_own_hold()const{
    if(a->resumed || ready_a!=1)return false;
    for(auto* t:{&m->_active_task,&m->_emergency_pullover,&m->_waiting})
      if(*t&&!t->v->holds.contains(a->token_map.at(t->id())))return false;
    return true;
 }
 void release_a(){
    a->resume({"handoff withdrawn"});
    m->_context->worker().drain();
 }
 void release_b(){
    b->resume({"independent hold withdrawn"});
    m->_context->worker().drain();
 }
};
int main(){
 int checked=0;
 for(int mode=0;mode<4;mode++){
   Episode live(mode),released(mode);
   live.internally_ready();released.internally_ready();
   released.release_a();
   assert(live.paused()&&released.paused());
   assert(live.ready_a==released.ready_a&&live.ready_b==released.ready_b);
   assert(live.retain_own_hold()&&!released.retain_own_hold());
   // A checked actuator predicate is explicitly external to the native task callback.
   for(bool measured_clear:{false,true})for(bool authorized:{false,true}){
     assert((live.retain_own_hold()&&authorized&&measured_clear)==(authorized&&measured_clear));
     assert(!(released.retain_own_hold()&&authorized&&measured_clear));
     checked++;
   }
   released.release_b();assert(!released.paused());
 }
 std::cout<<checked<<" paired cases: once-ready and task paused do not identify the operator's own retained hold\n"
          <<"independent hold still stops task release, but supplies no modeled actuation permission to the withdrawn operator\n"
          <<"fixture guards require separate plant evidence; no native standstill check invoked\n";
}
