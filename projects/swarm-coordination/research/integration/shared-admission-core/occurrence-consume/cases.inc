struct Scenario {
  Tr t;
  int id=0, nowRank=0, mail=0, sample=0, slot=0;
  void rec(std::string role, int parent, int value, bool good=true){
    std::cout<<++id<<' '<<nowRank<<' '<<role<<' '<<parent<<' '
             <<value<<' '<<good<<'\n';
  }
  void pub(int v,bool allowed){
    t.publish(v);
    rec("mail",0,v,allowed);
    mail=id;
    assert(t.robot.cached.targetVel.l.x==v);
  }
  void latch(){
    t.latch();
    rec("snapshot",mail,t.robot.cached.linearVelocity.x);
    sample=id;
  }
  void write(){
    t.robot.use(t.ecs);
    assert(t.ecs.commands.contains(2));
    rec("slot",sample,t.ecs.commands.at(2).Data().x);
    slot=id;
  }
  void apply(){
    t.lift.write(t.ecs,1,.625);
    t.phys.consume9(t.ecs);
    assert(t.z()==.625);
    rec("setter",slot,t.x());
    cleanup9(t.ecs);
    assert(!t.ecs.commands.contains(2));
  }
};

int main(){
  for (int old:{0,1}) for (int arrive:{0,1,2,3})
  for (bool permit:{false,true}) for (int changes:{0,1,2,3}) {
    Scenario s;
    s.pub(old,true);
    for (int phase=0;phase<=3;++phase) {
      s.nowRank=phase;
      if (phase==arrive) {
        s.pub(0,permit);
        // Only the stated opportunity can run before the deadline.
        // These extra calls are authorized scheduling interventions in
        // the fixture, not implicit Gazebo priority behavior.
        if (phase>0 && phase<3 && (changes&1)) s.latch();
        if (phase>0 && phase<3 && (changes&2)) {
          s.write();
        }
      }
      if (phase==0) s.latch();
      if (phase==1) s.write();
      if (phase==2) s.apply();
    }
    assert(s.t.robot.cached.targetVel.l.x==0);
    std::cout<<"end "<<old<<' '<<arrive<<' '<<permit<<' '<<changes<<' '<<s.t.x()<<'\n';
  }
}
