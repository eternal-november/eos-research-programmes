struct S {
  Tr t;
  int mb=0, ss=0, xr=0, zr=0;
  void command(int v,int eid){ t.publish(v);mb=eid; }
  void latch(){ t.latch();ss=mb; }
  void horizontal(){ t.robot.use(t.ecs);xr=ss;zr=0; } // selected vector write
  void vertical(){ t.lift.write(t.ecs,1,.625);zr=1; }
  void setter(){
    assert(t.ecs.commands.contains(2));
    t.phys.consume9(t.ecs);
    assert(t.phys.entityFreeGroupMap.calls.size()==1);
    cleanup9(t.ecs);
  }
};
int main(){
  for(int old:{0,1}) for(int arrival:{0,1,2,3,4})
  for(bool z_again:{false,true}) for(int command:{0,1,2,3,4,5,6,7}){
    S s;
    s.command(old,1);
    for(int k=0;k<=4;++k){
      if(k==arrival){
        s.command(0,2);
        if(k>0 && k<4){
          if(command&1)s.latch();
          if(command&2)s.horizontal();
          if((command&4)&&z_again)s.vertical();
        }
      }
      if(k==0)s.latch();
      if(k==1)s.horizontal();
      if(k==2)s.vertical();
      if(k==3)s.setter();
    }
    assert(s.t.robot.cached.targetVel.l.x==0);
    assert((s.t.x()==0)==(old==0||s.xr==2));
    assert(s.t.z()==(s.zr?.625:0.));
    std::cout<<"front "<<old<<' '<<arrival<<' '<<z_again<<' '<<command<<' '
             <<s.xr<<' '<<s.zr<<' '<<s.t.x()<<' '<<s.t.z()<<'\n';
  }
  // The envelope needs both roles at the SAME effect occurrence.
  // Exercise two ordinary legal effects, with different role payloads,
  // in a separate source trace. Independent success at either cut is
  // not a join at one cut.
  Tr t;
  t.publish(0);t.latch();t.robot.use(t.ecs);
  t.phys.consume9(t.ecs);cleanup9(t.ecs);
  const auto x0=t.x(),z0=t.z();
  t.publish(1);t.latch();t.cycle();
  assert(x0==0 && z0==0 && t.x()==1 && t.z()==.625);
  std::cout<<"separate-effects "<<x0<<' '<<z0<<' '<<t.x()<<' '<<t.z()<<'\n';
}
