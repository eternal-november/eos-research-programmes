struct Gate {
  Gz cmd;
  EntityComponentManager cm;
  Gate() {
    cm.names={{{10,"left"},1},{{10,"right"},2}};
    cm.positions={{1,{{1.}}},{2,{{1.}}}};
  }
};
int main() {
  constexpr double dt=1./8;
  const DoorData door{{{"left",1.,0.},{"right",1.,0.}},
    {.v_max=1./4,.a_max=1./8,.a_nom=1./8,.dx_min=1./64}};
  const SupervisorHeartbeat hb={{{"gate",{{"crew",{8,0}}}}},{9,0}};
  auto write=[&](Gate& g, bool close) {
    g.cmd.command_door(10,g.cm,door,dt,close?DoorModeCmp::CLOSE:DoorModeCmp::OPEN);
  };
  int prior,rotate,arrive,tag,hold,mode;
  while(std::cin>>prior>>rotate>>arrive>>tag>>hold>>mode) {
    Gate main, other;
    for(int i=0;i<prior;i++)write(main,true);
    bool remembered=false;
    for(int t=0;t<9;t++) {
      const int epoch=t>=rotate;
      if(mode==2&&t==rotate)remembered=false; // flush-before-arrival
      if(t==arrive)remembered=mode!=1||tag==epoch;
      const bool sameScope=t>=hold;
      const bool effective=remembered&&sameScope&&(mode!=3&&mode!=5||tag==epoch);
      write(main,effective);
      const bool independent=t>=1&&(mode!=5||sameScope);
      write(other,independent);
      if(t==0) {
        main.cmd.publish_state(9.,"gate",main.cmd.get_current_mode(10,main.cm,door));
        assert(phase(main.cmd.sink.record,hb));
      }
      const int mv=std::lround(64*main.cm.written.at(1));
      const int ov=std::lround(64*other.cm.written.at(1));
      for(auto *g:{&main,&other}) for(auto j:{1,2}) {
        const auto v=g->cm.written.at(j);
        assert(v==g->cm.written.at(1));
        g->cm.positions.at(j).data[0]+=dt*v;
      }
      std::cout<<effective<<" "<<independent<<" "<<mv<<" "<<ov<<" "
        <<std::lround(512*(1-main.cm.positions.at(1).data[0]))<<";";
    }
    std::cout<<std::endl;
  }
}
