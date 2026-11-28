struct Gate {
  Gz cmd;
  EntityComponentManager cm;
  Gate() {
    cm.names={{{10,"left"},1},{{10,"right"},2}};
    cm.positions={{1,{{1.}}},{2,{{1.}}}};
  }
};
int main(){
  constexpr double dt=1./8;
  const DoorData door{{{"left",1.,0.},{"right",1.,0.}},
    {.v_max=1./4,.a_max=1./8,.a_nom=1./8,.dx_min=1./64}};
  const SupervisorHeartbeat hb={{{"gate",{{"crew",{8,0}}}}},{9,0}};
  auto write=[&](Gate& g, bool close){
    g.cmd.command_door(10,g.cm,door,dt,close?DoorModeCmp::CLOSE:DoorModeCmp::OPEN);
  };
  auto status=[&](Gate& g){
    g.cmd.publish_state(9.,"gate",g.cmd.get_current_mode(10,g.cm,door));
    return int(phase(g.cmd.sink.record,hb));
  };
  int first,second,report,plan,writer;
  while(std::cin>>first>>second>>report>>plan>>writer){
    assert(-1<=first&&first<2&&-1<=second&&second<2);
    Gate gates[4]; // 0/1 share with OLD, 2 is alternate, 3 independent
    for(int t=0;t<=2;t++){
      for(int g=0;g<=2;g++){write(gates[g],false);assert(status(gates[g])==1);}
      write(gates[3],true);
    }
    // Repair recreates the command path under the same door/joint identifiers.
    // Exact authority is supplied by reopened journal, not stock DoorState.
    for(int g=0;g<=1;g++)gates[g].cmd._last_cmd_vel.clear();
    std::cout<<"C "<<status(gates[0])<<" "<<status(gates[1])<<" "
      <<(report?first:-2)<<std::endl;
    int action;assert(std::cin>>action);
    assert(-1<=action&&action<3);
    bool authorized=true,unrelated=true,old=true;
    bool path=action>=0&&bool(plan&(1<<action));
    int maxdip=0, minother=0, early=-2;
    for(int t=3;t<=7;t++){
      int active=t==3?first:second;
      for(int g=0;g<4;g++){
        const bool due=active==g && g<2;
        const bool close=(g==3) || (g<2 && (writer==0?due:writer==1?true:writer==2?due&&g!=action:writer==3?first==g:due&&t==3));
        write(gates[g],close);
        const auto v=gates[g].cm.written.at(1);
        if(g<2){
          authorized=authorized&&(!close||due);
          if(due)old=old&&close&&v<0;
        }
        if(g==3){
          unrelated=unrelated&&v<0;
          minother=std::min(minother,int(std::lround(64*v)));
        }
        for(auto j:{1,2}){
          assert(gates[g].cm.written.at(j)==v);
          gates[g].cm.positions.at(j).data[0]+=dt*v;
        }
      }
      if(action>=0){
        const int d=std::lround(512*(1-gates[action].cm.positions.at(1).data[0]));
        if(t==3)early=d;
        maxdip=std::max(maxdip,d);
        path=path&&d<8;
      }
    }
    std::cout<<"O "<<path<<" "<<old<<" "<<authorized<<" "<<unrelated<<" "
      <<maxdip<<" "<<early<<" "<<minother<<std::endl;
  }
}
