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
 const auto write=[&](Gate&g,bool close){g.cmd.command_door(10,g.cm,door,dt,
  close?DoorModeCmp::CLOSE:DoorModeCmp::OPEN);};
 auto advance=[&](Gate&g){
  bool pass=true;
  for(auto j:{1,2}){
   auto &p=g.cm.positions.at(j).data[0];
   p+=dt*g.cm.written.at(j);
   pass&=p>1.-door.params.dx_min;
  }
  return pass;
 };
 auto publish=[&](Gate &g,int tick){
  g.cmd.publish_state(9.+tick*dt,"gate",g.cmd.get_current_mode(10,g.cm,door));
  return phase(g.cmd.sink.record,hb);
 };
 int swapped,closing,expiry,probe,link,deadline;
 while(std::cin>>swapped>>closing>>expiry>>probe>>link>>deadline){
   std::array<Gate,3> g;
   int init=0;
   write(g[0],false);
   assert(g[0].cm.written.at(1)==0);
   for(int j:{0,1}){
    const int prior=j==swapped?5:2;
    for(int i=0;i<prior;i++)write(g[j],true);
    assert(exact_known_open(g[j].cmd,10,g[j].cm,door));
   }
   // t0: the public OPEN result and session are current and complete.
   for(int j:{0,1}){write(g[j],false);assert(publish(g[j],0));}
   const int nowSample=g[0].cm.written.at(1)<-2./64;
   int evidence=-1,t0=probe?1:0,unrelated=0;
   if(probe&&link)evidence=probe==1?init:nowSample;
   auto target=[&](int gate,int tick){
     return tick>=1&&gate==closing&&tick>=expiry;
   };
   auto step=[&](int tick){
     bool pass[2];
     for(int k:{0,1}){if(tick)write(g[k],target(k,tick));pass[k]=advance(g[k]);}
     write(g[2],true);
     advance(g[2]);++unrelated;
     return std::array<bool,2>{pass[0],pass[1]};
   };
   for(int t=0;t<t0;t++)step(t);
   assert(publish(g[0],t0)&&publish(g[1],t0));
   std::cout<<"L "<<evidence<<" "<<t0<<std::endl;
   int gate,wait;assert(std::cin>>gate>>wait&&gate>=-1&&gate<=1&&wait>=0);
   const int enter=t0+wait,end=enter+4;
   bool good=gate>=0&&end<=deadline;
   bool badInterval=false;
   int observedSteps=0; 
   for(int t=t0;t<deadline;t++){
     if(gate>=0&&t==enter){
       for(int j:{1,2})badInterval|=g[gate].cm.positions.at(j).data[0]<=1.-door.params.dx_min;
     }
     auto ok=step(t);
     if(gate>=0&&enter<=t&&t<end){
       badInterval|=!ok[gate];
       ++observedSteps;
     }
   }
   // The authored velocity-following law is linear between checked endpoints.
   good &= !badInterval&&observedSteps==4;
   assert(unrelated==deadline);
   std::cout<<"O "<<good<<" "<<unrelated<<" "<<observedSteps<<std::endl;
 }
}
