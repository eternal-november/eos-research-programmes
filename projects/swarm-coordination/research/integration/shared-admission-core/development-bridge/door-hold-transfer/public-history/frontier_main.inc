struct Gate {
 Gz cmd;
 EntityComponentManager cm;
 Gate(){
  cm.names={{{10,"left"},1},{{10,"right"},2}};
  cm.positions={{1,{{1.}}},{2,{{1.}}}};
 }
};
int main(){
 constexpr double dt=1./8;
 const DoorData door{{{"left",1.,0.},{"right",1.,0.}},
  {.v_max=1./4,.a_max=1./8,.a_nom=1./8,.dx_min=1./64}};
 const SupervisorHeartbeat hb={{{"gate",{{"crew",{8,0}}}}},{9,0}};
 auto write=[&](Gate&g,bool close){g.cmd.command_door(10,g.cm,door,dt,close?DoorModeCmp::CLOSE:DoorModeCmp::OPEN);};
 auto advance=[&](Gate&g){
  for(auto j:{1,2})g.cm.positions.at(j).data[0]+=dt*g.cm.written.at(j);
 };
 auto observe=[&](Gate&g,int tick){
   g.cmd.publish_state(9.+tick*dt,"gate",g.cmd.get_current_mode(10,g.cm,door));
   return phase(g.cmd.sink.record,hb);
 };
 int sw,closing,expiry,kind,sampled,delivered,deadline;
 while(std::cin>>sw>>closing>>expiry>>kind>>sampled>>delivered>>deadline){
   assert(sampled<=delivered&&delivered<=deadline&&deadline<=12);
   std::array<Gate,3> gates;
   std::array<std::vector<int>,2> aperture, report;
   for(int i:{0,1}){
     for(int k=0;k<(i==sw?5:2);k++)write(gates[i],true);
     assert(exact_known_open(gates[i].cmd,10,gates[i].cm,door));
     write(gates[i],false);
   }
   const int writer=gates[0].cm.written.at(1)<-2./64;
   auto read=[&](int t){
    for(int i:{0,1}){
     auto &g=gates[i];
     const double p=g.cm.positions.at(1).data[0];
     assert(p==g.cm.positions.at(2).data[0]);
     const int a=int((p-1.)*512.);
     assert(a==(p-1.)*512.);
     aperture[i].push_back(a);report[i].push_back(observe(g,t));
    }
   };
   int independent=0;
   auto step=[&](int t){
     for(int i:{0,1}){
       if(t>0)write(gates[i],i==closing&&t>=expiry);
       advance(gates[i]);
     }
     write(gates[2],true);advance(gates[2]);++independent;
     read(t+1);
   };
   read(0);assert(report[0][0]&&report[1][0]);
   for(int t=0;t<delivered;t++)step(t);
   std::cout<<"L";
   if(kind==4)std::cout<<" "<<writer;
   for(int i:{0,1}){
     if(kind==1)std::cout<<" "<<report[i][sampled];
     if(kind==2){
       int bits=0;
       for(int t=0;t<=sampled;t++)bits|=report[i][t]<<t;
       std::cout<<" "<<bits;
     }
     if(kind==3){
       int loss=-1;for(int t=0;t<=sampled;t++)if(!report[i][t]){loss=t;break;}
       std::cout<<" "<<loss;
     }
   }
   std::cout<<std::endl;
   int g,enter;assert(std::cin>>g>>enter&&g>=-1&&g<=1);
   for(int t=delivered;t<deadline;t++)step(t);
   bool yes=g>=0&&enter>=delivered&&enter+4<=deadline;
   if(yes)for(int t=enter;t<=enter+4;t++)yes&=aperture[g][t]>-8;
   assert(independent==deadline);
   std::cout<<"O "<<yes<<" "<<independent;
   for(auto &gt:aperture)for(int u:gt)std::cout<<" "<<u;
   std::cout<<std::endl;
 }
}
