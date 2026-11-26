#define main inherited_radio_main
#include "replay.cpp"
#undef main

int main(){
 unsigned cap,a,b,alias,t8,early,shared;
 while(std::cin>>cap>>a>>b>>alias>>t8>>early>>shared){
  World w(cap);
  std::map<std::string,unsigned> calls;
  for(std::string s:{"R0","R1","Side","Depot"}){
   auto n=std::make_shared<TeamNode>();
   n->name=s;n->radio=w.b.team->at("P")->radio;
   w.b.team->emplace(s,n);
  }
  auto bind=[&](std::string topic,std::string endpoint){
   w.b.endpoints[topic+":7"]={{endpoint}};
   w.app.callbacks[topic+":7"]=[&,topic](auto,auto,auto,const auto& data){
     assert(!data.empty());++calls[topic];
   };
  };
  auto run=[&](std::string src,std::string dst,unsigned size,double t){
   now=t;
   w.b.incomingMsgs.push_back({src,dst,std::string(size,'a')});
   w.b.DispatchMessages();
   assert(w.b.incomingMsgs.empty());
  };
  bind("Old","R0"); bind("Peer","R1"); bind("Other","Depot");
  if(early)run(shared?"P":"Q","Peer",b,0.);
  run("Side","Other",1,0.);
  const double t=t8/8.0;
  if(alias)bind("Old","R1");
  run("P","Old",a,t);
  if(!early)run(shared?"P":"Q","Peer",b,t+1.25);
  std::cout<<calls["Old"]<<' '<<calls["Peer"]<<' '<<calls["Other"]<<'\n';
 }
}
