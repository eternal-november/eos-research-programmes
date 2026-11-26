#define main inherited_radio_main
#include "replay.cpp"
#undef main

int main(){
 unsigned cap,a,b,mode,rx,who,cut;
 while(std::cin>>cap>>a>>b>>mode>>rx>>who>>cut){
  World w(cap);
  std::map<std::string,unsigned> seen;
  for(std::string s:{"R0","R1","Far","Side","Seed"}){
   auto n=std::make_shared<TeamNode>(); n->name=s;n->radio=w.b.team->at("P")->radio;
   w.b.team->emplace(s,n);
  }
  auto bind=[&](std::string name,std::string dst){
   w.b.endpoints[name+":7"]={{dst}};
   w.app.callbacks[name+":7"]=[&,name](auto,auto,auto,const auto& bytes){assert(!bytes.empty());++seen[name];};
  };
  auto send=[&](std::string s,std::string dst,unsigned bytes,double cut,bool clear=true){
   now=cut;
   w.path_available=clear;
   w.b.incomingMsgs.push_back({s,dst,std::string(bytes,'a')});
   w.b.DispatchMessages();
   assert(w.b.incomingMsgs.empty());w.path_available=true;
  };
  bind("seed","R0");bind("earlier","R0");
  bind("side","Far");bind("final",rx?"R0":"R1");
  if(mode==3)send("Seed","seed",cap,0);
  unsigned seed=w.state("R0").bytes_received_this_epoch;
  unsigned base=w.state("P").bytes_sent_this_epoch;
  if(mode)send("P","earlier",b,0,mode!=1);
  unsigned tx=w.state("P").bytes_sent_this_epoch-base;
  unsigned radi=w.state("R0").bytes_received_this_epoch-seed;
  send("Side","side",1,.5);
  send(who?"Q":"P","final",a,cut/4.);
  std::cout<<seed<<' '<<tx<<' '<<radi<<' '<<seen["earlier"]
   <<' '<<seen["side"]<<' '<<seen["final"]<<'\n';
 }
}
