#define main previous_main
#include <replay.cpp>
#undef main

int main(){
 std::unique_ptr<World> w;
 std::map<std::string,std::string> bodies;
 std::vector<std::string> got;
 std::string cmd;
 auto decode=[](const std::string& h){
   assert(h.size()%2==0);
   std::string v;
   for(size_t i=0;i<h.size();i+=2)v+=char(std::stoi(h.substr(i,2),nullptr,16));
   return v;
 };
 while(std::cin>>cmd){
  if(cmd=="reset"){
   unsigned p,q,station;std::cin>>p>>q>>station;
   now=0;got.clear();bodies.clear();
   w=std::make_unique<World>(900);
   w->b.team->at("P")->radio.capacity=8*p;
   w->b.team->at("Q")->radio.capacity=8*q;
   w->b.team->at("Base")->radio.capacity=8*station;
   for(auto id:{"R","Home","Independent"}){
     auto m=std::make_shared<TeamNode>(*w->b.team->at("Base"));
     m->radio.capacity=8*900;m->name=id;(*w->b.team)[id]=m;
   }
   for(const std::string dest:{"Base","Home","Independent"}){
    if(dest!="Base")w->b.endpoints[dest+":7"].push_back({dest});
    w->app.callbacks[dest+":7"]=[&,dest](auto s,auto,auto,auto body){
      assert(bodies.at(s+":"+dest)==body);
      got.push_back(s+":"+dest);
    };
   }
   std::cout<<"ok"<<std::endl;
  } else if(cmd=="append"){
   std::string s,d,h;std::cin>>s>>d>>h;
   auto payload=decode(h);
   bodies[s+":"+d]=payload;
   w->b.incomingMsgs.push_back({s,d,payload});
   std::cout<<"ok"<<std::endl;
  } else if(cmd=="run"){
   unsigned t;std::cin>>t;now=t/4.;got.clear();
   w->b.DispatchMessages();
   std::cout<<got.size();
   for(const auto& item:got)std::cout<<' '<<item;
   std::cout<<std::endl;
  } else if(cmd=="ledger"){
   std::string s;std::cin>>s;
   const auto& x=w->state(s);
   unsigned tx=0,rx=0;
   for(auto [t,b]:x.bytes_sent)if(now-t<=1.)tx+=b;
   for(auto [t,b]:x.bytes_received)if(now-t<=1.)rx+=b;
   std::cout<<tx<<' '<<rx<<std::endl;
  } else assert(false);
 }
}
