#define main previous_replay
#include "staged_replay.inc"
#undef main
#include "first_effect.hpp"
#include <array>

int main(){
 int before,after,arm,edge;
 while(std::cin>>before>>after>>arm>>edge){
  // Ordinary source simulation; all commands and actual Q deliveries use
  // original native broker, as does the competing independent traffic.
  World w(4);
  for (auto who:{"A","B","C"}){
    auto t=std::make_shared<TeamNode>();t->name=who;
    w.b.team->emplace(who,t);w.b.endpoints[std::string(who)+":7"]={{who}};
  }
  w.b.team->at("P")->radio.capacity=8*12;
  unsigned old=0, rx=0, side=0, local_reads=0, last=0;
  const std::array<std::string,3> peer={"A","B","C"};
  for(int k:{0,1,2})w.app.callbacks[peer[k]+":7"]=[&,k](auto from,auto,auto,auto data){
   if(from=="P"){assert(data=="side");++side;}
   else{
    assert(from=="Q"&&data=="owed");
    ++rx;
    std::cout<<"M "<<k<<std::endl;
    unsigned outcome=0;
    assert(std::cin>>outcome && outcome<=2);
    last=outcome;old+=(outcome!=0);
   }
  };
  auto send=[&](const std::string& from,int k,double t){
   now=t;
   w.b.incomingMsgs.push_back({from,peer.at(k),from=="Q"?"owed":"side"});
   w.b.DispatchMessages();
   assert(w.b.incomingMsgs.empty());
  };
  const double t=edge?1.:17./16.;
  send("P",before,0.);
  if(after<2)send("P",after,t);
  else if(after==3)send("P",2,t);
  else{send("P",0,t);send("P",1,t);}
  std::cout<<"P"<<std::endl; // permit actual later source events before asking
  unsigned ready;
  assert(std::cin>>ready&&ready==1);
  auto radio=[&](std::size_t k){
    auto live=[&](const auto& xs){unsigned n=0;for(auto& v:xs)if(v.first>=t-1.)n+=v.second;return n;};
    return live(w.state("Q").bytes_sent)==0 && live(w.state(peer.at(k)).bytes_received)==0;
  };
  auto physical=[&](std::size_t k){
    ++local_reads;
    std::cout<<"I "<<k<<std::endl;
    unsigned free;
    assert(std::cin>>free&&free<=1);
    return free!=0;
  };
  auto commit=[&](std::size_t k){send("Q",k,t);};
  if(arm==0||arm==2)dispatch_one(2,[&](std::size_t k){return radio(k)&&physical(k);},commit);
  else if(arm==1) {if(radio(0)&&physical(0))commit(0);
                   else if(radio(1)&&physical(1))commit(1);}
  else {if(radio(0))commit(0);else if(radio(1))commit(1);}
  std::cout<<"O "<<old<<" "<<rx<<" "<<side<<" "<<w.state("Q").bytes_sent_this_epoch<<" "<<local_reads<<" "<<last<<std::endl;
 }
}
