#define main previous_replay
#include "staged_replay.inc"
#undef main
#include "first_effect.hpp"
#include <array>

int main(){
 int before,after,arm,cap,twice,side_bytes,exact_edge;
 while(std::cin>>before>>after>>arm>>cap>>twice>>side_bytes>>exact_edge){
  World w(cap);
  for(auto who:{"A","B"}){
   auto t=std::make_shared<TeamNode>();
   t->name=who;w.b.team->emplace(who,t);
   w.b.endpoints[std::string(who)+":7"]={{who}};
  }
  w.b.team->at("P")->radio.capacity=8*24;
  int old=0, unrelated=0;
  for(auto who:{"A","B"})w.app.callbacks[std::string(who)+":7"]=[&](auto from,auto,auto,auto data){
   if(from=="P"){assert(data==std::string(side_bytes,'s'));++unrelated;}
   else{assert(from=="Q"&&data=="owed");++old;}
  };
  const std::array<std::string,2> peer={"A","B"};
  auto send=[&](std::string from,int k,double time){
   now=time;
   w.b.incomingMsgs.push_back({from,peer.at(k),from=="Q"?"owed":std::string(side_bytes,'s')});
   w.b.DispatchMessages();
   assert(w.b.incomingMsgs.empty());
  };
  // Ledger aging for reads is functional; no send, callback or RX mutation.
  auto inspect=[&](std::size_t k,double t){
    auto live=[&](const auto& xs){unsigned n=0;for(auto& v:xs)if(v.first>=t-1.)n+=v.second;return n;};
    const auto& tx=w.state("Q");
    const auto& rx=w.state(peer.at(k));
    return live(tx.bytes_sent)+4<=unsigned(cap) && live(rx.bytes_received)+4<=unsigned(cap);
  };
  send("P",before,0.);
  auto chosen=propose(2,[&](std::size_t i){return inspect(i,0.);});
  assert(chosen&&(int(*chosen)==(side_bytes+4<=cap?0:1-before)));
  // The old independent report is real. After its debit expires, a
  // subsequent independent report shifts the busy receiver (or stays put).
  // Both events use the original dispatch and accounting.
  const double t=exact_edge?1.:17./16.;
  if(after<2)send("P",after,t);
  else{send("P",0,t);send("P",1,t);}
  if(arm==0)dispatch_one(2,[&](std::size_t i){return inspect(i,t);},
                              [&](std::size_t i){send("Q",i,t);});
  else if(arm==1){send("Q",*chosen,t);if(!old&&twice)send("Q",1-*chosen,t);}
  else if(arm==2){send("Q",0,t);if(!old&&twice)send("Q",1,t);}
  else if(arm==3){send("Q",1,t);if(!old&&twice)send("Q",0,t);}
  else {
   // Domain-specialized direct policy reads the exact receiver ledgers
   // at the same serialized cut, without using the generic chooser.
   const int k=inspect(0,t)?0:inspect(1,t)?1:-1;
   if(k>=0)send("Q",k,t);
  }
  assert(old<=1);
  std::cout<<old<<" "<<unrelated<<" "<<w.state("Q").bytes_sent_this_epoch<<"\n";
 }
}
