#define main previous_replay
#include "staged_replay.inc"
#undef main
#include "first_effect.hpp"
#include <array>

int main(){
 int early,late,mode,cap,edge,arm;
 while(std::cin>>early>>late>>mode>>cap>>edge>>arm){
  World w(cap);
  const std::array<std::string,3> peer={"A","B","C"};
  for(auto who:{"A","B","C","H"}){
    auto n=std::make_shared<TeamNode>();n->name=who;
    w.b.team->emplace(who,n);
    w.b.endpoints[std::string(who)+":7"]={{who}};
  }
  w.b.team->at("P")->radio.capacity=8*24;
  w.b.team->at("H")->radio.capacity=8*16;
  w.b.team->at("H")->radio.pathloss_f=[=](double,auto&,auto&,bool& via){
    via=false;return Power{mode==1?-std::numeric_limits<double>::infinity():100.,0};
  };
  unsigned receipts=0,settled=0,side=0,refused=0,actuator=0;
  std::array<int,2> grant={0,0};
  // Ground truth authority is supplied by the local source after its
  // recorded motion. The selector sees only a grant that really arrives.
  int owner;
  for(int k:{0,1,2})w.app.callbacks[peer[k]+":7"]=[&,k](auto from,auto,auto,auto data){
   if(from=="P"){assert(data=="side");++side;}
   else if(from=="H"){
     assert(k<2 && (data=="n"||data=="g"));
     grant[k]=data=="n"?8:7;++receipts;
   }else{
     assert(from=="Q"&&data=="owed");
     if(k!=owner||grant[k]!=8){++refused;return;}
     ++actuator;
     std::cout<<"M "<<k<<std::endl;
     int effect;assert(std::cin>>effect && 0<=effect && effect<=1);
     settled+=effect;
   }
  };
  auto send=[&](std::string from,int to,std::string data,double t){
    now=t;w.b.incomingMsgs.push_back({from,peer[to],data});w.b.DispatchMessages();
    assert(w.b.incomingMsgs.empty());
  };
  send("P",early,"side",-2); // same independent prefix in all comparisons
  std::cout<<"P"<<std::endl;
  assert(std::cin>>owner&&0<=owner&&owner<=2);
  if(owner<2)send("H",owner,mode==2?"g":"n",0.);
  const double t=edge==0?1.:17./16.;
  if(late==2){send("P",0,"side",t);send("P",1,"side",t);}
  else send("P",late==3?2:late,"side",t);
  std::cout<<"L"<<std::endl; // later native physical interference, if any
  int ready;assert(std::cin>>ready&&ready==1);
  auto radio=[&](std::size_t k){
   auto live=[&](const auto& xs){unsigned n=0;for(auto& v:xs)if(v.first>=t-1.)n+=v.second;return n;};
   return live(w.state("Q").bytes_sent)+4<=unsigned(cap) &&
          live(w.state(peer[k]).bytes_received)+4<=unsigned(cap);
  };
  auto physical=[&](std::size_t k){
   std::cout<<"I "<<k<<std::endl;int accessible;
   assert(std::cin>>accessible&&0<=accessible&&accessible<=1);return accessible!=0;
  };
  auto commit=[&](std::size_t k){send("Q",k,"owed",t);};
  auto joined=[&](std::size_t k){return grant[k]==8&&radio(k)&&physical(k);};
  if(arm==0)dispatch_one(2,joined,commit);
  else if(arm==1){
    // Factored direct comparator, same information and effects.
    if(grant[0]==8 && radio(0) && physical(0))commit(0);
    else if(grant[1]==8 && radio(1) && physical(1))commit(1);
  }else if(arm==2){
    // Cached prior owner. Receipt may arrive but cannot authorize that action.
    if(radio(1-early)&&physical(1-early))commit(1-early);
  }else{
    // Grant and budget, without rereading access after interference.
    if(grant[0]==8&&radio(0))commit(0);
    else if(grant[1]==8&&radio(1))commit(1);
  }
  std::cout<<"O "<<settled<<" "<<receipts<<" "<<refused<<" "<<actuator<<" "<<side
           <<" "<<w.state("Q").bytes_sent_this_epoch<<std::endl;
 }
}
