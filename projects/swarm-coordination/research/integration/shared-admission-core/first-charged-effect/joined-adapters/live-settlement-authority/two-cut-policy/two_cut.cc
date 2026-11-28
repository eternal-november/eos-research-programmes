#define main previous_replay
#include "staged_replay.inc"
#undef main
#include <array>
int main(){
 int side_route,label;
 while(std::cin>>side_route>>label){
  int route=-1,known=2;
  World w(4);
  const std::array<std::string,3> peer={"D0","D1","D2"};
  for(auto addr:peer){
   auto node=std::make_shared<TeamNode>();
   node->name=addr;node->radio.capacity=8*4;
   node->radio.pathloss_f=[](double,auto&,auto&,bool& b){b=false;return Power{100,0};};
   w.b.team->emplace(addr,node);w.b.endpoints[addr+":7"]={{addr}};
  }
  w.b.team->at("P")->radio.capacity=8*16;
  int side=0,arrived=0,reply=0,effects=0;
  std::string result;
  for(int k:{0,1,2})w.app.callbacks[peer[k]+":7"]=[&,k](auto from,auto,auto,auto data){
   if(from=="P"){assert(data=="side");++side;return;}
   assert(from=="Q"&&data=="owed"&&k==route);++arrived;
   std::cout<<"L "<<k<<std::endl;
   int actual;assert(std::cin>>actual&&0<=actual&&actual<=2);
   if(actual<2){++effects;result=actual==0?"done":"DONE";}
  };
  w.app.callbacks["Q:7"]=[&](auto from,auto,auto,auto payload){
   if(from=="P"){assert(payload=="0"||payload=="1");known=payload=="0"?0:1;return;}
   assert(route>=0&&from==peer[route]&&payload==result);++reply;
  };
  auto send=[&](std::string src,std::string dst,std::string data,double at=1.){
   now=at;w.b.incomingMsgs.push_back({src,dst,data});w.b.DispatchMessages();
   assert(w.b.incomingMsgs.empty());
  };
  if(label<2)send("P","Q",label==0?"0":"1",-2.);
  send("P",peer.at(side_route),"side");
  std::cout<<"E "<<known<<std::endl;
  assert(std::cin>>route&&-1<=route&&route<=1);
  // Sender has neither receiver's private ledger nor the later actor.
  if(route>=0){
   send("Q",peer.at(route),"owed");
   if(!result.empty())send(peer.at(route),"Q",result);
  }
  std::cout<<"O "<<side<<" "<<arrived<<" "<<effects<<" "<<reply<<" "<<w.state("Q").bytes_sent_this_epoch<<std::endl;
 }
}
