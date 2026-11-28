#define main previous_replay
#include "staged_replay.inc"
#undef main
#include <array>
int main(){
 int side_route,cap,probe,with_side,when;
 while(std::cin>>side_route>>cap>>probe>>with_side>>when){
  World w(cap);
  const std::array<std::string,3> peer={"D0","D1","D2"};
  for(auto addr:peer){
   auto node=std::make_shared<TeamNode>();
   node->name=addr;node->radio.capacity=8*cap;
   node->radio.pathloss_f=[](double,auto&,auto&,bool& b){b=false;return Power{100,0};};
   w.b.team->emplace(addr,node);w.b.endpoints[addr+":7"]={{addr}};
  }
  w.b.team->at("P")->radio.capacity=8*32;
  int side=0,arrived=0,reply=0,effects=0,diagnostics=0,route=-1;
  std::array<int,3> known={2,2,2};
  std::string result;
  for(int k:{0,1,2})w.app.callbacks[peer[k]+":7"]=[&,k](auto from,auto,auto,auto data){
   if(from=="P"&&data=="side"){++side;return;}
   if(from=="P"){
    assert(data=="0"||data=="1");known[k]=data=="1";++diagnostics;return;
   }
   assert(from=="Q"&&data=="owed"&&k==route);++arrived;
   std::cout<<"L "<<k<<" "<<known[k]<<std::endl;
   int actual;assert(std::cin>>actual&&0<=actual&&actual<=3);
   if(actual<3){++effects;result=std::string(4,char('A'+actual));}
  };
  w.app.callbacks["Q:7"]=[&](auto from,auto,auto,auto payload){
   assert(route>=0&&from==peer[route]&&payload==result);++reply;
  };
  auto send=[&](std::string src,std::string dst,std::string data,double at){
   now=at;w.b.incomingMsgs.push_back({src,dst,data});w.b.DispatchMessages();
   assert(w.b.incomingMsgs.empty());
  };
  if(with_side)send("P",peer.at(side_route),"side",0.1875);
  std::cout<<"E"<<std::endl;
  assert(std::cin>>route&&-1<=route&&route<=1);
  if(route>=0){
   if(probe&(1<<route)){
    std::cout<<"S "<<route<<std::endl;
    int bit;assert(std::cin>>bit&&(bit==0||bit==1));
    send("P",peer.at(route),bit?"1":"0",when?0.875:0.25);
   }
   send("Q",peer.at(route),"owed",1.125);
   if(!result.empty())send(peer.at(route),"Q",result,1.125);
  }
  std::cout<<"O "<<side<<" "<<diagnostics<<" "<<arrived<<" "<<effects<<" "<<reply
           <<" "<<w.state("Q").bytes_sent_this_epoch<<std::endl;
 }
}
