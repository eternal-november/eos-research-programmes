#define main previous_replay
#include "staged_replay.inc"
#undef main

int main(){
 int initial,side_to,reply_first,cap,arm;
 while(std::cin>>initial>>side_to>>reply_first>>cap>>arm){
  World w(cap);
  auto D=std::make_shared<TeamNode>();
  D->name="D";D->radio.capacity=8*4;
  D->radio.pathloss_f=[](double,auto&,auto&,bool& old){old=false;return Power{100,0};};
  w.b.team->emplace("D",D);w.b.endpoints["D:7"]={{"D"}};
  w.b.team->at("P")->radio.capacity=8*16;
  int settled=0, refused=0, side=0, reply=0,moves=0, delivered=0;
  std::string return_payload;
  w.app.callbacks["D:7"]=[&](auto from,auto,auto,auto body){
    if(from=="P"){assert(body=="side");++side;return;}
    assert(from=="Q");++delivered;
    // The native broker has already charged the transfer before this
    // callback. Admit an independent local event before effect execution.
    std::cout<<"L"<<std::endl;int live;assert(std::cin>>live && 0<=live && live<=2);
    int named=body=="owea"?0:body=="oweb"?1:2;
    int k=2;
    if(arm==0){assert(named<2);if(named==live)k=named;}
    else if(arm==1){assert(body=="owed");if(live<2)k=live;}
    else{assert(body=="owed");if(live==0)k=0;else if(live==1)k=1;}
    if(k==2){++refused;return;}
    assert(k==live);++moves;
    std::cout<<"M "<<k<<std::endl;int effect;assert(std::cin>>effect && effect==1);
    ++settled;
    return_payload=(k==0?"done":"DONE");
  };
  w.app.callbacks["Q:7"]=[&](auto from,auto,auto,auto body){
   if(from=="P"){assert(body=="side");++side;}
   else{assert(from=="D"&&body==return_payload);++reply;}
  };
  auto send=[&](std::string src,std::string dst,std::string body,double t){
   now=t;w.b.incomingMsgs.push_back({src,dst,body});w.b.DispatchMessages();
   assert(w.b.incomingMsgs.empty());
  };
  const double t=1.;
  auto side_send=[&]{
   if(side_to<2)send("P",side_to==0?"D":"Q","side",t);
  };
  if(!reply_first) side_send();
  // All arms know the same dock/RF debit. Reversing side traffic is
  // permitted only under the separate scheduling condition in the grid.
  bool permit=w.state("D").bytes_received_this_epoch+4<=unsigned(cap);
  if(permit){
   send("Q","D",arm==0?(initial==0?"owea":"oweb"):"owed",t);
   if(!return_payload.empty())send("D","Q",return_payload,t);
  }
  if(reply_first) side_send();
  std::cout<<"O "<<settled<<" "<<refused<<" "<<side<<" "<<reply<<" "<<moves<<" "<<delivered
            <<" "<<w.state("Q").bytes_sent_this_epoch<<" "<<w.state("D").bytes_sent_this_epoch
            <<std::endl;
 }
}
