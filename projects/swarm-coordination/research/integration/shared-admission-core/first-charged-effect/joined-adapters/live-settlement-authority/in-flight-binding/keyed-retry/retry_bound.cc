#define main previous_replay
#include "staged_replay.inc"
#undef main
#include <array>

int main(){
 int load;
 while(std::cin>>load){
  World w(4);
  auto d=std::make_shared<TeamNode>();
  d->name="D";d->radio.capacity=8*4;
  d->radio.pathloss_f=[](double,auto&,auto&,bool& via){via=false;return Power{100,0};};
  w.b.team->emplace("D",d);w.b.endpoints["D:7"]={{"D"}};
  w.b.team->at("P")->radio.capacity=8*16;
  std::string answer,arrived;
  int calls=0,replies=0,side=0;
  w.app.callbacks["D:7"]=[&](auto from,auto,auto,auto body){
    assert(from=="Q"&&body=="owed");
    std::cout<<"C "<<calls++<<std::endl;
    int ok;assert(std::cin>>ok&&0<=ok&&ok<=1);
    if(!ok){answer.clear();return;}
    std::array<int,4> bytes;
    for(auto& b:bytes)assert(std::cin>>b&&0<=b&&b<=255);
    answer.clear();for(auto b:bytes)answer.push_back(char(b));
  };
  w.app.callbacks["Q:7"]=[&](auto from,auto,auto,auto body){
    if(from=="P"){assert(body=="side");++side;}
    else {assert(from=="D"&&body==answer&&body.size()==4);arrived=body;++replies;}
  };
  auto send=[&](std::string from,std::string to,std::string data,double t){
    now=t;
    w.b.incomingMsgs.push_back({from,to,data});w.b.DispatchMessages();
    assert(w.b.incomingMsgs.empty());
  };
  if(load)send("P","Q","side",1.);
  send("Q","D","owed",1.);
  assert(answer.size()==4);
  send("D","Q",answer,1.);
  int first_reply=replies;
  int first_tx=w.state("D").bytes_sent_this_epoch;
  if(!replies){
    send("Q","D","owed",2.+1./16.);
    if(!answer.empty())send("D","Q",answer,2.+1./16.);
  }
  std::cout<<"O "<<calls<<" "<<replies<<" "<<side<<" "<<first_reply<<" "<<first_tx;
  for(unsigned char b:arrived)std::cout<<" "<<int(b);
  std::cout<<std::endl;
 }
}
