#define main previous_replay
#include "staged_replay.inc"
#undef main
#include <array>
static std::string raw(std::string h){
 std::string x;
 if(h=="-")return x;
 assert(h.size()%2==0);
 for(size_t i=0;i<h.size();i+=2)x+=char(std::stoi(h.substr(i,2),nullptr,16));
 return x;
}
static std::string hex(const std::string &x){
 static const char * h="0123456789abcdef";
 std::string r;
 for(unsigned char b:x){r+=h[b>>4];r+=h[b&15];}
 return r.empty()?"-":r;
}
int main(){
 int cap,side,dock,bit,fresh,drop;
 std::string early,late;
 while(std::cin>>cap>>side>>dock>>bit>>fresh>>drop>>early>>late){
  World w(cap);
  const std::array<std::string,3> addr={"D0","D1","D2"};
  const std::string at=dock<0?"":addr.at(dock);
  for(auto peer:addr){
   auto node=std::make_shared<TeamNode>();
   node->name=peer;node->radio.capacity=8*cap;
   node->radio.pathloss_f=[](double,auto&,auto&,bool& b){b=false;return Power{100,0};};
   w.b.team->emplace(peer,node);w.b.endpoints[peer+":7"]={{peer}};
  }
  w.b.team->at("P")->radio.capacity=8*32;
  int independent=0,arrived=0,probe=-1; unsigned long traffic=0;
  bool path=true;
  std::string returned,reply,record;
  w.b.team->at("P")->radio.pathloss_f=[&](double,auto&,auto&,bool& b){
    b=false;return Power{path?100:-std::numeric_limits<double>::infinity(),0};};
  for(auto peer:addr)w.app.callbacks[peer+":7"]=[&,peer](auto from,auto,auto,auto data){
   if(from=="P"&&data=="SIDE"){++independent;return;}
   assert(peer==at);
   if(from=="P"){
    if(data=="0"||data=="1")probe=data[0]-'0';else record=data;
    return;
   }
   assert(from=="Q"&&data=="owed");
   ++arrived;std::cout<<"L "<<probe<<" "<<hex(record)<<std::endl;
   std::string answer;assert(std::cin>>answer);reply=raw(answer);
  };
  w.app.callbacks["Q:7"]=[&](auto from,auto,auto,auto data){
   assert(from==at&&!reply.empty()&&data==reply);returned=data;
  };
  auto send=[&](std::string src,std::string dst,std::string data,double t){
   assert(!data.empty());now=t;
   uint64_t live=0;
   for(auto [stamp,n]:w.state(src).bytes_sent)if(stamp>=t-1.)live+=n;
   w.b.incomingMsgs.push_back({src,dst,data});
   w.b.DispatchMessages();assert(w.b.incomingMsgs.empty());
   const auto seen=w.state(src).bytes_sent_this_epoch;
   assert(seen>=live && seen-live==data.size());traffic+=seen-live;
  };
  if(dock>=0&&early!="-")send("P",at,raw(early),0.);
  if(side>=0)send("P",addr.at(side),"SIDE",1.0625);
  if(dock>=0){
   if(bit>=0)send("P",at,bit?"1":"0",fresh?2.:1.125);
   if(late!="-"){
    path=!drop;send("P",at,raw(late),2.);path=true;
   }
   send("Q",at,"owed",2.);
   if(!reply.empty())send(at,"Q",reply,2.);
  }
  auto& q=w.state("Q");auto& p=w.state("P");
  std::cout<<"O "<<independent<<" "<<arrived<<" "<<hex(returned)<<" "
   <<q.bytes_sent_this_epoch<<" "<<p.bytes_sent_this_epoch<<" "
   <<(dock<0?0:w.state(at).bytes_received_this_epoch)<<" "<<traffic<<std::endl;
 }
}
