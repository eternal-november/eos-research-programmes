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
 int cap,side,mask,hint,sample;
 std::string wire;
 while(std::cin>>cap>>side>>mask>>hint>>sample>>wire){
  World w(cap);
  const std::array<std::string,2> names={"D0","D1"};
  for(auto name:{"D0","D1","S","I","T"}){
   auto node=std::make_shared<TeamNode>();
   node->name=name;node->radio.capacity=8*cap;
   node->radio.pathloss_f=[](double,auto&,auto&,bool& b){b=false;return Power{100,0};};
   w.b.team->emplace(name,node);w.b.endpoints[std::string(name)+":7"]={{name}};
  }
  w.b.team->at("P")->radio.capacity=8*32;
  w.b.team->at("Q")->radio.capacity=8*cap;
  bool donorPath=true;
  w.b.team->at("P")->radio.pathloss_f=[&](double,auto&,auto&,bool& b){
    b=false;return Power{donorPath?100:-std::numeric_limits<double>::infinity(),0};};
  int busy=-1,qHint=-1,independent=0,lateReceipt=0,requests=0,pending=-1;
  std::array<std::string,2> records;
  std::array<int,2> probes={-1,-1};
  std::string returned,reply;
  for(int k:{0,1})w.app.callbacks[names[k]+":7"]=[&,k](auto from,auto,auto,auto data){
    if(from=="I"){assert(data=="SIDE");busy=k;++independent;return;}
    if(from=="P"){
      if(now==0.)records[k]=data;else ++lateReceipt;
      return;
    }
    if(from=="S"){assert(data=="0"||data=="1");probes[k]=data[0]-'0';return;}
    assert(from=="Q"&&data=="owed");
    ++requests;
    std::cout<<"L "<<probes[k]<<" "<<hex(records[k])<<std::endl;
    std::string response;assert(std::cin>>response);reply=raw(response);
  };
  w.app.callbacks["Q:7"]=[&](auto from,auto,auto,auto data){
    if(data.size()==1){qHint=data[0]-'0';assert(from==names.at(qHint));return;}
    assert(pending>=0&&from==names.at(pending)&&data==reply);
    returned=data;
  };
  w.app.callbacks["T:7"]=[&](auto from,auto,auto,auto data){
    assert(data.size()==1);
    qHint=data[0]-'0';assert(from==names.at(qHint));
  };
  auto send=[&](std::string from,std::string to,std::string data,double stamp){
   now=stamp;
   unsigned long live=0;
   for(auto [t,n]:w.state(from).bytes_sent)if(t>=stamp-1.)live+=n;
   w.b.incomingMsgs.push_back({from,to,data});
   w.b.DispatchMessages();
   assert(w.b.incomingMsgs.empty());
   if(w.state(from).bytes_sent_this_epoch!=live+data.size()){
     std::cerr<<from<<" -> "<<to<<" @ "<<stamp<<" cap "<<cap<<" payload "<<data.size()<<" prior "<<live<<" got "<<w.state(from).bytes_sent_this_epoch<<std::endl;
     assert(false);
   }
  };
  for(int k:{0,1})if(mask&(1<<k))send("P",names[k],raw(wire),0.);
  assert(!records[0].empty()==bool(mask&1));
  assert(!records[1].empty()==bool(mask&2));
  send("I",names[side],"SIDE",1.0625);
  assert(busy==side&&independent==1);
  if(hint)send(names[busy],hint==1?"Q":"T",std::string(1,char('0'+busy)),1.125);
  std::cout<<"C "<<qHint<<std::endl;
  assert(std::cin>>pending);
  assert(pending>=-1&&pending<=1);
  donorPath=false;
  if(pending>=0){
    auto d=names[pending];
    send("P",d,raw(wire),1.9375); // known-outage probe arm reserves the same failed traffic
    assert(lateReceipt==0);
    if(sample>=0)send("S",d,sample?"1":"0",2.);
    send("Q",d,"owed",2.);
    if(!reply.empty()) send(d,"Q",reply,2.);
  }
  std::cout<<"O "<<independent<<" "<<requests<<" "<<hex(returned)<<" "
    <<w.state("Q").bytes_received_this_epoch<<" "<<lateReceipt<<" "<<qHint<<std::endl;
 }
}
