#define main inherited_radio_main
#include "replay.cpp"
#undef main

struct Fixture{
 World w;
 bool missing=true;
 std::map<std::string,int> received;
 Fixture(unsigned cap, unsigned oldSize, unsigned fastSize, bool sharedTx):w(cap){
  for (std::string n:{"R0","R1","Unrelated","Depot"}){
   auto a=std::make_shared<TeamNode>();
   a->name=n;
   a->radio=w.b.team->at("P")->radio;
   w.b.team->emplace(n,a);
  }
  bind("Old","R0");
  bind("Early","R1");
  bind("Other","Depot");
  w.b.pose_update_f=[this](const std::string& s){
    return std::make_tuple(s!="R0" || !missing,Pose{},now);
  };
  w.b.incomingMsgs.push_back({"P","Old",std::string(oldSize,'A')});
  w.b.incomingMsgs.push_back({sharedTx?"P":"Q","Early",std::string(fastSize,'B')});
  w.b.incomingMsgs.push_back({"Unrelated","Other","C"});
 }
 void bind(std::string topic,std::string receiver){
   w.b.endpoints[topic+":7"]={{receiver}};
   if(!received.count(topic)) received[topic]=0;
   w.app.callbacks[topic+":7"]=[this,topic](auto,auto,auto,const auto&){++received[topic];};
 }
 void subset(char name){
  Broker local;
  local.communication_function=w.b.communication_function;
  local.node=w.b.node;
  local.pose_update_f=w.b.pose_update_f;
  for(auto a=w.b.incomingMsgs.begin();a!=w.b.incomingMsgs.end();++a){
   if(a->data()[0]!=name)continue;
   auto key=a->dst_address()+":7";
   local.endpoints[key]=w.b.endpoints.at(key);
   auto sender=a->src_address();
   local.team->emplace(sender,w.b.team->at(sender));
   for(const auto& p:local.endpoints.at(key))local.team->emplace(p.address,w.b.team->at(p.address));
   for(const auto& [p,_]:*local.team)assert(std::get<0>(local.pose_update_f(p)));
   local.incomingMsgs.push_back(*a);
   w.b.incomingMsgs.erase(a);
   local.DispatchMessages();
   assert(local.incomingMsgs.empty());
   return;
  }
  assert(false);
 }
 std::string dest(char letter){
  for(const auto& j:w.b.incomingMsgs)
    if(j.data()[0]==letter)
      return w.b.endpoints.at(j.dst_address()+":7").at(0).address;
  assert(false); return {};
 }
};

int main(){
 unsigned cap,a,b,shared,mask,world,kind;
 while(std::cin>>cap>>a>>b>>shared>>mask>>world>>kind){
  now=0;
  Fixture f(cap,a,b,shared);
  assert(mask&(1u<<world));
  assert(f.dest('A')!=""+f.dest('B'));
  const double clocks[]={.75,.75,1.,1.25};
  bool early=false;
  if(kind==0){
   f.w.b.DispatchMessages();
   assert(f.w.b.incomingMsgs.size()==3);
  }else{
   bool bad=false;
   if(kind==1){
    // Optimizes over all declared clocks, but only today's receiver names.
    for(unsigned j=0;j<4;++j)if(mask&(1u<<j))
      bad|=shared && clocks[j]<=1. && a+b>cap;
   }else if(kind==2){
    // Safe factorized partition: union of possible aliases and times.
    const bool may_share=shared || (mask&14);
    const bool may_overlap=mask&7;
    bad=may_share && may_overlap && a+b>cap;
   }else{
    for(unsigned j=0;j<4;++j)if(mask&(1u<<j))
      bad|=(shared||j!=0) && clocks[j]<=1. && a+b>cap;
   }
   early=!bad;
   if(early)f.subset('B');
   f.subset('C');
  }
  assert(f.received["Early"]==early);
  int earlyOther=f.received["Other"];
  // Commit actual destination registration at its authored authority cut.
  now=clocks[world];
  f.missing=false;
  if(world)f.bind("Old","R1");
  f.subset('A');
  if(kind==0)f.subset('C');
  if(!early){
    now=clocks[world]+1.25; // valid late delivery within 2.5 seconds
    f.subset('B');
  }
  assert(f.w.b.incomingMsgs.empty());
  std::cout<<early<<' '<<earlyOther<<' '<<f.received["Old"]<<' '
    <<f.received["Early"]<<' '<<f.received["Other"]<<'\n';
 }
}
