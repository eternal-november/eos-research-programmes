#define main inherited_replay_main
#include "subt/replay.cpp"
#undef main

struct Fixture {
 World w{5};
 bool bad=true;
 std::vector<std::string> seen;
 Fixture(char scenario){
   for(auto n:{"Bad","T","D1","D2","Solo"}){
     auto t=std::make_shared<TeamNode>(*w.b.team->at("P"));
     t->name=n;w.b.team->emplace(n,t);
   }
   auto sink=[&](std::string topic,std::initializer_list<const char*> receivers){
     for(auto r:receivers)
       w.b.endpoints[topic+":7"].push_back({r});
     w.app.callbacks[topic+":7"]=[&,topic](auto,auto,auto,const auto& p){
       seen.push_back(topic+":"+p.substr(0,1));
     };
   };
   sink("X",{"D1"});
   sink("Y",{"D2"});
   sink("B",{"Bad"});
   sink("E",{"Solo"});
   sink("F",{"D1","Bad"});
   w.b.pose_update_f=[this](const std::string& n){
     return std::make_tuple(n!="Bad"||!bad,Pose{},now);
   };
   auto put=[&](const char* s,const char* target,const char* data){
     w.b.incomingMsgs.push_back({s,target,data});
   };
   put("P","X","a");
   if(scenario=='O')put("P","B","b");
   if(scenario=='F')put("P","F","b");
   put("P","Y","cc");
   put("T","Y","dddd");
   put("Q","E","eee");
 }
 std::string endpoint(const subt::msgs::Datagram& m){return m.dst_address()+":7";}
 void describe(){
   // Read the actual pending datagrams, actual endpoint→subscriber map,
   // and the same test pose provider used by the native code.
   for(const auto& m:w.b.incomingMsgs){
     auto s=m.src_address();
     std::cout<<m.data()[0]<<' '<<s;
     for(auto r:w.b.endpoints.at(endpoint(m)))std::cout<<' '<<r.address;
     std::cout<<'\n';
   }
   std::cout<<"!"<<(std::get<0>(w.b.pose_update_f("Bad"))?"":" Bad")<<std::endl;
 }
 void scoped(std::string selected){
   if(selected=="-")return;
   Broker local;
   local.communication_function=w.b.communication_function;
   local.pose_update_f=w.b.pose_update_f;
   local.node=w.b.node;
   for(auto it=w.b.incomingMsgs.begin();it!=w.b.incomingMsgs.end();){
     if(selected.find(it->data()[0])==std::string::npos){++it;continue;}
     const auto& m=*it;
     auto key=endpoint(m),sender=m.src_address();
     local.team->emplace(sender,w.b.team->at(sender));
     local.endpoints[key]=w.b.endpoints.at(key);
     for(const auto& r:local.endpoints.at(key))
       local.team->emplace(r.address,w.b.team->at(r.address));
     local.incomingMsgs.push_back(m);
     it=w.b.incomingMsgs.erase(it);
   }
   for(const auto& [k,v]:*local.team)
     assert(std::get<0>(local.pose_update_f(k)));
   assert(local.incomingMsgs.size()==selected.size());
   // Share the very same native rf_state objects and the same application.
   // No placeholder pose is supplied for a blocked recipient.
   local.DispatchMessages();
   assert(local.incomingMsgs.empty());
 }
 void read(){
   for(auto& s:seen)std::cout<<s<<' ';
   std::cout<<"| ";
   for(auto& m:w.b.incomingMsgs)std::cout<<m.data()[0];
   std::cout<<" | "<<w.state("P").bytes_sent_this_epoch
      <<' '<<w.state("D2").bytes_received_this_epoch<<std::endl;
 }
};
int limits(int receiver_limit){
 World w(5);
 unsigned receive_count=0;
 w.b.team->at("Base")->radio.capacity=8*receiver_limit;
 auto T=std::make_shared<TeamNode>(*w.b.team->at("P"));
 T->name="T";w.b.team->emplace("T",T);
 w.b.team->at("Q")->radio.capacity=48;
 assert(w.send("T","Base",4,0));
 assert(!w.send("P","Base",2,0.25));
 assert(w.state("Base").bytes_received_this_epoch==4);
 assert(w.send("Q","Base",2,0.25));
 assert(w.state("Base").bytes_received_this_epoch==6);
 std::cout<<receiver_limit<<" "<<w.state("Base").bytes_received_this_epoch<<std::endl;
 return receive_count;
}

int main(int argc,char** argv){
 if(argc==2)return limits(std::stoi(argv[1]));
 char scenario;std::cin>>scenario;Fixture f(scenario);
 char phase;double t;
 while(std::cin>>phase>>t){
   now=t;
   if(phase=='M'){f.describe();continue;}
   if(phase=='R')f.bad=false;
   if(phase=='P'){std::string s;std::cin>>s;f.scoped(s);}
   if(phase=='N'||phase=='R')f.w.b.DispatchMessages();
   f.read();
 }
}
