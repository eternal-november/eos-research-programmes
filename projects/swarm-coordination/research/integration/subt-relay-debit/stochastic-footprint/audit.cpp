#define main prior_radio_main
#include <replay.cpp>
#undef main

namespace {
double power_for_drop(double target){
 double x=0,y=10;
 for(int k=0;k<100;++k){
   double m=(x+y)/2;
   if(std::erfc(m)>target)x=m;else y=m;
 }
 return -100+10*std::log10((x+y)*(x+y)/4);
}
struct Fixture{
 World w;
 std::map<std::string,int> got{{"old",0},{"side",0}};
 int n=1;
 Fixture():w(16){
   for(std::string k:{"Last"}){
     auto node=std::make_shared<TeamNode>();
     node->name=k;node->radio=w.b.team->at("P")->radio;
     w.b.team->emplace(k,node);
   }
   w.b.endpoints["Base:7"]={{"Base"}};
   w.b.endpoints["Last:7"]={{"Last"}};
   w.app.callbacks["Base:7"]=[&](auto,auto,auto,auto){++got["old"];};
   w.app.callbacks["Last:7"]=[&](auto,auto,auto,auto){++got["side"];};
   for(auto [i,node]:*w.b.team){
     const double p=power_for_drop(i=="P"?.5005:.1005);
     node->radio.pathloss_f=[p](double,auto&,auto&,bool& c){c=false;return Power{p,0.};};
   }
 }
 void queue(bool old){
   w.b.incomingMsgs.push_back({old?"P":"Q",old?"Base":"Last",std::string(n,'d')});
 }
 auto outcome(){return std::make_pair(got["old"],got["side"]);}
};
// Generated harness exposes only the rand seam. Its original source
// traversal, statically selected power law, charges and callbacks remain.
auto run(int oldmark,int sidemark,bool swapped,bool keyed){
 Fixture f;now=0;
 reset_draws({oldmark,sidemark});
 if(keyed){
   // Caller binds an externally selected tape item to this physical
   // attempt here (no payload-level reuse, no production RNG).
   for(bool old:{!swapped,swapped}){
     reset_draws({old?oldmark:sidemark});
     f.queue(old);f.w.b.DispatchMessages();
     assert(draws_consumed==1);
   }
 }else{
   f.queue(!swapped);f.queue(swapped);f.w.b.DispatchMessages();
   assert(draws_consumed==2);
 }
 assert(f.w.state("P").bytes_sent_this_epoch==1);
 assert(f.w.state("Q").bytes_sent_this_epoch==1);
 return f.outcome();
}
void rejection(){
 for(bool pre_rx:{false,true}){
   Fixture f;
   now=0;
   if(pre_rx){
     auto& s=f.w.state("Last");
     s.bytes_received.emplace_back(0,16);s.bytes_received_this_epoch=16;
   }else{
     auto& s=f.w.state("Q");
     s.bytes_sent.emplace_back(0,16);s.bytes_sent_this_epoch=16;
   }
   // First .25 mark is sufficient for side RF; only the reject cut
   // changes whether the old report receives .25 or .75.
   reset_draws({250,750});
   f.queue(false);f.queue(true);
   f.w.b.DispatchMessages();
   assert(f.got["side"]==0);
   assert(draws_consumed==(pre_rx?2:1));
   assert(f.got["old"]==pre_rx);
   assert(f.w.state("Q").bytes_sent_this_epoch==(pre_rx?1:16));
   std::cout<<"reject "<<(pre_rx?"rx":"tx")<<' '<<draws_consumed<<' '<<f.got["old"]<<'\n';
 }
}
void recipient_and_retry(){
 for(bool reverse:{false,true}){
   Fixture f;now=0;
   f.w.b.endpoints["Base:7"]= reverse ?
        std::vector<BrokerClientInfo>{{"Last"},{"Base"}} :
        std::vector<BrokerClientInfo>{{"Base"},{"Last"}};
   reset_draws({250,750});f.queue(true);f.w.b.DispatchMessages();
   assert(draws_consumed==2 && f.w.state("P").bytes_sent_this_epoch==2);
   assert(f.w.state("Base").bytes_received_this_epoch==unsigned(reverse));
   assert(f.w.state("Last").bytes_received_this_epoch==unsigned(!reverse));
 }
 // Same application bytes and route; second attempt must not replay
 // the first physical mark. The payload identity stays constant.
 Fixture f;now=0;reset_draws({250,750});
 f.queue(true);f.w.b.DispatchMessages();assert(f.got["old"]==0);
 f.queue(true);f.w.b.DispatchMessages();assert(f.got["old"]==1);
 assert(draws_consumed==2 && f.w.state("P").bytes_sent_this_epoch==2);
 std::cout<<"recipient order and retry marks checked\n";
}
int full_grid(){
 // The native formula is checked for all one thousand individual
 // possible marks at both thresholds. Enumerate the paired products
 // exactly using those tables; do not infer libc statistical law.
 bool A[1000],B[1000];
 for(int t=0;t<1000;++t){
   Fixture f;now=0;reset_draws({t,t});f.queue(true);f.queue(false);
   f.w.b.DispatchMessages();
   A[t]=f.got["old"];B[t]=f.got["side"];
   assert(A[t]==(t>500) && B[t]==(t>100));
 }
 int bothside=0,flip=0,oldfirst=0,oldsecond=0,forward=0,reverse=0;
 for(int i=0;i<1000;++i)for(int j=0;j<1000;++j){
   oldfirst+=A[i];oldsecond+=A[j];
   if(!B[i]||!B[j])continue;
   ++bothside;
   if(A[i]!=A[j])++flip;
   forward+=!A[i]&&A[j];reverse+=A[i]&&!A[j];
 }
 assert(bothside==808201 && flip==399200 && oldfirst==499000 && oldsecond==499000);
 assert(forward==reverse);
 std::cout<<"grid "<<bothside<<' '<<flip<<' '<<forward<<' '<<reverse<<' '<<oldfirst<<' '<<oldsecond<<'\n';
 return 0;
}
}
int main(){
 for(int a:{99,100,101,249,250,500,501,750,999})
 for(int b:{99,100,101,249,250,500,501,750,999}){
   assert(run(a,b,false,false)==std::make_pair(int(a>500),int(b>100)));
   assert(run(a,b,true,false)==std::make_pair(int(b>500),int(a>100)));
   assert(run(a,b,true,true)==run(a,b,false,true));
 }
 assert(run(250,750,false,false)==std::make_pair(0,1));
 assert(run(250,750,true,false)==std::make_pair(1,1));
 assert(run(750,250,false,false)==std::make_pair(1,1));
 assert(run(750,250,true,false)==std::make_pair(0,1));
 std::cout<<"paired order checks 81\n";
 rejection();
 recipient_and_retry();
 return full_grid();
}
