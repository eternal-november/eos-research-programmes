// Offline fixture only. Build after restoring six #449 blobs, extraction, and shim.
#define main original_subt_fixture_main
#include "upstream_replay.cpp"
#undef main

unsigned nativeSchedule(const std::vector<int>& ticks, unsigned colors) {
 World w(5);
 w.recover();
 std::map<std::string,std::set<std::string>> copies;
 std::vector<bool> got(ticks.size(),false);
 auto emit=[&](std::string s,std::string d,std::string data,double stamp){
  now=stamp;
  w.b.incomingMsgs.push_back({std::move(s),std::move(d),std::move(data)});
  w.b.DispatchMessages();
  assert(w.b.incomingMsgs.empty());
 };
 for(std::string sender:{"P","Q"}){
  w.b.endpoints[sender+":7"]={{sender}};
  w.app.callbacks[sender+":7"]=[&,sender](auto src,auto,auto,auto v){
   assert(src=="Base" && v.size()==3); copies[sender].insert(v);
  };
 }
 double setup=-4.0*ticks.size()-2.0;
 for(size_t i=0;i<ticks.size();++i){
  const auto pkt=std::string(3,char('a'+i));
  for(std::string sender:{"P","Q"}){
   emit("Base",sender,pkt,setup);
   assert(copies[sender].count(pkt)); setup+=2;
  }
  auto dst="D"+std::to_string(i);
  auto node=std::make_shared<TeamNode>(*w.b.team->at("Base"));
  node->rf_state=rf_interface::radio_state{}; node->name=dst;
  w.b.team->emplace(dst,node); w.b.endpoints[dst+":7"].push_back({dst});
  w.app.callbacks[dst+":7"]=[&,i,pkt](auto,auto,auto,auto v){got[i]=v==pkt;};
 }
 unsigned count=0;
 for(size_t i=0;i<ticks.size();++i){
  const std::string sender=(colors>>i&1)?"Q":"P";
  const auto pkt=std::string(3,char('a'+i)); assert(copies[sender].count(pkt));
  emit(sender,"D"+std::to_string(i),pkt,ticks[i]*0.25);
  count+=got[i];
 }
 return count;
}

bool directAll(const std::vector<int>& t,unsigned colors) {
 for(size_t i=0;i<t.size();i++)
  for(size_t j=0;j<i;j++)
   if(t[i]-t[j]<=4 && ((colors>>i&1)==(colors>>j&1)))return false;
 return true;
}
bool every(const std::vector<int>& t,const std::vector<unsigned>& masks) {
 for(unsigned x=0;x<(1u<<t.size());x++){
  bool valid=true;
  for(size_t i=0;i<t.size();i++)if(!(masks[i]&(1u<<(x>>i&1))))valid=false;
  if(valid && nativeSchedule(t,x)==t.size())return true;
 }
 return false;
}
int main(){
 assert(!every({0,3,6},{1,3,2})); assert(!every({0,4,6},{1,3,2}));
 assert(every({0,5,6},{1,3,2})); assert(every({0,6,6},{1,3,2}));
 assert(every({0,3,6},{1,3,1})); 
 unsigned cases=0;
 for(size_t n=1;n<=5;n++)
  for(unsigned gaps=0;gaps<(1u<<(2*(n-1)));gaps++){
   const int width[]{0,2,3,5};
   std::vector<int> t{0};
   for(size_t i=1;i<n;i++)t.push_back(t.back()+width[gaps>>(2*(i-1))&3]);
   for(unsigned x=0;x<(1u<<n);x++){
     assert((nativeSchedule(t,x)==n)==directAll(t,x)); ++cases;
   }
  }
 std::cout<<"matched native fixed-time assignments: "<<cases<<"\n";
 std::cout<<"middle at 0.75 or 1.00 fails; 1.25 or 1.50 succeeds with legal slots\n";
}
