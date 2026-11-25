#define main upstream_replay_main
#include "subt/replay.cpp"
#undef main

unsigned live(const rf_interface::radio_state &r, double t) {
 unsigned ans=0;
 for(const auto& [s,z]:r.bytes_sent) if(s<=t && t-s<=1) ans+=z;
 return ans;
}
int main(){
 World w(5);
 unsigned rescue=0,independent=0,old_receipts=0;
 std::string copy,old_payload="ooo";
 w.app.callbacks["Base:7"]=[&](auto,auto,auto,const auto& v){
  if(v=="rrr") ++rescue;
  else if(v=="ooo"){++old_receipts;old_payload.clear();}
  else assert(false);
 };
 w.app.callbacks["Q:7"]=[&](auto,auto,auto,const auto& v){copy=v;};
 w.app.callbacks["OtherSink:7"]=[&](auto,auto,auto,const auto& v){
  assert(v=="uuu");++independent;
 };
 for(auto n:{"Other","OtherSink"}){
  auto t=std::make_shared<TeamNode>(*w.b.team->at("P"));
  t->name=n; w.b.team->emplace(n,t);
 }
 w.b.endpoints["OtherSink:7"].push_back({"OtherSink"});
 auto emit=[&](std::string src,std::string dst,std::string payload,double at,bool open){
  now=at;w.path_available=open;
  w.b.incomingMsgs.push_back({src,dst,payload});
  w.b.DispatchMessages();
  assert(w.b.incomingMsgs.empty());
 };
 emit("P","Q","rrr",-2,true);
 assert(copy=="rrr");
 auto sender=[](char c){assert(c=='L'||c=='R');return c=='L'?"P":"Q";};

 char action,side;
 double at;
 while(std::cin>>action>>side>>at) {
  if(action=='O'){
   emit(sender(side),"Base",old_payload,at,false);
   assert(old_receipts==0);
  }
  else if(action=='C'){
   if(side!='-'){
    assert(side=='L'||copy=="rrr");
    emit(sender(side),"Base","rrr",at,true);
   }
   emit("Other","OtherSink","uuu",at,true);
  }else assert(action=='P');
  std::cout<<(live(w.state("P"),at)+3>5)<<(live(w.state("Q"),at)+3>5)<<" "
           <<rescue<<" "<<independent<<" "<<old_receipts<<" "<<!old_payload.empty()<<std::endl;
 }
}
