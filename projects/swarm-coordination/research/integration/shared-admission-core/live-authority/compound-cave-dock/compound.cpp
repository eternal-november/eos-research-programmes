#include <array>
#include <fstream>
#define main earlier_replay
#include "staged_replay.inc"
#undef main
#include "load.inc"

int main(){
 const std::array<uint64_t,6> ids{18,39,16,13,42,6};
 const std::array<Point,6> fixed{Point{100,-25,6},Point{50,25,6},Point{100,100,6},
  Point{100,50,8},Point{100,75,8},Point{75,100,6}};
 std::ifstream tbl("dist6.tsv");
 double d[6][6];for(auto& row:d)for(auto& v:row)assert(tbl>>v);
 CommsBrokerPlugin tracker;auto& m=*tracker.visibilityModel;auto& lib=m.visibilityTable;
 m.defaultRangeConfig.max_range=72.;m.defaultRangeConfig.scaling_factor=.55;
 for(unsigned i=0;i<ids.size();++i){
   lib.visibilityGraph.vertices.emplace(ids[i],0);
   for(unsigned j=0;j<ids.size();++j)lib.visibilityGraph.projected[ids[i]][ids[j]]={d[i][j],0};
 }
 lib.lutPath="cave.dat";assert(lib.LoadLUT());
 int shift,duplicate,omit,policy,oldBytes,sideBytes,cap;
 while(std::cin>>shift>>duplicate>>omit>>policy>>oldBytes>>sideBytes>>cap){
  World w(32);
  for(const auto& name:{"R","S","D"}){
   auto p=std::make_shared<TeamNode>();p->name=name;p->radio.capacity=8*32;
   (*w.b.team)[name]=p;w.b.endpoints[std::string(name)+":7"].push_back({name});
  }
  for(const auto& name:{"P","Q","Base","R","S","D"}){
   auto& cfg=w.b.team->at(name)->radio;cfg.default_tx_power=80;
   cfg.pathloss_f=[&](double watts,auto& a,auto& b,bool& used){
      return m.ComputeReceivedPower(watts,a,b,used);
   };
  }
  w.b.team->at("Q")->radio.capacity=8*cap;
  // P and Q exchange the preauthorized archival copy during staging (-200).
  // Thereafter Q is deployed at fixed site 16. No transit time is estimated.
  // R's former terminal is at Base, but at time zero its available site is 13.
  // If the second branch occurs, R moves 1/64 m along the staged axis between
  // .125 and .375, then stays there. The selected RF link still works.
  auto rpose=[&](double t){
    if(t<0)return fixed[1];
    Point value=fixed[3];
    const double start=shift==2 ? .625 : .125;
    if(shift && t>start) {
      double z=std::min(t-start,.25);
      value.y+=z<=.125 ? z*z/2 : 1./64.-(.25-z)*(.25-z)/2;
    }
    return value;
  };
  auto localR=[&](double t){return rpose(t).y<=50.+1./128.;};
  auto selected=[&](double t){return localR(t)?std::string("R"):std::string("S");};
  w.b.pose_update_f=[&](auto who){
    auto p=who=="P"?fixed[0]:who=="Q"?(now<0?Point{101,-25,6}:fixed[2]):
           who=="R"?rpose(now):who=="S"?fixed[4]:who=="D"?fixed[5]:fixed[1];
    return std::make_tuple(true,Pose{p},now);
  };
  std::string old(oldBytes,'a'), side(sideBytes,'d'), archived;
  int paid=0,sidePaid=0,invalid=0,copySeen=0,polls=0,providerTransfer=0,primaryContact=0;
  std::vector<std::pair<char,std::string>> receipts;
  w.app.callbacks["Q:7"]=[&](auto who,auto,auto,auto v){
   if(who=="P"){assert(v==old);archived=v;++copySeen;}
   else{assert(v.size()==1&&(v[0]=='e'||v[0]=='g')&&(who=="R"||who=="S"));
        receipts.emplace_back(v[0],who);}
  };
  auto finish=[&](auto who,auto dst,auto,auto v){
    if(v=="c"){assert(who=="P"&&dst=="R"&&now<0);++primaryContact;return;}
    if(v=="?"){assert(who=="Q");++polls;return;}
    if(v=="h"){assert(who=="R"&&dst=="S"&&!localR(now));++providerTransfer;return;}
    assert(v==old);
    // Endpoints can deliver a packet even when their application is not
    // authorized to settle the outstanding named duty at consumption.
    const bool allowed=dst=="R"?localR(now):(providerTransfer==1 && now>=.375);
    if(who=="Q" && allowed) ++paid;
    else ++invalid;
  };
  w.app.callbacks["R:7"]=finish;
  w.app.callbacks["S:7"]=finish;
  w.app.callbacks["D:7"]=[&](auto who,auto,auto,auto v){
   assert(who=="Q"&&v==side);++sidePaid;
  };
  auto send=[&](auto src,auto dst,auto v,double when){
   now=when;w.b.incomingMsgs.push_back({src,dst,v});w.b.DispatchMessages();
   assert(w.b.incomingMsgs.empty());
  };
  send("P","Q",old,-200);assert(copySeen==1&&archived==old);
  send("P","R","c",-100);assert(primaryContact==1);
  send("P","R",old,0);assert(paid==0&&invalid==0);
  assert(w.state("P").bytes_sent_this_epoch==size_t(oldBytes));
  assert(selected(.125)=="R");
  send("R","Q","e",.125); // truthful historical preparation, not current lease
  send("Q","D",side,.25);
  assert(selected(.375)==(shift==1?"S":"R"));
  // Native R-to-S transfer: R alone reads its declared local dock rule.
  // S may issue a fresh grant only after consuming the matching transfer.
  if(!localR(.375)&&omit!=2)send("R","S","h",.375);
  assert(providerTransfer==(shift==1 && omit!=2));
  if(policy==2){send("Q","R","?",.5);assert(polls==(size_t(sideBytes)+1<=size_t(cap)));}
  if(omit!=1){
    if(localR(.625))send("R","Q","g",.625);
    if(providerTransfer==1)send("S","Q","g",.625);
  }
  if(duplicate)send("R","Q","e",.75);
  std::string to;
  if(policy==1){if(!receipts.empty())to=receipts.back().second;}
  else for(const auto& r:receipts)if(r.first=='g'){
    assert(to.empty());to=r.second;
  }
  if(!to.empty())send("Q",to,archived,.875);
  const auto latest=receipts.empty()?'-':receipts.back().first;
  char fresh='-';
  for(const auto& r:receipts)if(r.first=='g'){assert(fresh=='-');fresh=r.second[0];}
  std::cout<<shift<<" "<<duplicate<<" "<<omit<<" "<<policy<<" "<<oldBytes<<" "<<sideBytes
      <<" "<<cap<<" "<<paid<<" "<<sidePaid<<" "<<invalid<<" "<<latest<<" "
      <<w.state("Q").bytes_sent_this_epoch<<" "<<receipts.size()<<" "<<providerTransfer<<" "<<fresh<<" "<<(to.empty()?'-':to[0])<<"\n";
 }
}
