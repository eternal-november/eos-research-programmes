#include <array>
#include <fstream>
#define main earlier_replay
#include "staged_replay.inc"
#undef main
#include "load.inc"

int main(){
 std::ifstream tbl("all-dist.tsv");
 unsigned n;
 assert(tbl>>n);
 std::vector<uint64_t> ids(n);
 for(auto& v:ids)assert(tbl>>v);
 CommsBrokerPlugin tracker;
 auto& m=*tracker.visibilityModel;auto& table=m.visibilityTable;
 m.defaultRangeConfig.max_range=72.;m.defaultRangeConfig.scaling_factor=.55;
 for(auto a:ids){
   table.visibilityGraph.vertices.emplace(a,0);
   for(auto b:ids){
     unsigned d;assert(tbl>>d);
     table.visibilityGraph.projected[a][b]={d,0};
   }
 }
 table.lutPath="cave.dat";assert(table.LoadLUT());
 int cap,mode;
 double slot;
 Point early,edge,late,desk,base;
 while(std::cin>>cap>>mode>>slot>>early.x>>early.y>>early.z>>edge.x>>edge.y>>edge.z
              >>late.x>>late.y>>late.z>>desk.x>>desk.y>>desk.z>>base.x>>base.y>>base.z){
  World w(cap);
  int seenSide=0,seenRelease=0;
  double tReport=-1,tRelease=-1;
  // This late-world wrapper starts after all pre-reply ledger entries
  // expired. The new endpoint is a fixed local gate control desk.
  w.app.callbacks["Base:7"]=[&](auto from,auto,auto,auto data){
    assert(from=="Q"&&data=="iiii");tReport=now;++seenSide;};
  w.app.callbacks["Desk:7"]=[&](auto from,auto,auto,auto data){
    assert(from=="Q"&&data=="r");tRelease=now;++seenRelease;};
  auto D=std::make_shared<TeamNode>();D->name="Desk";
  w.b.team->emplace("Desk",D);
  w.b.endpoints["Desk:7"].push_back({"Desk"});
  auto& c=w.b.team->at("Q")->radio;
  c.default_tx_power=80;
  c.pathloss_f=[&](double power,auto& a,auto& b,bool& used){return m.ComputeReceivedPower(power,a,b,used);};
  w.b.pose_update_f=[&](auto who){
   Point p=(who=="Desk"?desk:who=="Base"?base:
            (now==slot?early:now==slot+1?edge:late));
   return std::make_tuple(true,Pose{p},now);
  };
  auto emit=[&](const std::string &target,const std::string &data,double t){
    now=t;w.b.incomingMsgs.push_back({"Q",target,data});w.b.DispatchMessages();
    assert(w.b.incomingMsgs.empty());
  };
  if(mode==0)emit("Base","iiii",slot);  // certificate, no remote completion needed
  else{
    if(mode==1)emit("Base","iiii",slot);
    else emit("Desk","r",slot);
    auto peer=mode==1?"Desk":"Base";
    auto data=mode==1?"r":"iiii";
    emit(peer,data,slot);  // both same slot; permissions differ from charge
    if(cap==4){
      const auto sent=w.state("Q").bytes_sent_this_epoch;
      assert(sent==size_t(mode==1?4:1));
      emit(peer,data,slot+1); // native inclusive expiry: still blocked
      assert(w.state("Q").bytes_sent_this_epoch==sent);
      emit(peer,data,slot+17./16.);
    }
  }
  assert(seenSide<=1&&seenRelease<=1);
  std::cout<<cap<<" "<<mode<<" "<<slot<<" "<<tReport<<" "<<tRelease
           <<" "<<w.state("Q").bytes_sent_this_epoch<<"\n";
 }
}
