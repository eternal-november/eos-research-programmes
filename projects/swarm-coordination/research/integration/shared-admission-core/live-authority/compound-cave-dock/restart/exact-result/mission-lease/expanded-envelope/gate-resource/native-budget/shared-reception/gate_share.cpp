#include <array>
#include <fstream>
#include "gate_receipt.hpp"
#define main earlier_replay
#include "staged_roles.inc"
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
 int cap,mode,entitled,issuedEpoch,liveEpoch;
 double issued,clear;
 double slot;
 Point q,desk,base;
 while(std::cin>>cap>>mode>>entitled>>issuedEpoch>>liveEpoch>>issued>>clear>>slot>>q.x>>q.y>>q.z
              >>desk.x>>desk.y>>desk.z>>base.x>>base.y>>base.z){
  World w(cap);
  CommsClient control;
  w.b.node.roles["Base"]=&w.app;
  w.b.node.roles["Desk"]=&control;
  int report=0, deskSeen=0, gate=0, localCopies=0;
  // This producer decision is at the modeled authoritative source.
  // Receivers see no ground truth coordinates or clear timestamp.
  assert(issued<=slot);
  int scope=qualification(issued>clear,issuedEpoch);
  std::string endpoint=scope>=0?"Qualified"+std::to_string(scope):"Raw";
  std::vector<int> queue;
  for(const auto& channel:{std::string("Raw"),std::string("Qualified6"),std::string("Qualified7")}){
    int epoch=channel=="Qualified6"?6:channel=="Qualified7"?7:-1;
    auto accept=[&,channel](const std::string& from,const std::string& to,const std::string& data){
      assert(from=="Q"&&to==channel&&data=="iiii"&&now==slot);
    };
    auto key=channel+":7";
    w.app.callbacks[key]=[&,epoch,accept](auto from,auto to,auto,auto data){
      accept(from,to,data);++report;
      // Enqueue under native client mutex; consume with the local service below.
      if(mode==2&&entitled){++localCopies;queue.push_back(epoch);}
    };
    control.callbacks[key]=[&,epoch,accept](auto from,auto to,auto,auto data){
      accept(from,to,data);++deskSeen;
      if(may_use(epoch,liveEpoch,true,true))++gate;
    };
    if(mode==1)w.b.endpoints[key]={{"Desk"},{"Base"}};
    else if(mode==0)w.b.endpoints[key]={{"Base"},{"Desk"}};
    else w.b.endpoints[key]={{"Base"}};
  }
  auto D=std::make_shared<TeamNode>();D->name="Desk";
  w.b.team->emplace("Desk",D);
  auto& c=w.b.team->at("Q")->radio;
  c.default_tx_power=80;
  c.pathloss_f=[&](double power,auto& a,auto& b,bool& used){return m.ComputeReceivedPower(power,a,b,used);};
  w.b.pose_update_f=[&](auto who){
   return std::make_tuple(true,Pose{who=="Desk"?desk:who=="Base"?base:q},now);
  };
  now=slot;
  w.b.incomingMsgs.push_back({"Q",endpoint,"iiii"});w.b.DispatchMessages();
  assert(w.b.incomingMsgs.empty());
  for(int epoch:queue)if(may_use(epoch,liveEpoch,true,true))++gate;
  std::cout<<report<<" "<<deskSeen<<" "<<gate<<" "<<localCopies
           <<" "<<w.state("Q").bytes_sent_this_epoch
           <<" "<<w.state("Base").bytes_received_this_epoch
           <<" "<<w.state("Desk").bytes_received_this_epoch<<"\n";
 }
}
