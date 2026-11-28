// Compiled against the pinned selected native #726 extraction.
#include <array>
#include <fstream>
#define main earlier_replay
#include "staged_replay.inc"
#undef main


int main(){
 const std::array<uint64_t,5> ids{18,39,16,13,42};
 const std::array<Point,5> p{Point{100,-25,0},Point{50,25,0},Point{100,100,0},Point{100,50,0},Point{100,75,0}};
 std::ifstream is("distances.tsv");
 double d[5][5];for(auto& row:d)for(auto& w:row)assert(is>>w);
 int sid,site,sender,receiver,prior,event,bad;
 while(std::cin>>sid>>site>>sender>>receiver>>prior>>event>>bad){
   World w(256);
   auto& tr=w.tracker;auto& m=*tr.visibilityModel;auto& t=m.visibilityTable;
   m.defaultRangeConfig.max_range=72.;m.defaultRangeConfig.scaling_factor=.55;
   for(unsigned i=0;i<ids.size();++i){
     t.vertices.emplace(std::make_tuple((int32_t)p[i].x,(int32_t)p[i].y,(int32_t)p[i].z),ids[i]);
     t.visibilityGraph.vertices.emplace(ids[i],0);
     for(unsigned j=0;j<ids.size();++j)t.visibilityGraph.projected[ids[i]][ids[j]]={d[i][j],0};
   }
   t.PopulateVisibilityInfo();
   auto install=std::make_shared<TeamNode>(*w.b.team->at("P"));
   install->name="I";(*w.b.team)["I"]=install;
   auto monitor=std::make_shared<TeamNode>(*w.b.team->at("P"));
   monitor->name="X";(*w.b.team)["X"]=monitor;
   w.b.team->at("Q")->radio.capacity=8*receiver;
   w.b.team->at("I")->radio.capacity=8*sender;
   for(const auto& id:{"P","Q","I","X"}){
     auto& cfg=w.b.team->at(id)->radio;cfg.default_tx_power=80;
     cfg.pathloss_f=[&](double watts,auto& a,auto& b,bool& used){return m.ComputeReceivedPower(watts,a,b,used);};
   }
   bool blockedRoster=false;
   w.b.pose_update_f=[&](auto id){
     const auto index=id=="Base"?1:id=="P"?0:id=="Q"?2:id=="I"?site:4;
     return std::make_tuple(id!="X"||!blockedRoster,Pose{p[index]},now);
   };
   bool old=false;int monitorCount=0,signal=-1;
   w.app.callbacks["Base:7"]=[&](auto s,auto,auto,auto v){assert(s=="P"&&v=="aa");old=true;++w.recv;};
   w.app.callbacks["Q:7"]=[&](auto s,auto,auto,auto v){
      if(s=="X"){assert(v=="a");++monitorCount;return;}
      assert(s=="I"&&v==std::string(1,site==3?'0':'1'));signal=int(1024*now);
   };
   assert(w.send("P","Base",2,0.)&&old);
   if(prior>=0){
      now=prior/1024.;w.b.incomingMsgs.push_back({"X","Q","a"});
      w.b.DispatchMessages();assert(monitorCount==1);
   }
   blockedRoster=bool(bad);
   now=event/1024.;w.b.incomingMsgs.push_back({"I","Q",std::string(1,site==3?'0':'1')});
   w.b.DispatchMessages();
   if(blockedRoster){
      assert(signal==-1&&w.b.incomingMsgs.size()==1);
      blockedRoster=false;
      now=(event+64)/1024.;w.b.DispatchMessages();
   }
   assert(w.b.incomingMsgs.empty());
   std::cout<<sid<<' '<<signal<<' '<<int(old)<<' '<<monitorCount<<'\n';
 }
}
