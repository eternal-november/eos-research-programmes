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

 int sid,site,prior;
 std::array<int,3> caps{},sizes{},order{};
 while(std::cin>>sid>>site>>prior>>caps[0]>>caps[1]>>caps[2]>>sizes[0]>>sizes[1]>>sizes[2]>>order[0]>>order[1]>>order[2]){
   World w(256);
   auto& tr=w.tracker;auto& m=*tr.visibilityModel;auto& t=m.visibilityTable;
   m.defaultRangeConfig.max_range=72.;m.defaultRangeConfig.scaling_factor=.55;
   for(unsigned i=0;i<ids.size();++i){
     t.vertices.emplace(std::make_tuple((int32_t)p[i].x,(int32_t)p[i].y,(int32_t)p[i].z),ids[i]);
     t.visibilityGraph.vertices.emplace(ids[i],0);
     for(unsigned j=0;j<ids.size();++j)t.visibilityGraph.projected[ids[i]][ids[j]]={d[i][j],0};
   }
   t.PopulateVisibilityInfo();
   std::array<std::string,3> names{"I","X","Y"};
   auto cf=[&](std::string id,int cap){
     auto n=std::make_shared<TeamNode>(*w.b.team->at("P"));
     n->name=id;n->radio.capacity=8*cap;(*w.b.team)[id]=n;
   };
   for(int i=0;i<3;++i)cf(names[i],caps[i]);
   cf("E",256);
   for(const auto& id:{"P","Q","I","X","Y","E"}){
     auto& cfg=w.b.team->at(id)->radio;cfg.default_tx_power=80;
     cfg.pathloss_f=[&](double watts,auto& a,auto& b,bool& used){return m.ComputeReceivedPower(watts,a,b,used);};
   }
   w.b.pose_update_f=[&](auto id){
      int x=id=="Base"?1:id=="P"?0:id=="Q"?2:id=="I"?site:4;
      return std::make_tuple(true,Pose{p[x]},now);
   };
   bool old=false;int recovered=0,other=0;
   w.app.callbacks["Base:7"]=[&](auto s,auto,auto,auto v){assert(s=="P"&&v=="aa");old=true;++w.recv;};
   w.app.callbacks["Q:7"]=[&](auto s,auto,auto,auto v){
      if(s=="E"){other+=int(v.size());return;}
      for(int i=0;i<3;++i)if(s==names[i]){
         assert(v==std::string(sizes[i],char('a'+i)));recovered|=(1<<i);return;
      }
      assert(false);
   };
   assert(w.send("P","Base",2,0.)&&old);
   if(prior){
     now=0.5;w.b.incomingMsgs.push_back({"E","Q",std::string(prior,'d')});
     w.b.DispatchMessages();assert(other==prior);
   }
   now=1.;
   for(auto i:order)w.b.incomingMsgs.push_back({names[i],"Q",std::string(sizes[i],char('a'+i))});
   w.b.DispatchMessages();
   assert(w.b.incomingMsgs.empty());
   std::cout<<sid<<' '<<recovered<<' '<<int(old)<<' '<<other<<'\n';
 }
}
