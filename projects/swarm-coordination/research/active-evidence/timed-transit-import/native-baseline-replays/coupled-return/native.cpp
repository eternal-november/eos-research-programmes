// Compiled against the pinned selected native #726 extraction.
#include <array>
#include <fstream>
#define main earlier_replay
#include "staged_replay.inc"
#undef main


int main(){
 std::ifstream in("all-sampled.tsv");
 unsigned n,c;assert(in>>n>>c);
 std::vector<unsigned> ids(n),target(c);
 std::map<unsigned,Point> p;
 for(unsigned i=0;i<n;++i){
   unsigned v;double x,y,z;assert(in>>v>>x>>y>>z);ids[i]=v;p[v]=Point{x,y,z};
 }
 for(auto &u:target)assert(in>>u);
 std::vector<std::vector<double>> d(n,std::vector<double>(n));
 for(auto &row:d)for(auto &cell:row)assert(in>>cell);
 for(int l:{-1,13,42}){
   World w(256);
   auto& tr=w.tracker;auto& m=*tr.visibilityModel;auto& t=m.visibilityTable;
   m.defaultRangeConfig.max_range=72.;m.defaultRangeConfig.scaling_factor=.55;
   for(unsigned i=0;i<n;++i){
     auto u=ids[i];auto q=p.at(u);
     t.vertices.emplace(std::make_tuple((int32_t)q.x,(int32_t)q.y,(int32_t)q.z),u);
     t.visibilityGraph.vertices.emplace(u,0);
     for(unsigned j=0;j<n;++j)t.visibilityGraph.projected[u][ids[j]]={d[i][j],0};
   }
   assert(t.vertices.size()==n);
   t.PopulateVisibilityInfo();
   if(l>=0){
       tr.poses["mission__breadcrumb__1__static__"]=Pose{p.at(l)};
       tr.UpdateIfNewBreadcrumbs();assert(m.rebuilds==1);
   }
   auto& cfg=w.b.team->at("Q")->radio;cfg.default_tx_power=80;
   cfg.pathloss_f=[&](double watts,auto& a,auto& b,bool& used){return m.ComputeReceivedPower(watts,a,b,used);};
   unsigned u=18;
   w.b.pose_update_f=[&](auto id){return std::make_tuple(true,Pose{id=="Base"?p[39]:p[u]},now);};
   int tick=0;size_t nReceipt=0;
   w.app.callbacks["Base:7"]=[&](auto src,auto,auto,auto bytes){assert(src=="Q"&&bytes==std::string(2,'a'));++nReceipt;++w.recv;};
   for(auto v:target){
     u=v;auto before=nReceipt;
     bool delivered=w.send("Q","Base",2,tick++);
     assert(nReceipt==before+int(delivered));
     std::cout<<l<<' '<<v<<' '<<int(delivered)<<'\n';
   }
 }
}
