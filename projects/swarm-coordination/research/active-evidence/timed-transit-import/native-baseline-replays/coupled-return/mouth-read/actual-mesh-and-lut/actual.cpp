// Compiled against the pinned selected native #726 extraction.
#include <array>
#include <fstream>
#define main earlier_replay
#include "staged_replay.inc"
#undef main


#include "load.inc"
int contacts(){
 const std::array<uint64_t,5> ids{18,39,16,13,42};
 const std::array<Point,5> p{Point{100,-25,0},Point{50,25,0},Point{100,100,0},Point{100,50,0},Point{100,75,0}};
 std::ifstream is("distances.tsv");
 double d[5][5];for(auto& row:d)for(auto& w:row)assert(is>>w);
 World w(256);auto& tr=w.tracker;auto& m=*tr.visibilityModel;auto& t=m.visibilityTable;
 m.defaultRangeConfig.max_range=72.;m.defaultRangeConfig.scaling_factor=.55;
 for(unsigned i=0;i<ids.size();++i){
   t.visibilityGraph.vertices.emplace(ids[i],0);
   for(unsigned j=0;j<ids.size();++j)t.visibilityGraph.projected[ids[i]][ids[j]]={d[i][j],0};
 }
 t.lutPath="cave.dat";
 assert(t.LoadLUT());
 std::cout<<t.vertices.size()<<'\n';
 auto in=std::make_shared<TeamNode>(*w.b.team->at("P"));
 in->name="I";(*w.b.team)["I"]=in;
 for(const auto& id:{"P","I","Q"}){
   auto& cfg=w.b.team->at(id)->radio;cfg.default_tx_power=80;
   cfg.pathloss_f=[&](double watts,auto& a,auto& b,bool& used){return m.ComputeReceivedPower(watts,a,b,used);};
 }
 Point s=p[3];
 w.b.pose_update_f=[&](auto id){
   return std::make_tuple(true,Pose{id=="Base"?p[1]:(id=="P"?p[0]:(id=="Q"?p[2]:s))},now);
 };
 bool old=false;
 w.app.callbacks["Base:7"]=[&](auto id,auto,auto,auto bytes){assert(id=="P"&&bytes=="aa");old=true;++w.recv;};
 w.app.callbacks["Q:7"]=[&](auto id,auto,auto,auto bytes){assert(id=="I"&&bytes=="a");++w.recv;};
 assert(w.send("P","Base",2,0)&&old);
 int k=1;
 for(int x=95;x<=105;++x)for(int y=50;y<=75;++y)for(int z=0;z<=10;++z){
   s=Point{double(x),double(y),double(z)};
   auto it=t.vertices.find(std::make_tuple(x,y,z));
   int label=it==t.vertices.end()?-1:int(it->second);
   auto ok=w.send("I","Q",1,k++);
   std::cout<<x<<' '<<y<<' '<<z<<' '<<label<<' '<<int(ok)<<'\n';
 }
 return 0;
}

int main(){
 assert(contacts()==0);
 const std::array<uint64_t,6> ids{18,39,16,13,42,6};
 const std::array<Point,6> p{Point{100,-25,0},Point{50,25,0},Point{100,100,0},
  Point{100,50,8},Point{100,75,8},Point{75,100,0}};
 std::ifstream tbl("dist6.tsv");
 double d[6][6];for(auto& row:d)for(auto& v:row)assert(tbl>>v);
 for(unsigned branch:{3u,4u}){
    World w(256);auto& tr=w.tracker;auto& m=*tr.visibilityModel;auto& t=m.visibilityTable;
    m.defaultRangeConfig.max_range=72.;m.defaultRangeConfig.scaling_factor=.55;
    for(unsigned i=0;i<ids.size();++i){
      t.visibilityGraph.vertices.emplace(ids[i],0);
      for(unsigned j=0;j<ids.size();++j)t.visibilityGraph.projected[ids[i]][ids[j]]={d[i][j],0};
    }
    t.lutPath="cave.dat";assert(t.LoadLUT());
    for(const auto& id:{"P","Q"}){
      auto& cfg=w.b.team->at(id)->radio;cfg.default_tx_power=80;
      cfg.pathloss_f=[&](double watts,auto& a,auto& b,bool& used){return m.ComputeReceivedPower(watts,a,b,used);};
    }
    w.b.pose_update_f=[&](auto id){
      return std::make_tuple(true,Pose{id=="Base"?p[1]:(id=="P"?p[0]:(branch==3?p[5]:p[2]))},now);
    };
    assert(w.send("P","Base",2,0.));
    assert(!w.send("Q","Base",2,1.));
    tr.poses["experiment__breadcrumb__1__static__"]=Pose{p[branch]};
    tr.UpdateIfNewBreadcrumbs();assert(m.rebuilds==1);
    assert(w.send("P","Base",2,2.)==(branch==4));
    assert(w.send("Q","Base",2,3.));
    std::cout<<"stage "<<ids[branch]<<" altitude 8 delivers branch report\n";
 }
}
