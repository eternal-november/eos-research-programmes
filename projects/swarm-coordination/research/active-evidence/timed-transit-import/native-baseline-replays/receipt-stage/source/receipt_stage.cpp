// Compiled against the pinned selected native #726 extraction.
#include <array>
#include <fstream>
#define main earlier_replay
#include "staged_replay.inc"
#undef main


struct Result{bool old,new_work;int receipt;};
Result run_case(unsigned target,int old_tick,int new_tick,int activation,int delay){
 const std::array<uint64_t,5> ids{18,39,16,13,42};
 const std::array<Point,5> p{Point{100,-25,0},Point{50,25,0},
   Point{100,100,0},Point{100,50,0},Point{100,75,0}};
 std::ifstream is("distances.tsv");
 double d[5][5];for(auto& row:d)for(auto& w:row)assert(is>>w);
 World w(256);
 auto& tr=w.tracker;auto& m=*tr.visibilityModel;auto& t=m.visibilityTable;
 m.defaultRangeConfig.max_range=72.;
 m.defaultRangeConfig.scaling_factor=.55;
 for(unsigned i=0;i<ids.size();++i){
   t.vertices.emplace(std::make_tuple((int32_t)p[i].x,(int32_t)p[i].y,(int32_t)p[i].z),ids[i]);
   t.visibilityGraph.vertices.emplace(ids[i],0);
   for(unsigned j=0;j<ids.size();++j)t.visibilityGraph.projected[ids[i]][ids[j]]={d[i][j],0};
 }
 t.PopulateVisibilityInfo();
 for(const auto& id:{"P","Q"}){
   auto& cfg=w.b.team->at(id)->radio;
   cfg.default_tx_power=80;
   cfg.pathloss_f=[&](double watts,auto& a,auto& b,bool& used){return m.ComputeReceivedPower(watts,a,b,used);};
 }
 w.b.pose_update_f=[&](auto id){return std::make_tuple(true,Pose{id=="Base"?p[1]:(id=="P"?p[0]:p[2])},now);};
 int receipt=999;bool deliveredP=false,deliveredQ=false;
 w.app.callbacks["Base:7"]=[&](auto id,auto,auto,auto bytes){
   assert(bytes==std::string(2,'a'));
   if(id=="P"){deliveredP=true;receipt=old_tick+delay;}else {assert(id=="Q");deliveredQ=true;}
   ++w.recv;
 };
 for(int u=0;u<=10;++u){
   if(u==activation){
     tr.poses["probe__breadcrumb__1__static__"]=Pose{p[target]};
     tr.UpdateIfNewBreadcrumbs();
   }
   if(u==old_tick)w.send("P","Base",2,u);
   if(u==new_tick)w.send("Q","Base",2,u);
 }
 assert(deliveredP==(target==4||activation>old_tick));
 assert(deliveredQ==(activation<=new_tick));
 return {deliveredP,deliveredQ,receipt};
}
int main(){
 int native=0,robust=0,blocked=0;
 for(unsigned site:{3u,4u})for(int p=1;p<=3;++p)for(int b=p+1;b<=8;++b)
 for(int k=0;k<=9;++k){run_case(site,p,b,k,0);++native;}
 for(int p=1;p<=3;++p)for(int b=p+1;b<=8;++b)
 for(int delay=0;delay<=3;++delay)for(int lower=1;lower<=3;++lower)
 for(int upper=lower;upper<=3;++upper){
   // Obtain the controller's signal from an actual unactivated source
   // prefix. Only the receiver's true successful P event starts the timer.
   const auto prefix=run_case(3,p,b,99,delay);++native;
   assert(prefix.old&&!prefix.new_work);
   const bool guard=prefix.receipt+upper<=b;
   const int chosen=guard?prefix.receipt:99;
   bool okay=true;
   for(int latency=lower;latency<=upper;++latency){
      auto r=run_case(3,p,b,chosen+latency,delay);++native;
      assert(r.old);
      okay &=r.new_work;
   }
   assert(okay==guard);
   robust+=okay;blocked+=!okay;
 }
 // One fixed activation cannot serve both hidden configurations. The
 // receiver can act at its own old-delivery cut, with one tick to effect.
 for(int k=0;k<=5;++k){
    auto early=run_case(3,1,2,k,0),late=run_case(3,3,4,k,0);
    assert(!(early.old&&early.new_work&&late.old&&late.new_work));native+=2;
 }
 for(int p:{1,3}){
   auto first=run_case(3,p,p+1,99,0);++native;
   auto own=run_case(3,p,p+1,first.receipt+1,0);++native;
   assert(own.old&&own.new_work);
   auto far=run_case(4,p,p+1,1,0);++native;assert(far.old&&far.new_work);
   auto late=run_case(3,p,p+1,p+2,1);++native;
   assert(late.old&&!late.new_work);native+=3;
 }
 std::cout<<native<<" exact selected source runs; "<<robust<<" supported receipt-time activations; "
          <<blocked<<" no guarantee by waiting for that delayed observation\n";
}
