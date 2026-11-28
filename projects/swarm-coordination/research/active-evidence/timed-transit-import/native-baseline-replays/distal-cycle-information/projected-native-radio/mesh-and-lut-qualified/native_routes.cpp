#include <array>
#include <fstream>
#define main inherited_cave_test
#include "staged_replay.inc"
#undef main

constexpr size_t N=6;
struct Trial{
 std::array<uint64_t,N> id{};
 std::array<Point,N> xyz{};
 std::array<std::array<int,N>,N> D{};
 Trial(const char* path){
   std::ifstream f(path);
   for(size_t i=0;i<N;++i)assert(f>>id[i]>>xyz[i].x>>xyz[i].y>>xyz[i].z);
   for(auto& d:D)for(auto& w:d)assert(f>>w);
   assert(id[0]==103&&id[1]==118&&id[2]==117);
 }
 int mask(const std::vector<size_t>& R,double range,bool moving=false,int stage=0,bool reverse=false){
   World w(320);
   auto& tr=w.tracker;
   auto& m=*tr.visibilityModel;
   auto& tab=m.visibilityTable;
   m.defaultRangeConfig.max_range=range;
   m.defaultRangeConfig.scaling_factor=.55;
   for(size_t i=0;i<N;++i){
     tab.vertices.emplace(std::make_tuple(int32_t(xyz[i].x),int32_t(xyz[i].y),int32_t(xyz[i].z)),id[i]);
     tab.visibilityGraph.vertices.emplace(id[i],0);
     for(size_t j=0;j<N;++j)tab.visibilityGraph.projected[id[i]][id[j]]={double(D[i][j]),0};
   }
   tab.PopulateVisibilityInfo();
   auto stage_relays=[&](){
     for(size_t i:R)
       tr.poses["helper__breadcrumb__"+std::to_string(i)+(moving?"__moving__":"__static__")]=Pose{xyz[i]};
     tr.UpdateIfNewBreadcrumbs();
     assert(tr.visibilityModel->rebuilds==(!R.empty()&&!moving));
   };
   if(stage==0)stage_relays();
   for(const auto& id:{"P","Q"}){
     auto& cfg=w.b.team->at(id)->radio;
     cfg.default_tx_power=80;
     cfg.pathloss_f=[&](double watts,auto& a,auto& b,bool& used){
       return m.ComputeReceivedPower(watts,a,b,used);
     };
   }
   w.b.pose_update_f=[&](auto id){
     return std::make_tuple(true,Pose{xyz[id=="Base"?0:id=="P"?1:2]},now);
   };
   int reads=0;
   w.app.callbacks["Base:7"]=[&](auto src,auto,auto,auto bytes){
      assert(bytes=="a"&&(src=="P"||src=="Q"));
      reads|=(src=="P"?1:2);++w.recv;
   };
   const auto a=w.send(reverse?"Q":"P","Base",1,.75);
   if(stage==1)stage_relays();
   const auto b=w.send(reverse?"P":"Q","Base",1,1.);
   if(stage==2)stage_relays();
   assert(reads==(reverse?int(b)+2*int(a):int(a)+2*int(b)));
   for(const auto& who:{"P","Q"})assert(w.state(who).bytes_sent_this_epoch==1);
   return reads;
 }
 bool ideal(const std::vector<size_t>& R,double range,size_t src){
   // A generous independent-hop model, not proof of actual native route.
   std::vector<size_t> q{src},pool=R;
   std::array<bool,N> seen{};
   seen[src]=true;
   pool.push_back(0);
   for(size_t n=0;n<q.size();++n)for(auto b:pool){
      const auto a=q[n];
      if(!seen[b]&&D[a][b]<=10&&xyz[a].Distance(xyz[b])<=range){
        if(!b)return true;
        seen[b]=true;q.push_back(b);
      }
   }
   return false;
 }
};


int main(int argc,char** argv){
    assert(argc==2);Trial t(argv[1]);
    const std::vector<size_t> chosen{3,4,5};
    for(bool rev:{false,true}){
        for(int stage:{0,1,2}){
            int got=t.mask(chosen,72.,false,stage,rev);
            assert(got==(stage==0?3:stage==1?(rev?1:2):0));
            std::cout<<"reverse "<<rev<<" stage "<<stage<<" receipt_mask "<<got<<'\n';
        }
        assert(t.mask(chosen,72.,true,0,rev)==0);
    }
}
