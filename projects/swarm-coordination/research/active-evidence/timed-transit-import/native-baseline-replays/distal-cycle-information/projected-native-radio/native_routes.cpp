#include <array>
#include <fstream>
#define main inherited_cave_test
#include "staged_replay.inc"
#undef main

constexpr size_t N=20;
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
 int mask(const std::vector<size_t>& R,double range,bool moving=false,int stage=0){
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
   const auto a=w.send("P","Base",1,.75);
   if(stage==1)stage_relays();
   const auto b=w.send("Q","Base",1,1.);
   if(stage==2)stage_relays();
   assert(reads==int(a)+2*int(b));
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
 for(double range:{72.,80.,500.}){
    std::array<int,5> both{},ideal{},either{},notify{};
    size_t mask_mismatches=0;
    std::vector<size_t> stack,first;
    const auto scan=[&](auto&& self,size_t start)->void{
       auto m=t.mask(stack,range);
       size_t sz=stack.size();
       if(m==3){++both[sz];if(first.empty()||sz<first.size())first=stack;}
       if(m)++either[sz];
       const int other=int(t.ideal(stack,range,1))+2*int(t.ideal(stack,range,2));
       if(other==3)++ideal[sz];
       mask_mismatches+=other!=m;
       ++notify[sz];
       if(sz<4)for(size_t j=start;j<N;++j){
          stack.push_back(j);self(self,j+1);stack.pop_back();
       }
    };
    scan(scan,3);
    assert(t.mask({},range)==(range==72?0:2));
    if(!first.empty()){
       assert(t.mask(first,range,true)==t.mask({},range));
       assert(t.mask(first,range,false,1)==2);
       assert(t.mask(first,range,false,2)==t.mask({},range));
    }
    std::cout<<"range "<<range<<"; both";
    for(auto x:both)std::cout<<' '<<x;
    std::cout<<"; ideal";for(auto x:ideal)std::cout<<' '<<x;
    std::cout<<"; either";for(auto x:either)std::cout<<' '<<x;
    std::cout<<"; trials";for(auto x:notify)std::cout<<' '<<x;
    std::cout<<"; mismatched "<<mask_mismatches;
    std::cout<<"; sample";for(auto x:first)std::cout<<' '<<t.id[x];
    std::cout<<'\n';
 }
}
