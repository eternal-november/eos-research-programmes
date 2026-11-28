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
 std::array<std::array<std::string,2>,2> beam{};
 Trial(const char* path){
   std::ifstream f(path);
   for(size_t i=0;i<N;++i)assert(f>>id[i]>>xyz[i].x>>xyz[i].y>>xyz[i].z);
   for(auto& d:D)for(auto& w:d)assert(f>>w);
   for(auto& world:beam)for(auto& observed:world)assert(f>>observed&&(observed=="c"||observed=="o"));
   assert(id[0]==103&&id[1]==118&&id[2]==117);
 }
 int mask(const std::vector<size_t>& R,double range,bool moving=false,int stage=0,bool reverse=false,int closed=0,int live=3,int slow=0){
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
   int reads=0, announced=-1;
   w.app.callbacks["Base:7"]=[&](auto src,auto,auto,auto bytes){
      assert((bytes=="c"||bytes=="o")&&(src=="P"||src=="Q"));
      if(now<=1.){
          reads|=(src=="P"?1:2);
          const auto caseForSender=src=="P"?0:1;
          const int v=bytes=="c"?caseForSender:1-caseForSender;
          if(announced<0)announced=v;
          else assert(announced==v);
      }
      ++w.recv;
   };
   auto tell=[&](int who,double at){
       if(!(live&(1<<who))) return;
       now=at;
       w.b.incomingMsgs.push_back({who==0?"P":"Q","Base",beam[closed][who]});
       w.b.DispatchMessages();
       assert(w.b.incomingMsgs.empty());
   };
   tell(int(reverse),.75+.5*slow);
   if(stage==1)stage_relays();
   tell(1-int(reverse),1.+.5*slow);
   if(stage==2)stage_relays();
   for(int who:{0,1})
      assert(w.state(who==0?"P":"Q").bytes_sent_this_epoch==unsigned(bool(live&(1<<who))));
   assert(announced==-1||announced==closed);
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
   std::vector<size_t> staged{3,4,5};
   std::array<int,2> admitted{};
   int cases=0;
   for(int closed:{0,1})
   for(int live:{0,1,2,3})
   for(int stage:{0,1,2})
   for(bool reverse:{false,true})
   for(bool moving:{false,true})
   for(int slow:{0,1}){
      auto got=t.mask(staged,72.,moving,stage,reverse,closed,live,slow);
      auto wanted=slow||moving||stage==2?0:stage==0?live:live&(reverse?1:2);
      assert(got==wanted);
      admitted[closed]+=got!=0;
      ++cases;
   }
   std::cout<<"traces "<<cases<<" qualified_choices "<<admitted[0]<<' '<<admitted[1]<<'\n';
}
