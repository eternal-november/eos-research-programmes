// Compiled against the pinned selected native #726 extraction.
#include <array>
#include <fstream>
#define main earlier_replay
#include "staged_replay.inc"
#undef main

int main() {
 const std::array<uint64_t,5> ids{18,39,16,13,42};
 const std::array<Point,5> p{Point{100,-25,0},Point{50,25,0},
   Point{100,100,0},Point{100,50,0},Point{100,75,0}};
 std::ifstream is("distances.tsv");
 double d[5][5]; for(auto& row:d)for(auto& w:row)assert(is>>w);
 size_t checks=0, plans=0, both=0;
 for(double range:{69.,71.,72.,74.,75.,76.,500.})
 for(size_t target:{3u,4u})
 for(bool reverse:{false,true})
 for(int cut:{-1,0,1,2,3}){
   World w(256);
   auto& tr=w.tracker;
   auto& m=*tr.visibilityModel;
   auto& t=m.visibilityTable;
   m.defaultRangeConfig.max_range=range;
   m.defaultRangeConfig.scaling_factor=.55;
   for(unsigned i=0;i<ids.size();++i){
     t.vertices.emplace(std::make_tuple((int32_t)p[i].x,(int32_t)p[i].y,
                                         (int32_t)p[i].z),ids[i]);
     t.visibilityGraph.vertices.emplace(ids[i],0);
     for(unsigned j=0;j<ids.size();++j)
       t.visibilityGraph.projected[ids[i]][ids[j]]={d[i][j],0};
   }
   t.PopulateVisibilityInfo();
   for(const auto& id:{"P","Q"}){
     auto& cfg=w.b.team->at(id)->radio;
     cfg.default_tx_power=80;
     cfg.pathloss_f=[&](double watts,auto& a,auto& b,bool& used){
       return m.ComputeReceivedPower(watts,a,b,used);
     };
   }
   w.b.pose_update_f=[&](auto id){
     return std::make_tuple(true,Pose{id=="Base"?p[1]:(id=="P"?p[0]:p[2])},now);
   };
   size_t qualified_receipts=0;
   w.app.callbacks["Base:7"]=[&](auto src,auto,auto,auto bytes){
     assert(bytes==std::string(2,'a'));assert(src=="P"||src=="Q");
     ++qualified_receipts;++w.recv;
   };
   double time=0;
   auto check=[&](int activeBy) {
     int delivered=0;
     for(unsigned j=0;j<2;++j){
       if(cut!=-1 && int(j)==cut) {
         tr.poses["probe__breadcrumb__1__static__"]=Pose{p[target]};
         tr.UpdateIfNewBreadcrumbs();
       }
       const bool active=int(j)>=activeBy;
       const bool old=(j==0)!=reverse;const auto i=old?0u:2u;
       const int direct=old?10:13;
       auto cost=direct;double rr=old?std::sqrt(5000.):std::sqrt(8125.);
       bool expectedRelay=false;
       if(active&&target==3){
         cost=9;rr=old?75.:std::sqrt(3125.);expectedRelay=true;
       }else if(active&&target==4&&!old){
         cost=10;rr=std::sqrt(5000.);expectedRelay=true;
       }
       auto actual=t.Cost(p[i],p[1]);
       assert(actual.cost==cost);
       assert(actual.route.size()==size_t(expectedRelay));
       if(expectedRelay)assert(actual.route.front()==ids[target]);
       bool used=false;radio_state a{Pose{p[i]}},b{Pose{p[1]}};
       auto rf=m.ComputeReceivedPower(80,a,b,used);
       const auto expected=cost<=10&&rr<=range;
       assert(std::isfinite(rf.mean)==expected);
       if(cost<=10)assert(used==expectedRelay);
       auto prestep=qualified_receipts;
       assert(w.send(old?"P":"Q","Base",2,time++)==expected);
       assert(qualified_receipts==prestep+expected);
       delivered+=expected; ++checks;
     }
     return delivered;
   };
   if(cut!=-1){
     auto n=check(cut); ++plans; both+=n==2;
     if(range==72.){
       const bool win=target==4 ? cut<=int(reverse?0:1) : !reverse && cut==1;
       assert((n==2)==win);
     }
     continue;
   }
   check(2);
   tr.poses["probe__breadcrumb__moving"]=Pose{p[target]};
   tr.UpdateIfNewBreadcrumbs();assert(m.rebuilds==0);check(2);
   const std::string name="probe__breadcrumb__1__static__";
   tr.poses.erase("probe__breadcrumb__moving");
   tr.poses[name]=Pose{p[target]};
   tr.UpdateIfNewBreadcrumbs();assert(m.rebuilds==1);check(0);
   tr.poses.erase(name);
   tr.UpdateIfNewBreadcrumbs();assert(m.rebuilds==1);check(0);
   tr.poses[name]=Pose{p[target==3?4:3]};
   tr.UpdateIfNewBreadcrumbs();assert(m.rebuilds==1);check(0);
 }
 assert(checks==504 && plans==112);
 std::cout<<"native RF/qualified callback trials "<<checks<<'\n';
 std::cout<<"joined dispatch schedules "<<plans<<"; both reports "<<both<<'\n';
}
