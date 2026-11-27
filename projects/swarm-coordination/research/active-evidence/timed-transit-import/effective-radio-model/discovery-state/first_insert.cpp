#include <array>
#define main prior
#include "staged_replay.inc"
#undef main
int main(){
 size_t n;std::cin>>n;
 for(size_t i=0;i<n;++i) {
  std::array<uint64_t,3> ids;
  for(auto& x:ids)std::cin>>x;
  std::array<std::array<double,3>,3> distance;
  for(auto& row:distance)for(auto& d:row)std::cin>>d;
  Point source,base,a,b;
  for(auto* p:{&source,&base,&a,&b})std::cin>>p->x>>p->y>>p->z;
  double range;std::cin>>range;
  for(std::string history:{"a","b","ab","ba","batch","none","restore-ab","restore-ba"}) {
   World w(12);
   auto& tracker=w.tracker;
   auto& m=*tracker.visibilityModel;
   auto& table=m.visibilityTable;
   auto& graph=table.visibilityGraph;
   m.defaultRangeConfig.max_range=range;
   auto set=[](auto &tab,Point p,uint64_t id) {
     auto key=std::make_tuple(int32_t(std::round(p.x)),int32_t(std::round(p.y)),int32_t(std::round(p.z)));
     auto [it,inserted]=tab.emplace(key,id);assert(inserted||it->second==id);
   };
   set(table.vertices,source,ids[0]);set(table.vertices,a,ids[1]);
   set(table.vertices,b,ids[1]);set(table.vertices,base,ids[2]);
   for(int j=0;j<3;++j) {
     graph.vertices.emplace(ids[j],0);
     for(int k=0;k<3;++k)graph.projected[ids[j]][ids[k]]={distance[j][k],0};
   }
   table.PopulateVisibilityInfo();
   auto prep=[&](char c){
     tracker.poses[std::string("site__breadcrumb__static__")+c]=Pose{c=='a'?a:b};
   };
   const bool restore=history.rfind("restore-",0)==0;
   if(history=="batch"){prep('a');prep('b');tracker.UpdateIfNewBreadcrumbs();}
   else if(history!="none"){
     for(char c:restore?history.substr(8):history){prep(c);tracker.UpdateIfNewBreadcrumbs();}
   }
   if(restore){
     auto known=tracker.breadcrumbs;
     auto graph_input=graph;
     auto vertex_lookup=table.vertices;
     std::vector<Point> firsts;
     for(const auto& t:table.breadcrumbs)firsts.push_back(t.second.front());
     // Cold reconstructed route table seeded only with the preserved firsts.
     table=VisibilityTable{};
     table.visibilityGraph=graph_input;table.vertices=vertex_lookup;
     for(Point p:firsts){
       auto key=std::make_tuple(int32_t(std::round(p.x)),int32_t(std::round(p.y)),int32_t(std::round(p.z)));
       table.breadcrumbs[table.vertices.at(key)].push_back(p);
     }
     std::set<Point> positions;
     for(const auto& n:known)positions.insert(n.second.Pos());
     m.PopulateVisibilityInfo(positions);
   }
   // Actual update hook is also called at steady state. With no new static
   // names it leaves the first point in the visibility table unchanged.
   tracker.UpdateIfNewBreadcrumbs();
   auto v=table.Cost(source,base);
   auto side=std::make_shared<TeamNode>();
   side->name="Side";side->radio=w.b.team->at("Q")->radio;
   w.b.team->emplace(side->name,side);
   auto sink=std::make_shared<TeamNode>();
   sink->name="Sink";sink->radio=w.b.team->at("Q")->radio;
   w.b.team->emplace(sink->name,sink);
   w.b.endpoints["Sink:7"]={{"Sink"}};
   unsigned independent=0;
   w.app.callbacks["Sink:7"]=[&](auto s,auto,auto,auto msg){if(s=="Side"&&msg=="W")++independent;};
   auto& p=w.b.team->at("P")->radio;
   p.default_tx_power=80;p.pathloss_f=[&](double p,auto& s,auto& t,bool& used){
     return m.ComputeReceivedPower(p,s,t,used);
   };
   w.b.pose_update_f=[&](auto id){return std::make_tuple(true,Pose{id=="Base"?base:source},now);};
   bool used=false;
   radio_state from{Pose{source}},to{Pose{base}};
   const auto r=m.ComputeReceivedPower(80,from,to,used);
   bool received=w.send("P","Base",2,4.0);
   now=4.25;w.b.incomingMsgs.push_back({"Side","Sink","W"});
   w.b.DispatchMessages();
   assert(independent==1);
   auto front=v.route.empty()?0:(v.posFirstBreadcrumb.Distance(a)<1e-8?'a':'b');
   std::cout<<ids[0]<<' '<<ids[1]<<' '<<ids[2]<<' '<<history<<' '
     <<m.rebuilds<<' '<<tracker.breadcrumbs.size()<<' '<<v.cost<<' '
     <<v.route.size()<<' '<<front<<' '<<std::isfinite(r.mean)<<' '<<used<<' '
     <<received<<' '<<w.state("Base").bytes_received_this_epoch<<' '<<independent<<'\n';
  }
 }
}
