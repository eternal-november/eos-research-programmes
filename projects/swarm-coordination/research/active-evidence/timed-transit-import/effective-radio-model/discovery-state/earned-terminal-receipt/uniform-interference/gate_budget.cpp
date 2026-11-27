#include <array>
#define main prior
#include "staged_replay.inc"
#undef main
int main(int argc,char** argv){
 assert(argc==6);
 const unsigned qcap=std::stoi(argv[1]),bcap=std::stoi(argv[2]);
 const std::string requested=argv[3], expiry=argv[4], filter=argv[5];
 assert(filter=="none"||filter=="exact"||filter=="family");
 assert(expiry=="closed"||expiry=="past");
 size_t n;std::cin>>n;
 for(size_t i=0;i<n;++i) {
  std::array<uint64_t,3> ids;
  for(auto& x:ids)std::cin>>x;
  std::array<std::array<double,3>,3> distance;
  for(auto& row:distance)for(auto& d:row)std::cin>>d;
  Point source,base,a,b;
  for(auto* p:{&source,&base,&a,&b})std::cin>>p->x>>p->y>>p->z;
  double range;std::cin>>range;
  for(std::string history:{requested}) {
   World w(32);
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
   auto second=std::make_shared<TeamNode>();
   second->name="R";second->radio=w.b.team->at("Q")->radio;second->radio.capacity=8*bcap;
   w.b.team->emplace("R",second);
   w.b.team->at("Q")->radio.capacity=8*qcap;
   auto& p=w.b.team->at("P")->radio;
   p.default_tx_power=80;p.pathloss_f=[&](double p,auto& s,auto& t,bool& used){
     return m.ComputeReceivedPower(p,s,t,used);
   };
   w.b.pose_update_f=[&](auto id){return std::make_tuple(true,Pose{id=="Base"?base:source},now);};
   const std::string key="IR:3/run7", other="IER:1/run7";
   std::vector<std::string> observed;
   std::set<std::string> dockRecords{"IR:3/prior"};
   w.app.callbacks["Base:7"]=[&](auto send,auto,auto,auto body){
      if((send=="P"||send=="Q")&&body==key){observed.push_back("A");dockRecords.insert(body);}
      if(send=="R"&&body==other)observed.push_back("B");
   };
   auto dispatch=[&](double t,const std::string& from,const std::string& dst,const std::string& payload){
     now=t;w.b.incomingMsgs.push_back({from,dst,payload});w.b.DispatchMessages();
   };
   dispatch(4.0,"P","Base",key);
   assert(observed.empty()||observed==std::vector<std::string>{"A"});
   std::cout<<(observed.empty()?"-":key)<<' '<<w.state("P").bytes_sent_this_epoch<<' '
             <<w.state("Base").bytes_received_this_epoch<<std::endl;
   dispatch(4.125,"Side","Sink","W");
   std::string cmd;assert(std::getline(std::cin>>std::ws,cmd));assert(!cmd.empty());
   const auto slot=expiry=="past"?5.125:5.0;
   unsigned p2=0,r2=0;
   for(char letter:cmd) {
     if(letter=='Q'){
       ++p2;
       // Alternative, fixture-owned enqueue authority at the dock. This
       // does not change native SubT or retroactively refund a debit.
       const auto head=key.substr(0,key.find('/'));
       const bool family=std::any_of(dockRecords.begin(),dockRecords.end(),[&](auto saved){
          return saved.substr(0,saved.find('/'))==head;
       });
       const bool fenced=(filter=="family"&&family)||(filter=="exact"&&dockRecords.count(key));
       if(!fenced)dispatch(slot,"Q","Base",key);
     }
     else if(letter=='B'){++r2;dispatch(slot,"R","Base",other);}
     else assert(false);
   }
   assert(p2<=1 && r2==1);
   auto n=[&](auto key){return std::count(observed.begin(),observed.end(),key);};
   std::cout<<n("A")<<' '<<n("B")<<' '<<w.state("Q").bytes_sent_this_epoch<<' '
    <<w.state("R").bytes_sent_this_epoch<<' '<<w.state("Base").bytes_received_this_epoch<<' '<<independent<<std::endl;
  }
 }
}
