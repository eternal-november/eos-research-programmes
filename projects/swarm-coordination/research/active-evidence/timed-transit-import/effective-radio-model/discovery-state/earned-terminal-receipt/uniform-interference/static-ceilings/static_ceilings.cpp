#include <array>
#define main prior
#include "staged_replay.inc"
#undef main
int main(int argc,char** argv){
 assert(argc==10);
 const unsigned pcap=std::stoi(argv[1]),qcap=std::stoi(argv[2]),bcap=std::stoi(argv[3]);
 const auto requested=std::string(argv[4]),timeline=std::string(argv[6]);
 const bool q_up=std::stoi(argv[5]),exact_guard=std::stoi(argv[8]);
 const unsigned bkg=std::stoi(argv[7]);
 assert(std::string(argv[9])=="sealed-fixture");
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
   const std::string key="IR:3/run7", other="IER:1/run7", third="IR:4/run7";
   auto add=[&](const std::string& n){
     auto x=std::make_shared<TeamNode>();x->name=n;x->radio=w.b.team->at("Q")->radio;
     x->radio.capacity=512;w.b.team->emplace(n,x);
   };
   add("X");
   w.b.team->at("P")->radio.capacity=8*pcap;
   if(!q_up)w.b.team->at("Q")->radio.pathloss_f=[](double,auto&,auto&,bool& via){
      via=false;return Power{-std::numeric_limits<double>::infinity(),0};
   };
   std::set<std::string> exact{"IR:3/prior"};
   int a_seen=0,b_seen=0,c_seen=0,excluded=0;
   w.app.callbacks["Base:7"]=[&](auto who,auto,auto,auto value){
     if((who=="P"||who=="Q")&&value==key){++a_seen;exact.insert(value);}
     if(who=="R"&&value==other)++b_seen;
     if(who=="P"&&value==third)++c_seen;
   };
   auto dispatch=[&](double t,const std::string& from,const std::string& dst,const std::string& value){
      now=t;w.b.incomingMsgs.push_back({from,dst,value});w.b.DispatchMessages();
   };
   dispatch(4.0,"Side","Sink","W");
   if(bkg>0)dispatch(4.125,"X","Base",std::string(bkg,'X'));
   double when=4.25;
   for(char event: timeline){
      if(event=='B')dispatch(when,"R","Base",other);
      else if(event=='C'){
        dispatch(when,"P","Base",third);
      }else if(event=='P'||event=='Q'){
        if(exact_guard&&exact.count(key))++excluded;
        else dispatch(when,std::string(1,event),"Base",key);
      }else assert(false);
      when+=0.125;
   }
   std::cout<<a_seen<<' '<<b_seen<<' '<<c_seen<<' '<<excluded<<' '
     <<w.state("P").bytes_sent_this_epoch<<' '<<w.state("Q").bytes_sent_this_epoch<<' '
     <<w.state("Base").bytes_received_this_epoch<<' '<<independent<<std::endl;
  }
 }
}
