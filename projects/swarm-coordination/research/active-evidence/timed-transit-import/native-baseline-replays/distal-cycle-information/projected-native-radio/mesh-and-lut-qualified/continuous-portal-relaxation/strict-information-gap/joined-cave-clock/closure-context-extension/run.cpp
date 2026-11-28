#include <algorithm>
#include "mission.cpp"
using GateMask=unsigned;
constexpr std::array<GateMask,4> history{0,1,2,3};
GateMask knowledge(GateMask support, const std::array<std::string,2>& reads) {
 GateMask out=0;
 for(auto w:history) if(support&(1<<w)){
    bool accept=true;
    for(int g:{0,1})
      if(!reads[g].empty()&&(reads[g]=="c")!=bool(w&(1<<g)))accept=false;
    if(accept)out|=1<<w;
 }
 return out;
}
GateMask allowed(GateMask fiber){
 if(!fiber)return 0;
 GateMask out=3;
 for(auto w:history) if(fiber&(1<<w))out&=(3^w);
 return out;
}
int main(int argc,char** argv){
 assert(argc==2);Scene s(argv[1]);
 std::string data;
 // Read the final four rows, independently from successful parses above.
 std::ifstream fs(argv[1]);std::deque<std::string> lines;
 while(std::getline(fs,data)){lines.push_back(data);if(lines.size()>4)lines.pop_front();}
 std::array<std::array<std::string,2>,4> ray;
 for(unsigned w:history){
   assert(lines.at(w).size()==3&&lines.at(w)[1]==' ');
   ray[w]={lines.at(w).substr(0,1),lines.at(w).substr(2,1)};
 }
 constexpr GateMask exclusive=6;
 constexpr GateMask wider=15;
 std::array<int,4> chosen{},strict{},invalidCounterfactual{};
 for(auto world:history)
 for(unsigned live=0;live<=3;++live)
 for(bool reverse:{false,true})
 for(bool late:{false,true})
 for(bool stagedAtStart:{false,true}){
   Radio r(s,6,stagedAtStart);
   auto& tr=r.w.tracker;
   std::array<std::string,2> seen;
   for(int step:{0,1}){
     if(step==1&&!stagedAtStart){
        for(size_t j:{3,4,5})
          tr.poses["probe__breadcrumb__"+std::to_string(j)+"__static__"]=Pose{s.xyz[j]};
        tr.UpdateIfNewBreadcrumbs();
     }
     const int i=reverse?1-step:step;
     if(!(live&(1<<i)))continue;
     const double t=.75+.25*step+.5*late;
     auto bytes=r.route(i?"Q":"P","Base",ray[world][i],t);
     if(t<=1.)seen[i]=bytes;
   }
   const auto actual=knowledge(wider,seen);
   const auto contracted=knowledge(exclusive,seen);
   assert(actual&(1<<world));
   const GateMask bound=allowed(actual);
   GateMask direct=0;
   for(int i:{0,1})if(seen[i]=="o")direct|=1<<i;
   // Transparent replacement law, all four context histories.
   assert(bound==direct);
   assert((bound&world)==0);
   if(bound){
      auto gate=bound&1?0:1;
      auto path=s.routeRequiringGate[gate];
      assert(s.path[path].front()==0);
      assert(s.path[path].back()==s.path[s.routeRequiringGate[1-gate]].back());
      ++chosen[world];
   }
   const GateMask claimed=allowed(contracted);
   strict[world]+=bool(claimed);
   invalidCounterfactual[world]+=(claimed&world)!=0;
 }
 for(auto w:history)
   std::cout<<w<<" universal_open_launch "<<chosen[w]<<" using_exclusive "<<strict[w]
            <<" unsafe_route_in_context "<<invalidCounterfactual[w]<<"\n";
}
