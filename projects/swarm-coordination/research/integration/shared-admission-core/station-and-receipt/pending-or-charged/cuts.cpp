#define main prior_main
#include <replay.cpp>
#undef main

// Authored single-thread adapter. The native broker owns the deque, pose
// gating, dispatch order, rolling debits, and receive callbacks.
int main() {
 std::unique_ptr<World> w;
 bool pose_ok=true;
 std::vector<std::pair<std::string,std::string>> got;
 std::map<std::string,std::string> expected;
 std::string cmd;
 auto decode=[](const std::string& x) {
  assert(x.size()%2==0); std::string out;
  for(size_t i=0;i<x.size();i+=2)out+=char(std::stoi(x.substr(i,2),nullptr,16));
  return out;
 };
 while(std::cin>>cmd) {
  if(cmd=="reset") {
   unsigned cap; std::cin>>cap;
   pose_ok=true; expected.clear(); w=std::make_unique<World>(cap);
   for(const std::string id:{"R","Side","Independent"}) {
    auto t=std::make_shared<TeamNode>(*w->b.team->at("P"));
    t->name=id; (*w->b.team)[id]=t;
   }
   for(const std::string id:{"Base","Side","Independent"}) {
    if(id!="Base")w->b.endpoints[id+":7"].push_back({id});
    w->app.callbacks[id+":7"]=[&,id](auto src,auto,auto,auto data){assert(expected.at(id)==data);got.emplace_back(src,data);};
   }
   w->b.pose_update_f=[&](const std::string& n){return std::make_tuple(pose_ok||n!="Side",Pose{},now);};
   std::cout<<"ok"<<std::endl;
  } else if(cmd=="enqueue") {
   std::string s,d,hex; std::cin>>s>>d>>hex;
   auto payload=decode(hex);
   assert(!expected.count(d)||expected.at(d)==payload);
   expected[d]=payload;
   w->b.incomingMsgs.push_back({s,d,payload});
   std::cout<<"ok"<<std::endl;
  } else if(cmd=="dispatch") {
   unsigned at;int pose,path;std::cin>>at>>pose>>path;
   now=at/4.;pose_ok=pose;w->path_available=path;got.clear();
   w->b.DispatchMessages();
   std::cout<<got.size();
   for(const auto& [s,v]:got)std::cout<<' '<<s<<':'<<v.size();
   std::cout<<std::endl;
  } else if(cmd=="pending"||cmd=="remove") {
   std::string s,d,hex;std::cin>>s>>d>>hex;
   auto v=decode(hex);auto& q=w->b.incomingMsgs;
   auto match=[&](const auto& p){return p.src_address()==s&&p.dst_address()==d&&p.data()==v;};
   auto n=std::count_if(q.begin(),q.end(),match);
   assert(n<=1);
   if(cmd=="remove"&&n)q.erase(std::find_if(q.begin(),q.end(),match));
   std::cout<<n<<std::endl;
  } else if(cmd=="tx") {
   unsigned at;std::string s;std::cin>>at>>s;
   unsigned used=0;
   for(const auto& [t,b]:w->state(s).bytes_sent)if(at/4.-t<=1)used+=b;
   std::cout<<used<<std::endl;
  } else assert(false);
 }
}
