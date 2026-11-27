#define main prior_main
#include <replay.cpp>
#undef main
#include "binding.inc"

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
   unsigned cap,capQ,capP; std::cin>>cap>>capQ>>capP;
   pose_ok=true; now=0; expected.clear(); w=std::make_unique<World>(cap);
   for(const std::string id:{"R","Side","Independent","SpareSide","Home"}) {
    auto t=std::make_shared<TeamNode>(*w->b.team->at("P"));
    t->name=id; (*w->b.team)[id]=t;
   }
   w->b.team->at("Q")->radio.capacity=8*capQ;
   w->b.team->at("P")->radio.capacity=8*capP;
   for(const std::string id:{"Base","Side","Home","Independent"}) {
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
  } else if(cmd=="bind") {
   std::string endpoint,arm;
   unsigned capQ,capP;
   std::cin>>endpoint>>arm>>capQ>>capP;
   bool allow=true;
   size_t reads=0;
   std::map<std::string,unsigned> bound{{"P",0},{"Q",0}},delta=bound;
   if(arm!="stock")w->b.beforeBind=[&](const std::string& key){
   for(const auto& entry:w->b.incomingMsgs) {
    ++reads;
    const auto& s=entry.src_address();
    if(!bound.count(s))continue;
    const auto& d=entry.dst_address();
    const auto bytes=entry.data().size();
    bool protected_entry=d=="Base"||d=="Home";
    if(protected_entry) {
     const unsigned cap=s=="P"?capP:capQ;
     if((s=="Q"||arm!="one-sender") && bound[s]+delta[s]+bytes>cap)allow=false;
    }
    const std::string ep=d+":7";
    bound[s]+=bytes*w->b.endpoints.at(ep).size();
    if(ep==key)delta[s]+=bytes;
   }
    return allow;
   };
   bool accepted=w->b.Bind("SpareSide",endpoint);
   w->b.beforeBind={};
   std::cout<<accepted<<' '<<reads<<std::endl;
  } else if(cmd=="unregister") {
   std::string id;std::cin>>id;
   std::cout<<w->b.Unregister(id)<<std::endl;
  } else assert(false);
 }
}
