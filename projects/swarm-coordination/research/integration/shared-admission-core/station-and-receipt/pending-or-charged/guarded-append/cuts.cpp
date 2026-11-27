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
   pose_ok=true; now=0; expected.clear(); w=std::make_unique<World>(cap);
   for(const std::string id:{"R","Side","Independent","SpareSide"}) {
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
  } else if(cmd=="fanout") {
   assert(w->b.endpoints.at("Side:7").size()==1);
   w->b.endpoints.at("Side:7").push_back({"SpareSide"});
   std::cout<<"ok"<<std::endl;
  } else if(cmd=="commit") {
   // This lock is the one used by native DispatchMessages. No dispatch,
   // callbacks, pose updates or sleeps are performed under our commit.
   unsigned cap, at; int live_primary, allow_remove, full;
   std::string dh, rh;
   std::cin>>cap>>at>>live_primary>>allow_remove>>full>>dh>>rh;
   auto probe=decode(dh),report=decode(rh);
   std::string sender="R";
   size_t ledger_reads=0, queue_reads=0;
   bool removed=false;
   {
    std::lock_guard<std::mutex> lk(w->b.mutex);
    auto& q=w->b.incomingMsgs;
    auto match=[&](const auto& p){return p.src_address()=="Q"&&p.dst_address()=="Side"&&p.data()==probe;};
    assert(now<=at/4.); now=at/4.; // fixture monotone clock
    if(live_primary && cap>=report.size()) {
     unsigned charge=0, projected=0;
     for(const auto& [t,b]:w->state("Q").bytes_sent) {
      ++ledger_reads;
      if(now-t<=1)charge+=b;
     }
     auto optional=q.end(); unsigned optional_cost=0;
     for(auto i=q.begin();i!=q.end();++i) {
      ++queue_reads;
      unsigned bytes=0;
      if(i->src_address()=="Q") {
       auto e=w->b.endpoints.find(i->dst_address()+":"+std::to_string(i->dst_port()));
       bytes=i->data().size()*(full ? (e==w->b.endpoints.end()?0:e->second.size()) : 1);
       projected+=bytes;
      }
      if(match(*i)) {assert(optional==q.end()); optional=i; optional_cost=bytes;}
     }
     if(charge+projected+report.size()<=cap) sender="Q";
     else if(allow_remove && optional!=q.end() &&
             charge+projected+report.size()<=cap+optional_cost) {
      q.erase(optional); removed=true; sender="Q";
     }
    }
    if(cap<report.size()) sender="-";
    else {
     expected["Base"]=report;
     q.push_back({sender,"Base",report});
    }
   }
   std::cout<<sender<<' '<<removed<<' '<<ledger_reads<<' '<<queue_reads<<std::endl;
  } else if(cmd=="tx") {
   unsigned at;std::string s;std::cin>>at>>s;
   unsigned used=0;
   for(const auto& [t,b]:w->state(s).bytes_sent)if(at/4.-t<=1)used+=b;
   std::cout<<used<<std::endl;
  } else assert(false);
 }
}
