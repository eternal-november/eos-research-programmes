#define main prior_radio_main
#include <replay.cpp>
#undef main
#include <sstream>

namespace ignition { namespace math {
template<class> using Pose3=::Pose;
using Pose3d=::Pose;
}}
struct Frame {
 struct Marker {
  std::string id;
  Pose p;
  const auto& name()const{return id;}
 };
 std::vector<Marker> points;
 bool has_header()const{return false;}  // stamp already delivered on this fixture
 struct Header {
  bool has_stamp()const{return false;}
  struct Stamp {int sec()const{return 0;}int nsec()const{return 0;}};
  Stamp stamp()const{return {};}
 };
 Header header()const{return {};}
 int pose_size()const{return int(points.size());}
 const Marker& pose(int i)const{return points.at(i);}
};
namespace ignition { namespace msgs {
 Pose Convert(const Frame::Marker&m){return m.p;}
}}
struct Cache{
 struct Time {
  double t=0;
  double Double()const{return t;}
  void Set(int s,int ns){t=s+ns/1e9;}
 } simTime;
 std::map<std::string,Pose> poses;
 void ingest(const Frame& _msg){
 #include "frame.inc"
 }
 auto query(){
 #include "pose.inc"
  return updatePoseFunc;
 }
};
struct Outcome{
 int old=0,side=0,pending=0,tx=0,rx=0,stamped_current=0;
 auto tuple()const{return std::tie(old,side,pending,tx,rx,stamped_current);}
};
struct Fixture{
 World w;
 Cache cache;
 std::map<std::string,int> seen;
 std::vector<double> old,side;
 Fixture(unsigned cap):w(cap){
   for(std::string id:{"J","Far"}){
    auto n=std::make_shared<TeamNode>();
    n->name=id;n->radio=w.b.team->at("P")->radio;
    w.b.team->emplace(id,n);
   }
   for(auto [id,n]:*w.b.team)n->radio.pathloss_f=[](double,const auto&a,const auto&b,bool& crumbs){
     crumbs=false;
     return Power{std::abs(a.pose.p.x-b.pose.p.x)<=1000 ? 100. : -std::numeric_limits<double>::infinity(),0.};
   };
   w.b.pose_update_f=cache.query();
   w.b.endpoints["Far:7"]={{"Far"}};
   w.app.callbacks["Base:7"]=[&](auto s,auto,auto,const auto&p){
     if(s=="P" && p==std::string(173,'r'))old.push_back(now);
   };
   w.app.callbacks["Far:7"]=[&](auto s,auto,auto,const auto&p){
     assert(s=="Q"&&p=="side");
     side.push_back(now);
   };
 }
 void frame(double t,std::vector<Frame::Marker> samples){
   now=t; cache.simTime.t=t; // explicit timestamp delivered by test driver
   cache.ingest(Frame{samples});
   seen.clear();
   for(auto m:samples)seen[m.id]=m.p.p.x;
 }
 void scoped(unsigned shared_cap=0){
   // Declared dependency law for the two isolated unicast streams:
   // pose needs = endpoints; endpoint ledgers disjoint across streams.
   // This assumes no unlisted RF dependency such as a moving relay.
   std::deque<subt::msgs::Datagram> held;
   auto queue=std::move(w.b.incomingMsgs);
   for(const auto& msg:queue){
     auto keys=std::set<std::string>{msg.src_address(),msg.dst_address()};
     if(!std::all_of(keys.begin(),keys.end(),[&](auto k){return seen.count(k)>0;})){
       held.push_back(msg); continue;
     }
     // Restricted shared-ledger compatibility check for the declared
     // next cut: earlier held receives at this destination must still fit.
     // The fixture has at most one older such obligation, at .5 later.
     // No unrepresented receiver traffic or older debits in this arm.
     if(shared_cap){
       auto need=msg.data().size();
       for(const auto& old:held)
         if(old.dst_address()==msg.dst_address())need+=old.data().size();
       if(need>shared_cap){held.push_back(msg);continue;}
     }
     decltype(w.b.team)::element_type omitted;
     for(auto it=w.b.team->begin(); it!=w.b.team->end();){
       auto k=it++->first;
       if(!keys.count(k))omitted.insert(w.b.team->extract(k));
     }
     w.b.incomingMsgs.push_back(msg);
     w.b.DispatchMessages();
     assert(w.b.incomingMsgs.empty());
     w.b.team->merge(omitted);
   }
   w.b.incomingMsgs=std::move(held);
 }
 Outcome snapshot(){
   const auto& a=w.state("P");const auto& b=w.state("Base");
   return {int(old.size()),int(side.size()),int(w.b.incomingMsgs.size()),
           int(a.bytes_sent_this_epoch),int(b.bytes_received_this_epoch),
           int(a.update_stamp==now)};
 }
};
static auto pins(int pm,int jm){
 std::vector<Frame::Marker> m={{"Q",{{900}}},{"Base",{{0}}},{"Far",{{0}}}};
 if(pm>=0)m.push_back({"P",{{pm}}});
 if(jm>=0)m.push_back({"J",{{jm}}});
 return m;
}
int main(){
 int same=0;
 // frame mode: full, unrelated J never observed, P absent, P stale far,
 // P stale near. For last, independent evaluator's current P is far;
 // the stale cached pose must not count as licensed receiver evidence.
 for(int mode=0;mode<5;++mode)
 for(bool scope:{false,true})
 for(unsigned prior:{0,20,40})
 for(unsigned cap:{180,200,220})
 for(bool restore:{false,true}){
   if(mode==2 && prior)continue;
   Fixture f(cap);
   decltype(f.w.b.team)::element_type::node_type pending_member;
   if(mode==1)pending_member=f.w.b.team->extract("J");
   int pm=mode>=2?-1:900, jm=mode==1?-1:40;
   if(prior||mode>=3){
     f.frame(.25,pins(mode==4?900:2000,jm));
     if(prior){
       // Deterministically erased before the modeled geometric window.
       // Even when P cached near, send to different known-out client.
       auto old=f.w.b.team->at("P")->radio.pathloss_f;
       f.w.b.team->at("P")->radio.pathloss_f=[](double,const auto&,const auto&,bool& c){
         c=false;return Power{-std::numeric_limits<double>::infinity(),0};
       };
       f.w.b.incomingMsgs.push_back({"P","Base",std::string(prior,'d')});
       f.w.b.DispatchMessages();
       assert(f.w.state("P").bytes_sent_this_epoch==prior);
       assert(f.w.b.incomingMsgs.empty());
       f.w.b.team->at("P")->radio.pathloss_f=old;
     }
    }
   if(mode==1)f.w.b.team->insert(std::move(pending_member));
   f.frame(1.,pins(pm,jm));
   f.w.b.incomingMsgs.push_back({"P","Base",std::string(173,'r')});
   f.w.b.incomingMsgs.push_back({"Q","Far","side"});
   if(scope)f.scoped();else f.w.b.DispatchMessages();
   auto x=f.snapshot();
   bool physical_contact=(mode!=4);
   bool qualified=x.old&&physical_contact;
   assert(!(scope && x.old && !physical_contact));
   const bool oldblocked=scope?(mode>=2):(mode==1||mode==2);
   const bool sideblocked=!scope&&(mode==1||mode==2);
   const bool charged=!oldblocked && prior+173<=cap;
   assert(x.old==(charged&&mode!=3) && x.rx==173*x.old);
   assert(x.side==!sideblocked);
   assert(x.pending==int(oldblocked)+int(sideblocked));
   assert(x.tx==int(prior+173*charged));
   if(!scope&&mode>=3)assert(x.stamped_current); // not a newly observed pose
   assert(f.w.b.team->count("J")==1 && f.w.b.team->count("P")==1);
   if(restore){
     f.frame(1.5,pins(mode==4?2000:900,40));
     if(scope)f.scoped();else f.w.b.DispatchMessages();
     assert(f.w.b.incomingMsgs.empty());
     assert(f.old.size()==size_t(x.old+oldblocked*(mode!=4)));
     assert(f.side.size()==size_t(x.side+sideblocked));
     if(oldblocked&&mode!=4)assert(f.old.back()==1.5);
   }
   std::cout<<mode<<' '<<scope<<' '<<prior<<' '<<cap<<' '<<restore<<' '
            <<x.old<<' '<<x.side<<' '<<x.pending<<' '<<x.tx<<' '<<x.rx<<' '<<qualified<<'\n';
   ++same;
 }
 assert(same==156);
 // Negative control for an adapter that verifies only per-message
 // pose dependencies, ignoring shared downstream receive budget.
 for(unsigned cap:{200,233})for(int strategy:{0,1,2}){
   Fixture f(cap);
   int side_callback=0;
   f.w.app.callbacks["Base:7"]=[&](auto src,auto,auto,const auto& payload){
     if(src=="P"&&payload==std::string(173,'r'))f.old.push_back(now);
     if(src=="Q"&&payload==std::string(60,'s'))++side_callback;
   };
   auto dispatch=[&](){
     if(strategy==1)f.scoped();
     else if(strategy==2)f.scoped(cap);
     else f.w.b.DispatchMessages();
   };
   f.frame(1.,pins(-1,40));
   f.w.b.incomingMsgs.push_back({"P","Base",std::string(173,'r')});
   f.w.b.incomingMsgs.push_back({"Q","Base",std::string(60,'s')});
   dispatch();
   bool early=strategy==1 || (strategy==2&&cap==233);
   assert(side_callback==early && f.old.empty());
   f.frame(1.5,pins(900,40));
   dispatch();
   const auto x=f.snapshot();
   bool old=cap==233||!early;
   bool side=cap==233||early;
   assert(x.old==old && side_callback==side);
   assert(x.tx==173 && x.rx==173*old+60*side);
   std::cout<<"shared-receiver "<<cap<<' '<<strategy<<' '<<early<<' '
      <<x.old<<' '<<side_callback<<' '<<x.tx<<' '<<x.rx<<'\n';
 }
}
