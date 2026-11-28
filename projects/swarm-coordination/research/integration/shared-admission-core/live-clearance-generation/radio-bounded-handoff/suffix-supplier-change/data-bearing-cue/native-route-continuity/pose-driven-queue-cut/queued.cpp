#include <array>
#include <fstream>
#include "pinned_broker.h"
const std::array<uint64_t,5> ids{18,39,16,13,42};
const std::array<Point,5> p{Point{100,-25,0},Point{50,25,0},
   Point{100,100,0},Point{100,50,0},Point{100,75,0}};
void attach_visibility(Live& live,const char* matrix) {
 std::ifstream is(matrix);
 double d[5][5]; for(auto& row:d)for(auto& w:row)assert(is>>w);
 World& w=live.w;
   auto& tr=w.tracker;
   auto& m=*tr.visibilityModel;
   auto& t=m.visibilityTable;
   m.defaultRangeConfig.max_range=72.;
   m.defaultRangeConfig.scaling_factor=.55;
   for(unsigned i=0;i<ids.size();++i){
     t.vertices.emplace(std::make_tuple((int32_t)p[i].x,(int32_t)p[i].y,
                                         (int32_t)p[i].z),ids[i]);
     t.visibilityGraph.vertices.emplace(ids[i],0);
     for(unsigned j=0;j<ids.size();++j)
       t.visibilityGraph.projected[ids[i]][ids[j]]={d[i][j],0};
   }
   t.PopulateVisibilityInfo();

 w.b.pose_update_f=[](const auto& id){
    return std::make_tuple(true,Pose{id=="Base"?p[1]:(id=="P"?p[0]:p[2])},now);
 };
}


struct Replay{
 Live l{320};
 const std::string old=std::string(164,'b'),work=std::string(4,'x');
 std::vector<std::pair<std::string,std::string>> accepted;
 Replay(const char* matrix){
    attach_visibility(l,matrix);
    l.bind("aux","Far"); l.bind("sink","Base"); l.bind("diag","Side");
    auto& w=l.w; auto& t=w.tracker;
    t.brokerTarget=&w.b;
    t.poses={{"P",Pose{p[0]}},{"Q",Pose{p[2]}},{"Base",Pose{p[1]}},
             {"Far",Pose{p[1]}},{"Side",Pose{p[1]}}};
    w.b.pose_update_f=[&](auto id){
      const auto pose=t.poses.find(id);
      return std::make_tuple(pose!=t.poses.end(),pose==t.poses.end()?Pose{}:pose->second,now);
    };
    for(auto key:{"owed","aux","diag","sink"}){
      w.app.callbacks[std::string(key)+":7"]=[&,tag=std::string(key)](auto src,auto,auto,auto bytes){
         assert(!bytes.empty());accepted.emplace_back(tag,src);
      };
    }
    for(auto id:{"P","Q"}){
      auto& u=w.b.team->at(id)->radio; u.default_tx_power=80;
      const auto fallback=u.pathloss_f;
      u.pathloss_f=[&,fallback](double tx,auto& a,auto& b,bool& relay){
        // Route the needed old endpoint by native visibility. Fixture
        // Far/Side receive their authored unrelated traffic independently.
        if (&b==&w.state("Base") && w.path_available)
          return t.visibilityModel->ComputeReceivedPower(tx,a,b,relay);
        return fallback(tx,a,b,relay);
      };
    }
 }
 void enqueue(const std::string& s,const std::string& dst,const std::string& data){
    l.w.b.OnMessage({s,dst,data});
 }
 void event(int tick,int relay=0) {
    const auto kind=relay==1 ? "probe__breadcrumb__1__static__" : "probe__breadcrumb__2__static__";
    ignition::msgs::Pose_V event{{{tick/4,(tick%4)*250000000}}, {}};
    if(relay)event.entries.push_back({kind,Pose{p[relay==1?3:4]}});
    l.w.tracker.OnPose(event);
    assert(l.w.b.incomingMsgs.empty());
 }
 bool can_route(const std::string& s,int tick,size_t n){
    auto& w=l.w;
    auto tx=w.state(s), rx=w.state("Base");
    assert(w.tracker.poses.count(s)==1&&w.tracker.poses.count("Base")==1);
    tx.pose=w.tracker.poses.at(s);rx.pose=w.tracker.poses.at("Base");
    tx.update_stamp=rx.update_stamp=tick/4.;
    bool via=false;
    bool rf=std::isfinite(w.tracker.visibilityModel->ComputeReceivedPower(80,tx,rx,via).mean);
    return rf&&Live::used(tx.bytes_sent,tick)+n<=320&&Live::used(rx.bytes_received,tick)+n<=320;
 }
 bool delivered(const char* tag,const char* who)const{
    for(const auto& q:accepted)if(q.first==tag&&q.second==who)return true;
    return false;
 }
 void fixed(int d,int q){
    // TX-only debits in the last live window, followed by actual native
    // header/diagnostic and both early attempt queues.
    l.w.path_available=false;
    enqueue("P","sink",std::string(d,'p'));enqueue("Q","sink",std::string(q,'q'));event(5);
    l.w.path_available=true;
    enqueue("P","owed",std::string(114,'h'));enqueue("Q","diag",work);event(6);
    assert(delivered("owed","P")&&delivered("diag","Q"));
    accepted.clear();
    enqueue("Q","owed","a");enqueue("P","owed","a");event(7);
    assert(accepted.size()==1&&delivered("owed","P")&&!delivered("owed","Q"));
    assert(Live::used(l.w.state("P").bytes_sent,7)==d+115);
    assert(Live::used(l.w.state("Q").bytes_sent,7)==q+5);
    accepted.clear();
 }
};

int main(int argc,char** argv){
 assert(argc==2);
 size_t cases=0, oldCount[6]{}, sideCount[6]{}, wasted[6]{};
 for(int shape:{0,1,2})
 for(int d:{40,41,42})
 for(int q:{150,151,152})
 for(int strategy:{0,1,2,3,4,5}){
   Replay w(argv[1]);w.fixed(d,q);
   auto& b=w.l.w.b;
   // Both are pre-authorized immutable copies, and the shared early
   // result byte comes from P in all worlds. This C++ phase abstraction
   // only replays byte transport, not the journal join.
   auto bytes=w.old;
   std::string selected;
   if(strategy<2||strategy>=4){
     if(strategy==4) w.enqueue("P","aux",w.work);
     if(strategy==5) w.enqueue("Q","owed",bytes);
     w.enqueue("P","owed",bytes);
     if(strategy==1||strategy==4)w.enqueue("Q","owed",bytes);
     if(strategy!=4)w.enqueue("P","aux",w.work);
   }else{
     // This is a proposed receiver/broker-local hook at the native
     // pre-dispatch ordering point. It is not a stock API.
     b.beforeDispatch=[&](){
       const std::array<const char*,2> order=strategy==2?
           std::array<const char*,2>{"P","Q"}:std::array<const char*,2>{"Q","P"};
       for(const auto& s:order)if(w.can_route(s,8,bytes.size())){
         selected=s;w.enqueue(s,"owed",bytes);break;
       }
       w.enqueue("P","aux",w.work);
     };
   }
   w.event(8,shape);
   bool p=shape!=1&&d<=41, qgood=shape!=0&&q<=151;
   bool old=strategy==0?p:strategy==4?qgood:(p||qgood);
   assert((w.delivered("owed","P")||w.delivered("owed","Q"))==old);
   bool pAttempt=(strategy==0||strategy==1||strategy==5)?d<=41:
                 strategy==2?p:strategy==3?p&&!qgood:false;
   bool qAttempt=(strategy==1||strategy>=4)?q<=151:
                 strategy==2?!p&&qgood:strategy==3?qgood:false;
   bool side=!pAttempt;
   auto pUsed=Live::used(w.l.w.state("P").bytes_sent,8);
   auto qUsed=Live::used(w.l.w.state("Q").bytes_sent,8);
   assert(pUsed==d+115+int(pAttempt)*164+int(side)*4);
   assert(qUsed==q+5+int(qAttempt)*164);
   assert(Live::used(w.l.w.state("Base").bytes_received,8)==115+int(old)*164);
   wasted[strategy]+=(int(pAttempt)+int(qAttempt)-int(old))*164;
   assert(w.delivered("aux","P")==side);
   if(strategy==2)assert(selected==(p?"P":qgood?"Q":""));
   if(strategy==3)assert(selected==(qgood?"Q":p?"P":""));
   ++cases;oldCount[strategy]+=old;sideCount[strategy]+=side;
 }
 std::cout<<"cases "<<cases;
 for(const auto& row:{oldCount,sideCount,wasted}){
   std::cout<<" ;";for(int i=0;i<6;++i)std::cout<<' '<<row[i];
 }
 std::cout<<'\n';
}
