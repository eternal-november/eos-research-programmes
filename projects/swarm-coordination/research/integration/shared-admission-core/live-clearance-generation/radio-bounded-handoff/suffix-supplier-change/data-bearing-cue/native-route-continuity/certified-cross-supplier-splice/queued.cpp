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
 const std::string work=std::string(4,'x');
 struct Arrival{std::string tag,from,data;};
 std::vector<Arrival> accepted;
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
         assert(!bytes.empty());accepted.push_back({tag,src,bytes});
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
 bool route(const std::string& s,int tick){
    auto& w=l.w;
    auto tx=w.state(s), rx=w.state("Base");
    assert(w.tracker.poses.count(s)==1&&w.tracker.poses.count("Base")==1);
    tx.pose=w.tracker.poses.at(s);rx.pose=w.tracker.poses.at("Base");
    tx.update_stamp=rx.update_stamp=tick/4.;
    bool via=false;
    bool rf=std::isfinite(w.tracker.visibilityModel->ComputeReceivedPower(80,tx,rx,via).mean);
    return rf;
 }
 bool delivered(const char* tag,const char* who)const{
    for(const auto& q:accepted)if(q.tag==tag&&q.from==who)return true;
    return false;
 }
 std::pair<std::string,std::string> fixed(int d,int q,const std::string& header,const std::string& cue,int noise){
    // TX-only debits in the last live window, followed by actual native
    // header/diagnostic and both early attempt queues.
    l.w.path_available=false;
    enqueue("P","sink",std::string(d,'p'));enqueue("Q","sink",std::string(q,'q'));event(5);
    l.w.path_available=true;
    enqueue("P","owed",header);enqueue("Q","diag",work);event(6);
    assert(delivered("owed","P")&&delivered("diag","Q"));
    assert(accepted.size()==2);
    const auto h=accepted.at(0).data;
    accepted.clear();
    enqueue("Q","owed","a");enqueue("P","owed",cue);if(noise)enqueue("Side","owed",std::string(noise,'n'));
    event(7);
    assert(accepted.size()==size_t(1+(noise!=0))&&delivered("owed","P")&&!delivered("owed","Q"));
    assert(Live::used(l.w.state("P").bytes_sent,7)==d+115);
    assert(Live::used(l.w.state("Q").bytes_sent,7)==q+5);
    const auto confirmation=accepted.at(0).data;
    accepted.clear();
    return {h,confirmation};
 }
};


std::string unhex(std::string s){
 if(s=="-")return {};
 assert(s.size()%2==0);
 std::string out;
 for(size_t i=0;i<s.size();i+=2)out.push_back(char(std::stoi(s.substr(i,2),nullptr,16)));
 return out;
}
std::string hex(const std::string& s){
 if(s.empty())return "-";
 const std::string chars="0123456789abcdef";
 std::string out;
 for(unsigned char c:s){out.push_back(chars[c>>4]);out.push_back(chars[c&15]);}
 return out;
}
int main(int argc,char** argv){
 assert(argc==2);
 int shape,d,q,noise,arm;
 std::string h,c,pframe,qframe,command;
 while(std::cin>>command){
   assert(command=="begin");
   assert(std::cin>>d>>q>>noise>>h>>c);
   Replay w(argv[1]);auto got=w.fixed(d,q,unhex(h),unhex(c),noise);
   std::cout<<hex(got.first)<<' '<<hex(got.second)<<std::endl;
   assert(std::cin>>command>>shape>>arm>>pframe>>qframe);
   assert(command=="commit");
   std::string ps=unhex(pframe),qs=unhex(qframe);
   assert(ps.empty()||ps.size()==164);
   assert(qs.empty()||qs.size()==164);
   std::string selected;
   auto& b=w.l.w.b;
   // Stock enqueue arm has both already-qualified immutable send requests.
   // Test arm chooses at the proposed local cut, after pose. Bytes came
   // from the app's checked snapshots, not from a route-oracle packet.
   if(arm==0){
     if(!ps.empty())w.enqueue("P","owed",ps);
     if(!qs.empty())w.enqueue("Q","owed",qs);
     w.enqueue("P","aux",w.work);
   }else{
     b.beforeDispatch=[&](){
       std::cout<<"cut "<<w.route("P",8)<<' '<<w.route("Q",8)<<' '
         <<Live::used(w.l.w.state("P").bytes_sent,8)<<' '
         <<Live::used(w.l.w.state("Q").bytes_sent,8)<<' '
         <<Live::used(w.l.w.state("Base").bytes_received,8)<<std::endl;
       std::string line;
       assert(std::cin>>line);
       if(line=="Q"){assert(!qs.empty());selected=line;w.enqueue("Q","owed",qs);}
       else if(line=="P"){assert(!ps.empty());selected=line;w.enqueue("P","owed",ps);}
       else assert(line=="-");
       w.enqueue("P","aux",w.work);
     };
   }
   w.event(8,shape);
   std::string who,payload;
   for(auto& a:w.accepted)if(a.tag=="owed"){
     assert(who.empty());who=a.from;payload=a.data;
   }
   auto used=[&](const auto& s){return Live::used(w.l.w.state(s).bytes_sent,8);};
   std::cout<<(selected.empty()?"-":selected)<<' '
        <<(who.empty()?"-":who)<<' '<<hex(payload)<<' '<<w.delivered("aux","P")<<' '
        <<used("P")<<' '<<used("Q")<<' '<<Live::used(w.l.w.state("Base").bytes_received,8)<<std::endl;
 }
}
