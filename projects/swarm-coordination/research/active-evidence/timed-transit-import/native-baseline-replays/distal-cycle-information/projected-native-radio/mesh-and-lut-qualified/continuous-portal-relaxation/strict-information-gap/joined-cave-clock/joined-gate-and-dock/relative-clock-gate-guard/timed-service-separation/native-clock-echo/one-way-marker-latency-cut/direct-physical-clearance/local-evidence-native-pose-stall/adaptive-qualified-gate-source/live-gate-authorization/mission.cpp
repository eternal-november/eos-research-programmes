#include <array>
#include <fstream>
#define main inherited_cave_test
#include "staged_replay.inc"
#undef main

struct Scene{
   using S=std::size_t;
   std::vector<uint64_t> id;
   std::vector<Point> xyz;
   std::vector<std::vector<int>> D;
   std::array<std::array<std::string,2>,2> beam;
   std::array<std::vector<S>,2> path;
 std::array<S,2> routeRequiringGate;
   explicit Scene(const char* name){
     std::ifstream f(name);
     S n;assert(f>>n);
     id.resize(n);xyz.resize(n);D.resize(n);
     for(S i=0;i<n;++i)assert(f>>id[i]>>xyz[i].x>>xyz[i].y>>xyz[i].z);
     for(auto& r:D){r.resize(n);for(auto& v:r)assert(f>>v);}
     for(auto& r:beam)for(auto& v:r)assert(f>>v);
     for(auto& r:path){S n;assert(f>>n);r.resize(n);for(auto& p:r)assert(f>>p);}
     for(auto& route:routeRequiringGate)assert((f>>route)&&route<2);
     assert(routeRequiringGate[0]!=routeRequiringGate[1]);
   }
};

struct Radio {
 const Scene& s;
 World w;
 std::map<std::string,size_t> where{{"P",1},{"Q",2},{"Base",0}};
 std::map<std::string,Point> placement;
 Radio(const Scene& s,unsigned cap):s(s),w(cap){
   auto& tr=w.tracker;
   auto& m=*tr.visibilityModel;
   auto& tab=m.visibilityTable;
   m.defaultRangeConfig.max_range=72.;
   m.defaultRangeConfig.scaling_factor=.55;
   for(size_t i=0;i<s.id.size();++i){
     const auto p=s.xyz[i];auto a=s.id[i];
     tab.vertices.emplace(std::make_tuple(int32_t(p.x),int32_t(p.y),int32_t(p.z)),a);
     tab.visibilityGraph.vertices.emplace(a,0);
     for(size_t j=0;j<s.id.size();++j)
       tab.visibilityGraph.projected[a][s.id[j]]={double(s.D[i][j]),0};
   }
   tab.PopulateVisibilityInfo();
   for(size_t i:{3,4,5})
     tr.poses["helper__breadcrumb__"+std::to_string(i)+"__static__"]=Pose{s.xyz[i]};
   tr.UpdateIfNewBreadcrumbs();
   assert(m.rebuilds==1);
   w.b.pose_update_f=[&](auto name){
     const auto it=placement.find(name);
     return std::make_tuple(true,Pose{it==placement.end()?s.xyz.at(where.at(name)):it->second},now);
   };
   setup("P"); setup("Q"); setup("Base");
   add("R",0); add("D1",3); add("D2",4); add("Audit",5);
 }
 void setup(const std::string& name){
   auto& cfg=w.b.team->at(name)->radio;
   cfg.default_tx_power=80;
   cfg.pathloss_f=[&](double tx,auto& a,auto& b,bool& relay){
     return w.tracker.visibilityModel->ComputeReceivedPower(tx,a,b,relay);
   };
 }
 void add(const std::string& name,size_t site){
   auto node=std::make_shared<TeamNode>(*w.b.team->at("Base"));
   node->name=name;
   w.b.team->emplace(name,node);
   w.b.endpoints[name+":7"].push_back({name});
   where[name]=site; setup(name);
 }
 bool poseLost=false;
 std::string route(const std::string& a,const std::string& b,const std::string& bytes,double at,double take=-1){
   std::string out;
   const auto key=b+":7";
   w.app.callbacks[key]=[&](auto src,auto,auto,auto data){
      assert(src==a&&out.empty());out=data;
   };
   assert(w.b.incomingMsgs.empty());
   assert(take<0||take<=at);
   now=take<0?at:take;
   w.b.incomingMsgs.push_back({a,b,bytes});
   now=at;
   w.b.DispatchMessages();
   w.app.callbacks.erase(key);
   if(poseLost){assert(w.b.incomingMsgs.size()==1);w.b.incomingMsgs.clear();}
   else assert(w.b.incomingMsgs.empty());
   return out;
 }
};

long long bound_leg(const Point& p,const Point& q){
 // Coordinates are integer metres. Never round the positive ascent below
 // its Euclidean time. A check bounds the double candidate exactly.
 const long long x=p.x-q.x,y=p.y-q.y,z=p.z-q.z;
 const long long n=(x*x+y*y+z*z)*1000000000000LL;
 auto h=(long long)std::sqrt((long double)n);
 while(h*h<n)++h;
 while((h-1)*(h-1)>=n)--h;
 assert(n>=40000000000LL);
 return h+200000;
}
double secs(long long us){return us/1.e6;}
std::string readframe(){
 std::string x;assert(std::cin>>x);assert(x=="-"||x.size()==5);
 return x;
}

int main(int argc,char** argv){
 assert(argc==5);Scene s(argv[1]);
 const int world=std::stoi(argv[2]); const int rewind=std::stoi(argv[3]);
 const unsigned cap=std::stoi(argv[4]);
 Radio r(s,cap);
 int cue=-1;
 for(int i:{0,1}){
   // Bounded family includes loss of either staged physical observer.
   if(i==(rewind>>2))continue;
   const auto packet=r.route(i?"Q":"P","Base",s.beam[world][i],.75+.25*i);
   if(!packet.empty()){
      assert(packet=="c"||packet=="o");
      const auto decoded=packet=="c"?i:1-i;
      assert(cue<0||cue==decoded);cue=decoded;
   }
 }
 assert(cue==world);
 // Cue is a *closed physical gate*, not a certified route label.
 const auto selected=s.routeRequiringGate.at(1-cue);
 assert(selected!=s.routeRequiringGate.at(world));
 auto& p=s.path.at(selected);
 std::cout<<"schedule "<<selected<<std::endl;

 long long maintenance,actuation,witness,sample,repair;
 int err,bias,axis,sign,body,source;
 double plane;
 assert(std::cin>>maintenance>>actuation>>witness>>err>>bias>>axis>>sign>>body>>plane>>source>>sample>>repair);
 assert(maintenance<witness&&witness<actuation&&abs(bias)<=err);
 const std::string gate=selected==0?"P":"Q";
 r.w.b.endpoints["P:7"].push_back({"P"});
 auto plant=[&](const char* label,long long at,int chord){
    std::cout<<label<<" "<<at<<" "<<chord<<std::endl;
    std::string answer;assert(std::cin>>answer);
    assert(answer=="ok"||answer=="contact");
    return answer=="ok";
 };
 long long t=1000000;
 for(size_t i=1;i<p.size();++i){
   const auto stop=t+bound_leg(s.xyz[p[i-1]],s.xyz[p[i]]);
   if(t<maintenance&&maintenance<=stop)assert(plant("maintenance",maintenance,i-1));
   t=stop;
   r.where["R"]=p[i];
 }
 assert(r.where.at("R")==p.back());
 // Exact named simulator inspection output is read from the reached pose.
 const auto g=s.xyz[r.where.at("R")];
 assert(g.x==350&&g.y==-300&&g.z==13);
 const std::string report="I"+std::to_string((int)g.x)+std::to_string((int)g.z%10);
 assert(report.size()==5);
 std::cout<<"inspection "<<report<<" "<<t<<std::endl;
 // Counterfactual: the same report is not delivered from the inspection
 // stop, even without rolling contention. Separate run, no hidden RF query.
 Radio at_goal(s,cap);
 at_goal.where["R"]=p.back();
 assert(at_goal.route("R","D1",report,secs(t)).empty());
 assert(at_goal.route("R","D2",report,secs(t+1125000)).empty());
 // Use a named, previously chosen rest stop, not a look-ahead RF oracle.
 auto idx=selected==0?4:5;
 for(int i=int(p.size())-1;i>idx;--i){
    const auto stop=t+bound_leg(s.xyz[p[i]],s.xyz[p[i-1]]);
    if(t<actuation&&actuation<=stop){
       assert(i-1==idx&&t<witness);
       const auto u=s.xyz[p[i]],v=s.xyz[p[i-1]];
       auto pose=[&](long long q){
          const double m=(q-t-100000)/1000000.;
          const double length=u.Distance(v);
          assert(m>=0&&m<=length-.1);
          const double f=m/length;
          return Point{u.x+f*(v.x-u.x),u.y+f*(v.y-u.y),u.z+f*(v.z-u.z)};
       };
       auto observed=[&](long long q){
          const auto at=pose(q);
          const std::array<double,3> pos{{at.x,at.y,at.z}};
          return sign*(pos.at(axis)-plane)+bias/1000000.;
       };
       const double threshold=(body?.302:0)+err/1000000.;
       assert(observed(witness)>threshold&&observed(witness-1)<=threshold);
       // Site-bound registration not sending/receiving either job.
       // It nevertheless participates in the native broker's global
       // pose-update pass. Its disappearance leaves actual FIFO entries.
       const long long first=witness+10000;
       assert(first<repair&&repair<=stop);
       r.add("AuxX",0);
       auto pose_update=r.w.b.pose_update_f;
       r.w.b.pose_update_f=[&](auto name){
          if(name=="AuxX")return std::make_tuple(false,Pose{},now);
          return pose_update(name);
       };
       const std::string clearance{'C',char(7),char('0'+selected)};
       std::string rec,diag;
       r.w.app.callbacks[gate+":7"]=[&](const auto& src,auto,auto,const auto& data){assert(src=="R"&&rec.empty());rec=data;};
       r.w.app.callbacks["Base:7"]=[&](const auto& src,auto,auto,const auto& data){assert(src==gate&&diag.empty());diag=data;};
       now=secs(witness);r.w.b.incomingMsgs.push_back({"R",gate,clearance});
       if(source==1)assert(observed(sample)>threshold&&sample==first&&sample<actuation);
       else assert(source==0);
       now=secs(first);r.w.b.incomingMsgs.push_back({gate,"Base","Y"});
       r.placement["R"]=pose(first);
       r.w.b.DispatchMessages();
       assert(r.w.b.incomingMsgs.size()==2);
       assert(rec.empty()&&diag.empty()&&!r.w.state("R").bytes_sent_this_epoch);
       const auto remove_and_dispatch=[&]{
           now=secs(repair);
           assert(r.w.b.Unregister("AuxX"));
           r.w.b.pose_update_f=pose_update; // End the temporary probe scope.
           r.placement["R"]=pose(repair);
           // During the local-mode gate effect the pending diagnostic
           // uses only the outside station, observer, and three fixed
           // repeaters. Their entire convex hull is outside that slab.
           for(auto j:{size_t(0),r.where.at(gate),size_t(3),size_t(4),size_t(5)}){
              const auto v=s.xyz.at(j);
              const std::array<double,3> point{{v.x,v.y,v.z}};
              assert(sign*(point.at(axis)-plane)>0);
           }
           const auto actual=r.placement.at("R");
           const std::array<double,3> point{{actual.x,actual.y,actual.z}};
           assert(sign*(point.at(axis)-plane)>.302);
           r.w.b.DispatchMessages();
           assert(r.w.b.incomingMsgs.empty()&&diag=="Y"&&rec==clearance);
       };
       if(source==0){
          assert(actuation==repair);
          remove_and_dispatch();
       }else{
          assert(actuation<repair&&rec.empty()&&diag.empty());
       }
       std::cout<<"clearance 1 "<<(diag=="Y")<<" "<<witness<<std::endl;
       assert(plant("actuation",actuation,i-1));
       if(source==1) {
          remove_and_dispatch();
          assert(plant("late_clearance",repair,i-1));
       }
       assert(diag=="Y");
       assert(r.w.state(gate).bytes_received_this_epoch==3);
       assert(r.w.state("R").bytes_sent_this_epoch==3);
       std::cout<<"repaired "<<repair<<" "<<diag<<std::endl;
       r.w.app.callbacks.erase(gate+":7");r.w.app.callbacks.erase("Base:7");
       r.placement.erase("R");
    }
    t=stop;
    r.where["R"]=p[i-1];
 }
 assert(r.where["R"]==p[idx]);
 // Round up to a binary-exact native clock cut; carried as explicit wait.
 t=((t+124999)/125000)*125000;
 const auto smp=s.xyz[p[idx]];
 const auto one=[&](int offset){return std::string(1,char('a'+((int)smp.x+offset)%26));};
 // Full native RX delivery at the selected stop, before egress.
 auto aux1=r.route("R","Audit",one(0),secs(t));
 auto data1=r.route("R","D1",report,secs(t));
 std::cout<<"primary "<<(aux1.empty()?"-":aux1)<<" "
   <<(data1.empty()?"-":data1)<<" "<<t<<std::endl;
 auto reply1=readframe();assert(reply1=="-");
 if((rewind&3)>=2){
    r.poseLost=(rewind&3)==2;
    r.w.b.pose_update_f=[&](auto name){
       return std::make_tuple(name!="D1",Pose{s.xyz.at(r.where.at(name))},now);
    };
    if(!r.poseLost){
       assert(r.w.b.Unregister("D1"));
       assert(r.w.b.endpoints.at("D1:7").empty());
    }
 }
 // Native rolling window expires strictly after one second.
 const long long step=(rewind&3)==1?1000000:1125000;
 const auto data2=r.route("R","D2",report,secs(t+step));
 std::cout<<"backup "<<(data2.empty()?"-":data2)<<" "<<t+step<<std::endl;
 const auto reply2=readframe();
 std::string ack;
 if(reply2!="-")ack=r.route("D2","R",reply2,secs(t+step+125000));
 auto aux2=r.route("R","Audit",one(1),secs(t+step+125000));
 const auto courierTx=r.w.state("R").bytes_sent_this_epoch;
 t+=step+125000;
 for(int i=idx;i>0;--i){
    t+=bound_leg(s.xyz[p[i]],s.xyz[p[i-1]]);
    r.where["R"]=p[i-1];
 }
 assert(r.where.at("R")==0);
 std::cout<<"return "<<(ack.empty()?"-":ack)<<" "
   <<(aux2.empty()?"-":aux2)<<" "<<t<<" "<<courierTx<<std::endl;
}
