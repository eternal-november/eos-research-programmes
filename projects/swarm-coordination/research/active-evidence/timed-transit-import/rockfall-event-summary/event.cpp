#include <algorithm>
#include <chrono>
#include <iostream>
#include <map>
#include <mutex>
#include <set>
#include <sstream>
#include <string>
#include <vector>
#include <cassert>
struct Silent {
  template<class T> Silent& operator<<(const T&) {return *this;}
  Silent& operator<<(std::ostream& (*)(std::ostream&)){return *this;}
};
#define ignmsg Silent()
#define ignwarn Silent()
namespace ignition { namespace msgs {
struct Time {int s;int sec()const{return s;}};
struct Int32 {int n=0; void set_data(int a){n=a;}int data()const{return n;}};
struct StringMsg {void set_data(const std::string&){}};
struct Boolean {};
}}
using namespace ignition;
namespace transport {struct MessageInfo {
  std::string path; const std::string& Topic()const{return path;}
};}
namespace common {
std::vector<std::string> split(const std::string& a,const std::string&) {
  std::istringstream s(a);std::string piece;std::vector<std::string> r;
  while(std::getline(s,piece,'/')) if(!piece.empty())r.push_back(piece);
  return r;
}
}
struct GameLogicPluginPrivate {
  int eventCounter=0;
  ignition::msgs::Time simTime{0};
  std::map<std::string,std::pair<int,int>> rockFallsMax;
  std::mutex eventCounterMutex;
  std::vector<std::string> logs;
  std::vector<int> region;
  void OnRockFallDeployRemainingEvent(const ignition::msgs::Int32&,const transport::MessageInfo&);
  void LogEvent(const std::string& s){logs.push_back(s);}
  void PublishRegionEvent(const msgs::Time&,const std::string&,const std::string& performer,
                          const std::string&,const std::string&,int id){
    assert(performer.empty());
    region.push_back(id);
  }
};
#include "logs.inc"

using Entity=int;
struct SourceDetector {
  std::set<Entity> state;
  std::vector<int> published;
  void AddToDetected(Entity e){state.insert(e);}
  void RemoveFromDetected(Entity e){state.erase(e);}
  void Publish(Entity,const std::string&,bool b,int,int){published.push_back(b);}
  void step(Entity _entity,bool inside){
    struct {bool v; bool Intersects(int)const{return v;}} region{inside};
    const int performerVolume=0,relPose=0;
    struct {int simTime=0;} _info;
    const std::string name="sampled performer";
    const bool alreadyDetected=state.count(_entity);
    #include "detector.inc"
  }
};
struct Pose {
  Pose operator*(const Pose&)const{return {};}
  friend std::ostream& operator<<(std::ostream& o,const Pose&){return o;}
};
namespace sdf {struct Model {
  std::string name="Rock";
  const std::string& Name()const{return name;}
  Pose RawPose()const{return {};}
  void SetRawPose(Pose){}
  void SetName(const std::string& n){name=n;}
  bool Static()const{return false;}
};}
namespace components {
struct Model{};
struct Name{ std::string Data()const{return "world";} };
}
struct MockECM {
  template<class A,class B,class F>void Each(F){}
  template<class A>A* Component(Entity){static A x;return &x;}
};
struct MockCreator {
  std::vector<std::string> spawns;
  Entity CreateEntities(const sdf::Model* m){spawns.push_back(m->Name());return spawns.size();}
  void SetParent(Entity,Entity){}
};
struct Breadcrumbs {
  int maxDeployments=0,numDeployments=0,worldEntity=0;
  bool allowRenaming=false,isPerformer=false;
  MockCreator c;
  MockCreator* creator=&c;
  struct {sdf::Model m; const sdf::Model* ModelByIndex(int)const{return &m;}} modelRoot;
  std::chrono::steady_clock::duration disablePhysicsTime{};
  std::map<Entity,std::chrono::steady_clock::duration> autoStaticEntities;
  struct Node{template<class A,class B,class C>void Request(const std::string&,A,C){assert(false);}} node;
  std::set<Entity> pendingGeometryUpdate;
  struct Pub {std::vector<int> values;void Publish(msgs::Int32 x){values.push_back(x.data());}} remainingPub;
  void tick(int count){
    std::vector<bool> cmds(count,true);
    MockECM _ecm;
    struct {std::chrono::steady_clock::duration simTime{};} _info;
    struct {Pose Data()const{return {};}} pose;
    auto* poseComp=&pose;
    #include "deploy.inc"
  }
};
int main(){
  std::string kind;
  while(std::cin>>kind){
    if(kind=="detect"){
      int n;std::cin>>n;SourceDetector d;
      for(int i=0;i<n;i++){int id;bool inside;std::cin>>id>>inside;d.step(id,inside);}
      for(int b:d.published)std::cout<<b;
      std::cout<<'\n'<<std::flush;
    }else if(kind=="log"){
      int n;Breadcrumbs d;std::cin>>d.maxDeployments>>n;
      GameLogicPluginPrivate l;
      for(int i=0;i<n;i++){
        int sec,count;std::cin>>sec>>count;l.simTime.s=sec;
        auto mark=d.remainingPub.values.size();
        d.tick(count);
        for(size_t j=mark;j<d.remainingPub.values.size();j++){
          l.OnRockFallDeployRemainingEvent({d.remainingPub.values[j]},
                 {"/model/dynamic_rocks_1/breadcrumbs/Rock/deploy/remaining"});
        }
      }
      std::cout<<d.c.spawns.size()<<' '<<d.maxDeployments-d.numDeployments<<' '<<l.region.size()<<' ';
      for(const auto& s:l.logs){
        const auto i=s.find("  type: "); assert(i!=std::string::npos);
        auto j=s.find('\n',i);std::cout<<s.substr(i+8,j-(i+8))<<',';
      }
      std::cout<<'\n'<<std::flush;
    }else assert(false);
  }
}
