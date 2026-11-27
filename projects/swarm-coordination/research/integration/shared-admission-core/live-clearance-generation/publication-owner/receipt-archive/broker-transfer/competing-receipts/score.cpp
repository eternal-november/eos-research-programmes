
#include <cassert>
#include <cmath>
#include <chrono>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <mutex>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <vector>
namespace ignition {
namespace math {
struct Vector3d {
 double x=0,y=0,z=0;
 double X()const{return x;} double Y()const{return y;} double Z()const{return z;}
 double Distance(const Vector3d &b)const{return std::sqrt((x-b.x)*(x-b.x)+(y-b.y)*(y-b.y)+(z-b.z)*(z-b.z));}
 friend std::ostream& operator<<(std::ostream& o,const Vector3d& a){
  return o << std::round(a.x*1e6)/1e6 << " " << std::round(a.y*1e6)/1e6 << " " << std::round(a.z*1e6)/1e6;
 }
};
struct Pose3d {
 Vector3d v;
 auto Pos() const{return v;}
 Pose3d operator+(const Pose3d& o)const{return {{v.x+o.v.x,v.y+o.v.y,v.z+o.v.z}};}
 Pose3d operator-(const Pose3d& o)const{return {{v.x-o.v.x,v.y-o.v.y,v.z-o.v.z}};}
};
}
namespace msgs{
struct Time {
 int s=0,n=0;
 int sec()const{return s;} int nsec()const{return n;}
 void set_sec(int64_t v){s=v;} void set_nsec(int64_t v){n=v;}
};
struct Pose{
 struct Position{
 double a,b,c; double x()const{return a;} double y()const{return b;} double z()const{return c;}
 } p;
 const Position& position()const{return p;}
};
inline math::Pose3d Convert(const Pose& p){return {{p.p.a,p.p.b,p.p.c}};}
}
}
namespace subt::msgs{
struct Artifact{
 int kind=1;ignition::msgs::Pose p;
 int type()const{return kind;}
 const auto& pose()const{return p;}
 std::string DebugString()const{return "fixture payload";}
};
struct ArtifactScore{
 Artifact echo;ignition::msgs::Time dt,sim;
 double delta=0;unsigned count=0,run=0;std::string status;
 Artifact* mutable_artifact(){return &echo;}
 auto* mutable_submitted_datetime(){return &dt;}
 auto* mutable_sim_time(){return &sim;}
 void set_run(unsigned a){run=a;} void set_score_change(double a){delta=a;}
 void set_report_status(const std::string& s){status=s;} void set_report_id(unsigned n){count=n;}
};
}
namespace subt_ros{
struct ArtifactReport{
 struct{int sec,nsec;} timestamp;struct{double x,y,z;} reported_artifact_position;
 double points_scored=0,total_score=0,distance=0;
 std::string reported_artifact_type,closest_artifact_name;
};
}
enum class ArtifactType{inspection};
bool ArtifactFromInt(int x,ArtifactType& t){t=ArtifactType::inspection;return x==1;}
bool StringFromArtifact(ArtifactType,std::string& s){s="inspection";return true;}
std::ostringstream sink;
#define ignmsg sink
#define ignerr sink
const std::vector<int> kArtifactTypes{1};

struct GameLogicPluginPrivate{
 unsigned reportCount=0,duplicateReportCount=0,reportCountLimit=2,artifactCount=4,eventCounter=0;
 double totalScore=0,firstReportTime=-1,lastReportTime=-1;
 bool started=true,finished=false,rosnode=false;
 struct{void publish(const subt_ros::ArtifactReport&){} } rosArtifactPub;
 std::mutex mutex,eventCounterMutex;
 ignition::msgs::Time simTime;
 ignition::math::Pose3d artifactOriginPose;
 std::set<std::string> foundArtifacts;
 std::map<ArtifactType,std::map<std::string,ignition::math::Pose3d>> artifacts;
 std::map<std::string,double> uniqueReports;
 std::tuple<std::string,std::string,ignition::math::Vector3d,ignition::math::Vector3d,double> closestReport{"","",{},{},-1};
 std::vector<std::string> events;
 auto& Log(const ignition::msgs::Time&){return sink;}
 void LogEvent(const std::string& e){events.push_back(e);}
 void Finish(const ignition::msgs::Time&){finished=true;}
 void UpdateScoreFiles(const ignition::msgs::Time&){}
 bool OnNewArtifact(const subt::msgs::Artifact&,subt::msgs::ArtifactScore&);
 ignition::math::Pose3d ConvertToArtifactOrigin(const ignition::math::Pose3d&) const;
 std::tuple<double,bool> ScoreArtifact(const ignition::msgs::Time&,const ArtifactType&,const ignition::msgs::Pose&,subt_ros::ArtifactReport&);
};
#include "score.inc"
using Report=subt::msgs::Artifact;
using Result=subt::msgs::ArtifactScore;
Report point(double x,double y=100,double z=100){return {1,{{x,y,z}}};}
void init(GameLogicPluginPrivate& g,int limit){
 g.reportCountLimit=limit;
 g.artifacts[ArtifactType::inspection]={{"r",{{100,100,100}}},{"s",{{120,100,100}}},{"x",{{140,100,100}}},{"w",{{160,100,100}}}};
}
Result send(GameLogicPluginPrivate& g,Report r,int tick){
 g.simTime.s=tick;Result out;assert(g.OnNewArtifact(r,out));return out;
}

int live_session(bool exact,bool late){
 GameLogicPluginPrivate g;init(g,late?3:2);
 const Report sought=point(100+1.0/524288);
 const Report observed=point(late?140:(exact?100+1.0/524288:100-1.0/524288));
 const auto key=[](const Report& r){return "inspection_"+std::to_string(r.pose().position().x())+"_100.000000_100.000000";};
 const auto seen=send(g,observed,0);
 assert(seen.delta==1 && seen.status=="scored" && g.totalScore==1);
 assert(key(seen.echo)==key(observed));
 const bool present=g.uniqueReports.count(key(sought));
 assert(present==(exact&&!late));
 if(present){assert(key(seen.echo)==key(sought));assert(g.uniqueReports.at(key(sought))==seen.delta);}
 // Authored producer-local capture at a serial cut after native return.
 std::cout<<"{\"key\":\""<<key(sought)<<"\",\"present\":"<<present<<",\"delta\":"<<(present?seen.delta:0)
          <<",\"epoch\":7,\"at\":1}"<<std::endl;
 std::string cmd;
 assert(std::getline(std::cin,cmd)&&cmd=="next");
 // If enabled, the still-authorized original can arrive after an absence read.
 if(late)send(g,sought,2);
 auto other=send(g,point(120),3);
 assert(g.finished);
 const auto old=send(g,sought,4);
 std::cout<<"{\"other_delta\":"<<other.delta<<",\"other_status\":\""<<other.status
          <<"\",\"closed_status\":\""<<old.status<<"\",\"closed_score\":"<<old.delta
          <<",\"end_present\":"<<g.uniqueReports.count(key(sought))<<"}"<<std::endl;
 return 0;
}

int two_session(bool relevantA,bool relevantB){
 GameLogicPluginPrivate g;init(g,3);
 const auto key=[](const Report&r){
  return "inspection_"+std::to_string(r.pose().position().x())+"_100.000000_100.000000";
 };
 auto archive=[&](Report req,Report accepted,int tick){
  auto out=send(g,accepted,tick);
  assert(out.delta==1&&out.status=="scored"&&key(out.echo)==key(accepted));
  assert(g.uniqueReports.at(key(accepted))==1);
  bool exact=key(out.echo)==key(req);
  assert((g.uniqueReports.count(key(req))==1)==exact);
  return exact;
 };
 const Report a=point(100+1.0/524288),b=point(120);
 const bool A=archive(a,relevantA?a:point(100-1.0/524288),-2);
 const bool B=archive(b,relevantB?b:point(120+1.0/524288),-1);
 std::cout<<"{\"A\":"<<A<<",\"B\":"<<B<<",\"A_key\":\""<<key(a)<<"\",\"B_key\":\""<<key(b)
          <<"\",\"score\":"<<g.totalScore<<"}"<<std::endl;
 std::string cmd;assert(std::getline(std::cin,cmd)&&cmd=="next");
 auto x=send(g,point(160),3);
 assert(x.delta==1&&g.finished);
 auto aa=send(g,a,4),bb=send(g,b,4);
 assert(aa.status=="scoring finished"&&aa.status==bb.status&&aa.delta==0&&bb.delta==0);
 std::cout<<"{\"closed\":1,\"independent\":"<<x.delta<<"}"<<std::endl;
 return 0;
}

int main(int argc,char** argv){
 if(argc==4&&std::string(argv[1])=="two")return two_session(std::string(argv[2])=="exact",std::string(argv[3])=="exact");
 if(argc>1){assert(argc==3);return live_session(std::string(argv[1])=="exact",std::string(argv[2])=="late");}

 {
  GameLogicPluginPrivate g;init(g,3);
  auto a=send(g,point(100),0),b=send(g,point(120),1),c=send(g,point(100),2);
  assert(a.delta==1&&b.delta==1&&c.delta==1&&a.count==1&&c.count==2&&g.totalScore==2);
  assert(c.status=="scored"&&g.duplicateReportCount==1);
 }
 int pairs=0;
 for(int lim:{2,3})for(bool useRoundedAlias:{false,true}){
  GameLogicPluginPrivate a,b;init(a,lim);init(b,lim);
  Report r=point(useRoundedAlias?100+1.0/524288:100);
  Report other=point(useRoundedAlias?100-1.0/524288:140);
  auto old=send(a,r,0);auto alias=send(b,other,0);
  assert(old.status=="scored"&&alias.status=="scored"&&a.totalScore==b.totalScore);
  if(useRoundedAlias)assert(a.events==b.events);
  send(a,point(120),1);send(b,point(120),1);
  if(lim==3){send(a,point(160),2);send(b,point(160),2);}
  auto q=send(a,r,3),w=send(b,r,3);
  assert(q.status=="scoring finished"&&w.status==q.status&&q.delta==0&&w.delta==0&&q.count==w.count);
  assert(a.uniqueReports.count("inspection_"+std::to_string(r.pose().position().x())+"_100.000000_100.000000")==1);
  assert(b.uniqueReports.count("inspection_"+std::to_string(r.pose().position().x())+"_100.000000_100.000000")==0);
  std::cout<<"{\"cap\":"<<lim<<",\"alias\":"<<useRoundedAlias<<",\"closed_count\":"<<q.count
    <<",\"prior_score\":"<<old.delta<<",\"side_score\":"<<a.totalScore-old.delta<<"}\n";
  ++pairs;
 }
 assert(pairs==4);
}
