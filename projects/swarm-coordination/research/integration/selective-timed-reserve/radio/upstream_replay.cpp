#include <cassert>
#include <algorithm>
#include <cstdint>
#include <cmath>
#include <deque>
#include <functional>
#include <iostream>
#include <limits>
#include <map>
#include <memory>
#include <mutex>
#include <random>
#include <set>
#include <string>
#include <tuple>
#include <vector>

double now=0;
// Freeze the random-draw seam to avoid randomness in the boundary experiment.
// 500 is a possible native draw; high and erased endpoints are deterministic
// for any nonzero draw. No physical distribution is inferred from the mock.
int demo_draw(){return 500;}
#define ignmsg NullLog()
#define ignwarn NullLog()
struct NullLog {
 template<class T> NullLog& operator<<(const T&){return *this;}
 NullLog& operator<<(std::ostream& (*)(std::ostream&)){return *this;}
};
namespace ignition { namespace math {
struct Vector3d {
 int x=0; bool operator<(const Vector3d& b)const{return x<b.x;}
};}}
struct Pose {
 ignition::math::Vector3d p;
 auto Pos()const{return p;}
};
namespace subt { namespace msgs {
struct Datagram {
 std::string src,dst,value;
 unsigned port=7;
 double strength=4;
 const auto& src_address()const{return src;}
 const auto& dst_address()const{return dst;}
 const auto& data()const{return value;}
 auto dst_port()const{return port;}
 void set_rssi(double v){strength=v;}
};
}}
namespace subt_msgs {
struct DatagramRos {
 struct Request {std::string src_address,dst_address,data; unsigned dst_port; double rssi;};
 struct Response {};
};
}
namespace ros {
struct Time {static Time now(){return {};} double toSec()const{return ::now;}};
}
namespace rf_interface {
struct radio_state {
 Pose pose;
 double update_stamp=0;
 std::deque<std::pair<double,uint64_t>> bytes_sent,bytes_received;
 uint64_t bytes_sent_this_epoch=0,bytes_received_this_epoch=0;
};
}
struct Power{double mean,variance;};
struct radio_configuration{
 double capacity=0,default_tx_power=0,noise_floor=-100;std::string modulation="QPSK";
 std::function<Power(double,rf_interface::radio_state&,rf_interface::radio_state&,bool&)> pathloss_f;
};
namespace subt { namespace communication_model {
#define rand demo_draw
#include "radio.inc"
#undef rand
}}

struct Visibility {
 size_t rebuilds=0;
 std::set<ignition::math::Vector3d> points;
 void PopulateVisibilityInfo(const std::set<ignition::math::Vector3d>& p){points=p;++rebuilds;}
};
struct CommsBrokerPlugin{
 std::map<std::string,Pose> poses,breadcrumbs;
 std::unique_ptr<Visibility> visibilityModel=std::make_unique<Visibility>();
 void UpdateIfNewBreadcrumbs();
};
#include "drop.inc"
struct CommsClient{
 std::mutex mutex;
 std::map<std::string,std::pair<double,double>> neighbors;
 using Handler=std::function<void(std::string,std::string,unsigned,std::string)>;
 std::map<std::string,Handler> callbacks;
 bool OnMessageRos(subt_msgs::DatagramRos::Request&,subt_msgs::DatagramRos::Response&);
};
#include "ros-receipt.inc"
struct TeamNode {
 std::string name;
 radio_configuration radio;
 rf_interface::radio_state rf_state;
};
struct BrokerClientInfo{std::string address;};
struct Transport {
 CommsClient* receiver;
 bool Request(const std::string&,subt::msgs::Datagram msg){
  subt_msgs::DatagramRos::Request r{msg.src,msg.dst,msg.value,msg.port,msg.strength};
  subt_msgs::DatagramRos::Response res;
  return receiver->OnMessageRos(r,res);
 }
};
struct Broker {
 std::mutex mutex;
 std::map<std::string,std::vector<BrokerClientInfo>> endpoints;
 std::unique_ptr<std::map<std::string,std::shared_ptr<TeamNode>>> team=
    std::make_unique<std::map<std::string,std::shared_ptr<TeamNode>>>();
 std::function<decltype(subt::communication_model::attempt_send)> communication_function=subt::communication_model::attempt_send;
 std::function<std::tuple<bool,Pose,double>(const std::string&)> pose_update_f;
 std::deque<subt::msgs::Datagram> incomingMsgs;
 Transport node;
 void DispatchMessages();
};
#include "dispatch.inc"

struct World{
 CommsBrokerPlugin tracker;
 CommsClient app;
 Broker b;
 bool path_available=true, uses_breadcrumb=false;
 size_t recv=0;
 std::string carried_copy;
 World(unsigned limit){
  for(auto n:{"P","Q","Base"}){
   auto t=std::make_shared<TeamNode>();
   t->name=n;t->radio.capacity=8*limit;
   t->radio.pathloss_f=[this](double,auto&,auto&,bool& route){
      route=uses_breadcrumb;
      return Power{path_available?100.0:-std::numeric_limits<double>::infinity(),0};
   };
   (*b.team)[n]=t;
  }
  b.node.receiver=&app;
  app.callbacks["Base:7"]=[this](auto,auto,auto,auto v){if(v.size())++recv;};
  b.pose_update_f=[](auto){return std::make_tuple(true,Pose{},now);};
  app.callbacks["Q:7"]=[this](auto,auto,auto,auto v){carried_copy=v;};
  b.endpoints["Base:7"].push_back({"Base"});
  b.endpoints["Q:7"].push_back({"Q"});
 }
 auto& state(const std::string& id){return b.team->at(id)->rf_state;}
 bool send(const std::string& src,const std::string& dst,unsigned bytes,double at){
   now=at;
   auto before=recv;
   b.incomingMsgs.push_back({src,dst,std::string(bytes,'a')});
   b.DispatchMessages();
   assert(b.incomingMsgs.empty());
   return before!=recv;
 }
 void recover(){
   tracker.poses["P__breadcrumb__in_transit"]={{1}};
   tracker.UpdateIfNewBreadcrumbs();
   assert(tracker.visibilityModel->rebuilds==0);
   tracker.poses["P__breadcrumb__1__static__"]={{2}};
   tracker.UpdateIfNewBreadcrumbs();
   assert(tracker.visibilityModel->rebuilds==1 && tracker.visibilityModel->points.size()==1);
   path_available=true;uses_breadcrumb=true;
 }
};

struct Ref {
 unsigned limit; std::map<std::string,std::vector<std::pair<double,unsigned>>> tx,rx;
 static unsigned valid(const std::vector<std::pair<double,unsigned>>& xs,double at){
  unsigned n=0;
  for(const auto& [t,b]:xs)if(at-t<=1)n+=b;
  return n;
 }
 std::pair<bool,bool> send(const std::string& s,const std::string& d,unsigned bytes,double t,bool good){
  if(valid(tx[s],t)+bytes>limit)return {false,false};
  tx[s].emplace_back(t,bytes);
  if(!good||valid(rx[d],t)+bytes>limit)return {true,false};
  rx[d].emplace_back(t,bytes);
  return {true,true};
 }
};

int main(){
 size_t trials=0,attempts=0,hidden=0;
 // Every branch uses nonempty payloads and valid application endpoints.
 for(unsigned cap=3;cap<=9;++cap)
 for(unsigned a=1;a<=6;++a)
 for(unsigned b=1;b<=6;++b)
 for(unsigned c=1;c<=6;++c)
 for(bool failed:{false,true})
 for(bool alternate:{false,true})
 for(double cut:{0.25,0.50,1.0,1.25}){
   World w(cap);Ref oracle{cap,{},{}};
   auto check=[&](std::string s,unsigned bytes,double t,bool good,bool via){
     w.path_available=good;w.uses_breadcrumb=via;
     auto expect=oracle.send(s,"Base",bytes,t,good);
     const auto pass=w.send(s,"Base",bytes,t);
     assert(pass==expect.second);
     assert(w.state(s).bytes_sent_this_epoch==oracle.valid(oracle.tx[s],t));
     if(pass)assert(w.state("Base").bytes_received_this_epoch==oracle.valid(oracle.rx["Base"],t));
     ++attempts;return pass;
   };
   check("P",a,0,!failed,false);
   check("Q",b,.25,true,false);
   w.recover();
   auto before=w.app.neighbors;
   const auto success=check(alternate?"Q":"P",c,cut,true,true);
   assert(w.app.neighbors==before); // real ROS application receipt not neighbor refresh
   if(success)++hidden;
   ++trials;
 }
 std::cout<<"fixtures "<<trials<<" native attempts "<<attempts
          <<" successful final deliveries with no ROS neighbor update "<<hidden<<"\n";
 // Two opaque prehistories, both no delivery and same static relay cut.
 World spent(6),fresh(6),copy(6),receiver_busy(6);
 // The alternate sender actually obtains these bytes before the outage.
 assert(!copy.send("P","Q",3,-2.0)); // no Base delivery from this successful copy
 assert(copy.carried_copy==std::string(3,'a'));
 spent.path_available=copy.path_available=receiver_busy.path_available=false;
 assert(!spent.send("P","Base",4,0));
 assert(!copy.send("P","Base",4,0));
 assert(!receiver_busy.send("P","Base",4,0));
 assert(spent.recv==fresh.recv && spent.recv==0);
 spent.recover();fresh.recover();copy.recover();
 assert(!spent.send("P","Base",3,1.0));
 assert(fresh.send("P","Base",3,1.0));
 assert(copy.send("Q","Base",copy.carried_copy.size(),1.0)); // authorized app copy, distinct sender
 assert(spent.send("P","Base",3,1.25));
 assert(spent.app.neighbors.empty() && fresh.app.neighbors.empty());
 receiver_busy.path_available=true;
 // R receives six good bytes at .25 from a separate participant, hiding no source-history oracle.
 auto third=std::make_shared<TeamNode>(*receiver_busy.b.team->at("Q"));
 third->name="Other";receiver_busy.b.team->emplace("Other",third);
 assert(receiver_busy.send("Other","Base",6,.25));
 receiver_busy.recover();
 assert(!receiver_busy.send("Q","Base",3,1.0));
 assert(receiver_busy.state("Q").bytes_sent_this_epoch==3);
 // Native transfer still counts toward sender even if the destination budget rejects later.
 assert(!receiver_busy.send("Q","Base",4,1.5));
 assert(receiver_busy.send("Q","Base",4,2.25));
 {
  // Equal current debits at the cut, unequal expiry at the service deadline.
  World old(6),recent(6);
  old.path_available=recent.path_available=false;
  assert(!old.send("P","Base",4,0.0));
  assert(!recent.send("P","Base",4,0.25));
  assert(old.state("P").bytes_sent_this_epoch==recent.state("P").bytes_sent_this_epoch);
  old.recover();recent.recover();
  assert(old.send("P","Base",3,1.25));
  assert(!recent.send("P","Base",3,1.25));
 }
 std::cout<<"same drop, earlier failed attempt misses t=1; no attempt or a separate sender delivers\n";
 std::cout<<"old receive debit can defeat a separate sender; equal debit totals hide different expiry; age=1 is inclusive\n";
}
