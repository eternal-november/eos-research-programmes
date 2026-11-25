#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#define RCLCPP_INFO(...) ((void)0)
#define RCLCPP_WARN(...) ((void)0)
#define RCLCPP_DEBUG(...) ((void)0)
namespace rclcpp {
using Time = std::chrono::time_point<std::chrono::steady_clock, std::chrono::seconds>;
using Duration = std::chrono::seconds;
}
using Time = rclcpp::Time;
namespace rmf_reservation_msgs::msg {
struct ReleaseRequest {
  struct { uint64_t ticket_id; struct {std::string fleet_name, robot_name, request_id;} header;} ticket;
  std::string location;
};
}
namespace rmf_zone_msgs::msg {
struct ZoneRequest {
  using SharedPtr = std::shared_ptr<ZoneRequest>;
  std::string released_waypoint, zone_name="Z", fleet_name="F", robot_name="r";
};
}
struct Publisher {
  std::vector<std::pair<uint64_t,std::string>> releases;
  void publish(const rmf_reservation_msgs::msg::ReleaseRequest& msg) {
    releases.emplace_back(msg.ticket.ticket_id, msg.location);
  }
};
class Node;
class ZoneReservationClient {
public:
  enum class HandbackDisposal {Reclaim, Freeze};
  struct Holding {
    enum class State {Requested, Held, Transferred, Frozen};
    using RobotId=std::pair<std::string,std::string>;
    std::string zone, request_id;
    State state;
    std::optional<RobotId> transferred_to;
    std::optional<uint64_t> ticket_id;
  };
  struct ZonePoolRelease { int released=0, dropped_claims=0; };
  std::string _robot_name="pool", _fleet_name="pool";
  std::weak_ptr<Node> _node;
  std::shared_ptr<Publisher> _release_pub=std::make_shared<Publisher>();
  std::unordered_map<std::string,std::shared_ptr<Holding>> _holdings;
  std::shared_ptr<Holding> _find(const std::string& z, const std::string& v) {
    auto i = _holdings.find(v); if(i == _holdings.end() || i->second->zone != z) return {};
    return i->second;
  }
  std::shared_ptr<const Holding> _find(const std::string& z, const std::string& v) const {
    auto i = _holdings.find(v); if(i == _holdings.end() || i->second->zone != z) return {};
    return i->second;
  }
  bool is_available(const std::string&, const std::string&) const;
  bool transfer(const std::string&, const std::string&, const std::string&, const std::string&);
  bool confirm_handback(const std::string&,const std::string&,const std::string&,const std::string&,HandbackDisposal);
  void _disown(const std::string&);
  bool release(const std::string&,const std::string&);
  ZonePoolRelease release_zone(const std::string&);
  bool has_holdings(const std::string&) const;
  std::vector<std::string> transferred_vertices(const std::string&) const;
  std::unordered_set<std::string> zones_with_holdings() const;
};
class Node {
public:
  struct Log {std::string zone_name, fleet_name, robot_name; bool arrived;};
  std::unordered_map<std::string,Log> _zone_log;
  std::unordered_map<std::string,std::vector<std::string>> _pending_entries;
  std::unordered_map<std::string,Time> _zone_idle_since;
  std::chrono::seconds _zone_pool_idle_timeout{30};
  std::shared_ptr<ZoneReservationClient> _reservation_client;
  Time time{};
  Time now() const { return time; }
  auto _find_booking_for(const std::string& r,const std::string& f,const std::string& z) {
    for(auto i=_zone_log.begin();i!=_zone_log.end();++i)
      if (i->second.robot_name==r && i->second.fleet_name==f && i->second.zone_name==z) return i;
    return _zone_log.end();
  }
  // No pending request processed by the callbacks in the named witnesses.
  void _drop_pending_entry(const std::string& r,const std::string&,const std::string& z) {
    for(auto& p:_pending_entries[z]) if(p==r) std::abort();
  }
  void _retry_pending_entries(const std::string& z) {
    if (!_pending_entries[z].empty()) std::abort();
  }
  void _publish_state() {}
  void _process_arrived(const rmf_zone_msgs::msg::ZoneRequest::SharedPtr);
  void _process_handback(const rmf_zone_msgs::msg::ZoneRequest::SharedPtr);
  void _process_exit(const rmf_zone_msgs::msg::ZoneRequest::SharedPtr);
  bool _zone_pool_is_idle(const std::string&) const;
  void _sweep_idle_zone_pools();
};
#include "extracted.inc"

using Z = ZoneReservationClient;
using S = Z::Holding::State;
void ck(bool c){ if(!c) std::abort(); }
struct Fixture {
  std::shared_ptr<Node> n=std::make_shared<Node>();
  std::shared_ptr<Z> z=std::make_shared<Z>();
  Fixture(){n->_reservation_client=z;z->_node=n;}
  void hold(std::string v,int k){
    z->_holdings.emplace(v,std::make_shared<Z::Holding>(Z::Holding{"Z","req",S::Held,{},k}));
  }
  void grant(const std::string& v,const std::string& r) {
    ck(z->transfer("Z",v,"F",r));
    n->_zone_log.emplace(v,Node::Log{"Z","F",r,false});
  }
  auto msg(std::string r, std::string v=""){
    auto m=std::make_shared<rmf_zone_msgs::msg::ZoneRequest>();
    m->robot_name=r; m->released_waypoint=v; return m;
  }
  void sweep(int t) {
    n->time=Time(std::chrono::seconds(t)); n->_sweep_idle_zone_pools();
  }
  int stamp() const {
    auto i=n->_zone_idle_since.find("Z");
    return i==n->_zone_idle_since.end() ? -100000 : i->second.time_since_epoch().count();
  }
  std::size_t releases() const {return z->_release_pub->releases.size();}
};

int main() {
  for (int hidden=0; hidden<=1; ++hidden) {
    Fixture f; f.hold("spare",1); f.hold("occupied",2);
    f.grant("occupied","parked");
    f.n->_process_arrived(f.msg("parked"));
    f.n->_process_handback(f.msg("parked","occupied"));
    ck(!f.z->is_available("Z","occupied"));
    f.sweep(0);
    f.grant("spare","visitor");
    if (!hidden) f.sweep(12);
    f.n->_process_exit(f.msg("visitor"));
    ck(f.n->_zone_pool_is_idle("Z"));
    ck(f.z->is_available("Z","spare"));
    ck(f.releases()==0);
    f.sweep(29); ck(f.releases()==0);
    f.sweep(30); ck(f.releases()==static_cast<unsigned>(hidden));
    ck(!f.z->is_available("Z","occupied"));
    if(!hidden){ f.sweep(58);ck(f.releases()==0);f.sweep(59); }
    ck(f.releases()==1);
    ck(f.z->_release_pub->releases.front() == std::make_pair(uint64_t(1),std::string("spare")));
    f.n->_process_exit(f.msg("parked")); ck(f.z->is_available("Z","occupied"));ck(f.releases()==1);
    int last=hidden ? 30 : 59;
    f.sweep(last+29);ck(f.releases()==1); f.sweep(last+30);ck(f.releases()==2);
    ck(f.z->_release_pub->releases.back() == std::make_pair(uint64_t(2),std::string("occupied")));
    std::cout<<"visitor busy callback "<<(hidden?"not observed":"observed")<<": spare released at "<<last<<" and occupied slot at "<<last+30<<" after exit\n";
  }

  // 200 ms cadence expressed as a tick; source timeout is 150 ticks.
  for (int busy_sample=0;busy_sample<=1;++busy_sample) {
    Fixture f; f.n->_zone_pool_idle_timeout=std::chrono::seconds(150);
    f.hold("spare",1);
    f.sweep(0);
    f.grant("spare","visitor");
    if(!busy_sample) f.n->_process_exit(f.msg("visitor"));
    f.sweep(1);
    if(busy_sample) f.n->_process_exit(f.msg("visitor"));
    int released=-1;
    for(int t=2;t<=152;++t){
      auto prior=f.releases(); f.sweep(t);
      if(f.releases()!=prior){ck(released<0);released=t;}
    }
    ck(released==150+2*busy_sample);
    std::cout<<"200 ms cadence, busy sample "<<busy_sample<<": release tick "<<released<<"\n";
  }

  int pairs=0;
  for(int T=1;T<=60;++T)for(int a=0;a<T+2;++a)for(int b=a+1;b<T+2;++b){
    // d=0..T, and T+1 codes absent. The first sweep at min(d) separates.
    auto trial=[&](int d){
      Fixture f; f.n->_zone_pool_idle_timeout=std::chrono::seconds(T);
      f.hold("spare",1);
      if(d<=T)f.sweep(d-T);
      f.sweep(a);
      return f.releases();
    };
    ck(trial(a)==1);ck(trial(b)==0);++pairs;
  }
  std::cout<<"distinct integer residual pairs separated by a first sweep: "<<pairs<<"\n";

  // Exhaustively compare actual release publication after one future sweep
  // with independent clipped-time formula; no current grant/entry is attempted.
  int checks=0;
  for(int cap=1;cap<=60;++cap)for(int age=-1;age<=cap+2;++age)for(int offset=0;offset<=cap+1;++offset)
  for(int mode=0;mode<3;++mode) {
    Fixture f;
    f.n->_zone_pool_idle_timeout=std::chrono::seconds(cap);
    f.hold("spare",1);
    if (age>=0) f.sweep(-age);
    if(mode==1) f.n->_pending_entries["Z"].push_back("someone");
    if(mode==2){ f.hold("booked",2); f.grant("booked","enroute"); }
    f.sweep(offset);
    ck(f.releases() == static_cast<unsigned>(mode==0 && age>=0 && age+offset>=cap));
    if(mode)ck(f.stamp()==-100000);
    if(!mode && age==-1)ck(f.stamp()==offset);
    ++checks;
  }
  std::cout<<"source vs release formula: "<<checks<<" cases\n";
}
