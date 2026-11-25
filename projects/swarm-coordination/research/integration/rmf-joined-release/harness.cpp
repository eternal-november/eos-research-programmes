#include <chrono>
#include <algorithm>
#include <set>
#include <sstream>
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
#define RCLCPP_ERROR(...) ((void)0)
#define RCLCPP_DEBUG(...) ((void)0)
namespace rclcpp {
using Time = std::chrono::time_point<std::chrono::steady_clock, std::chrono::seconds>;
using Duration = std::chrono::seconds;
}
using Time = rclcpp::Time;
namespace rclcpp {
struct Node : std::enable_shared_from_this<Node> {};
}
namespace rmf_reservation_msgs::msg {
struct RequestHeader { std::string fleet_name, robot_name; uint64_t request_id=0; };
struct Ticket { RequestHeader header; std::size_t ticket_id=0; };
struct ReleaseRequest { using ConstSharedPtr=std::shared_ptr<const ReleaseRequest>; Ticket ticket; std::string location; };
struct FlexibleTimeRequest {
  using ConstSharedPtr=std::shared_ptr<const FlexibleTimeRequest>;
  struct Alternative { std::string resource_name; double cost; };
  RequestHeader header; std::vector<Alternative> alternatives;
};
struct ClaimRequest {
  using ConstSharedPtr=std::shared_ptr<const ClaimRequest>;
  Ticket ticket; std::vector<std::string> wait_points;
};
struct ReservationAllocation {
  enum { IMMEDIATELY_PROCEED=1, WAIT_IDENTIFIED=2 };
  Ticket ticket;
  std::size_t chosen_alternative;
  int instruction_type;
  std::string resource;
};
}
template<class M> struct Sink {
  std::vector<M> sent;
  void publish(const M& m) {sent.push_back(m);}
};
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
    std::string zone; uint64_t request_id;
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
#include "zone.inc"
#include "reservation.inc"

using Z = ZoneReservationClient;
using S = Z::Holding::State;
void ck(bool c){ if(!c) std::abort(); }
using namespace rmf_reservation_msgs::msg;
std::string wp(int i) { return "P"+std::to_string(i); }

struct Trial {
  std::shared_ptr<ReservationNode> n=std::make_shared<ReservationNode>();
  int counter=0;
  Ticket claim(std::vector<FlexibleTimeRequest::Alternative> opts, std::vector<std::string> wait, bool already_final=false) {
    auto q=std::make_shared<FlexibleTimeRequest>();
    q->header=RequestHeader{"fleet",std::to_string(++counter),static_cast<uint64_t>(counter)};
    q->alternatives=std::move(opts);
    std::size_t ct=n->allocation_pub_->sent.size();
    n->on_request(q);
    Ticket t=n->ticket_pub_->sent.back();
    auto c=std::make_shared<ClaimRequest>();
    c->ticket=t; c->wait_points=std::move(wait);
    n->claim_request(c);
    ck(n->allocation_pub_->sent.size()==ct+1);
    auto& a=n->allocation_pub_->sent.back();
    ck(a.ticket.ticket_id==t.ticket_id);
    ck(a.instruction_type==(already_final?ReservationAllocation::IMMEDIATELY_PROCEED:ReservationAllocation::WAIT_IDENTIFIED));
    return t;
  }
  void release(const Ticket& t) {
    auto r=std::make_shared<ReleaseRequest>();r->ticket=t;n->release(r);
  }
  std::size_t count() const {return n->allocation_pub_->sent.size();}
  auto final_allocs(std::size_t i) const {
    std::vector<std::pair<std::size_t,std::string>> result;
    for(;i<count();++i){
      auto& a=n->allocation_pub_->sent.at(i);
      ck(a.instruction_type==ReservationAllocation::IMMEDIATELY_PROCEED);
      result.emplace_back(a.ticket.ticket_id,a.resource);
    }
    return result;
  }
};


struct Coupled {
  Trial allocator;
  std::shared_ptr<Node> n=std::make_shared<Node>();
  std::shared_ptr<Z> client=std::make_shared<Z>();
  std::vector<std::pair<int,std::string>> order;
  std::size_t delivered_releases=0;
  int now=0;
  Coupled(int cap){
    n->_reservation_client=client; client->_node=n;
    n->_zone_pool_idle_timeout=std::chrono::seconds(cap);
  }
  Ticket add_zone_reserve(std::string z,std::string p) {
    Ticket t=allocator.claim({{p,0}}, {},true);
    client->_holdings.emplace(p,std::make_shared<Z::Holding>(
      Z::Holding{z,t.header.request_id,S::Held,{},t.ticket_id}));
    return t;
  }
  void grant_a_to_visitor(){
    ck(client->transfer("ZA","A","F","visitor"));
    n->_zone_log.emplace("A",Node::Log{"ZA","F","visitor",false});
  }
  void visitor_departed(){
    auto msg=std::make_shared<rmf_zone_msgs::msg::ZoneRequest>();
    msg->zone_name="ZA"; msg->robot_name="visitor";
    n->_process_exit(msg);
    ck(client->is_available("ZA","A"));
  }
  void sweep(int t) {
    now=t; n->time=Time(std::chrono::seconds(t));
    n->_sweep_idle_zone_pools();
    for(;delivered_releases<client->_release_pub->releases.size();++delivered_releases){
      auto [id,p]=client->_release_pub->releases.at(delivered_releases);
      order.emplace_back(now,p);
      allocator.release(allocator.n->ticket_store_.get_existing_ticket(id));
    }
  }
  bool both_held() const {
    return client->is_available("ZA","A") && client->is_available("ZB","B")
      && n->_zone_log.empty();
  }
};

struct Effect {
  int tick;
  std::size_t id;
  std::string destination;
  std::string previous;
};

// Adapter for a distinct physical layer. A grant registers an obligation;
// the destination is only entered once actually empty. Own waiting site is
// cleared after independently supplied movement duration. Paths/geometry
// outside reservations are not modelled; no runtime interpretation of ROS.
std::vector<std::vector<std::pair<int,std::string>>> physical(
  const std::vector<Effect>& proposals, std::unordered_set<std::string> occupied,
  int duration, int miss_limit=100000)
{
  std::vector<std::vector<std::pair<int,std::string>>> log;
  std::unordered_map<std::string,std::vector<int>> waits_until;
  int end=0;
  for(const auto& v:proposals)end=std::max(end,v.tick);
  // Holds remain unless physically cleared before the destination cut.
  struct Pending { int finish; std::string from,to; };
  std::vector<Pending> live;
  std::unordered_set<std::string> leased;
  std::vector<bool> used(proposals.size(),false);
  for(int t=0;t<=std::min(end+duration*(int(proposals.size())+2),miss_limit);++t){
    std::vector<std::pair<int,std::string>> events;
    for(auto& f:live)if(f.finish==t){
      ck(occupied.erase(f.from)==1);
      ck(occupied.insert(f.to).second);
      ck(leased.erase(f.to)==1);
      events.emplace_back(t,f.to);
    }
    if(!events.empty())log.push_back(events);
    for(std::size_t i=0;i<proposals.size();++i){
      auto& a=proposals[i];
      if(!used[i] && a.tick<=t && !occupied.count(a.destination) && !leased.count(a.destination)){
        ck(occupied.count(a.previous)>0);
        used[i]=true;
        leased.insert(a.destination);
        live.push_back({t+duration,a.previous,a.destination});
      }
    }
  }
  return log;
}

void matches(int C,int length,bool visit_sampled,bool blocker_first,int duration,bool announce) {
  Coupled f(C);
  auto A=f.add_zone_reserve("ZA","A");
  f.sweep(0);
  auto B=f.add_zone_reserve("ZB","B");
  auto flex=[&](){return f.allocator.claim({{"A",0},{"B",1}},{"QF"});};
  auto fixed=[&](){return f.allocator.claim({{"A",0}},{wp(0)});};
  Ticket x,y;
  if(blocker_first){y=fixed();x=flex();}else{x=flex();y=fixed();}
  std::vector<Ticket> follower;
  std::unordered_map<std::size_t,std::string> wait_site{
    {x.ticket_id,"QF"},{y.ticket_id,wp(0)}};
  std::unordered_set<std::string> occupied{"QF",wp(0)};
  for(int i=1;i<=length;++i){
    auto k=f.allocator.claim({{wp(i-1),0}},{wp(i)});
    wait_site[k.ticket_id]=wp(i);occupied.insert(wp(i));
    follower.push_back(k);
  }
  std::size_t prev=f.allocator.count();
  f.grant_a_to_visitor();
  if(!visit_sampled)f.visitor_departed();
  f.sweep(1);
  if(visit_sampled)f.visitor_departed();
  f.sweep(2);
  ck(f.both_held());ck(f.allocator.count()==prev);ck(f.order.empty());

  std::vector<Effect> effects;
  for(int tick=3;tick<=C+2;++tick){
    auto old=f.allocator.count();
    f.sweep(tick);
    for(auto& [id,d]:f.allocator.final_allocs(old)){
      effects.push_back({tick,id,d,wait_site.at(id)});
    }
  }
  std::vector<std::pair<int,std::string>> order=
    visit_sampled?std::vector<std::pair<int,std::string>>{{C+1,"B"},{C+2,"A"}}:
                  std::vector<std::pair<int,std::string>>{{C,"A"},{C+1,"B"}};
  ck(f.order==order);
  int expected=(!visit_sampled && !blocker_first)?1:length+2;
  ck(int(effects.size())==expected);
  std::vector<std::pair<int,std::string>> direct;
  if(visit_sampled)direct.emplace_back(C+1,"B");
  if(!visit_sampled && !blocker_first)direct.emplace_back(C,"A");
  else {
    int d=visit_sampled?C+2:C;
    direct.emplace_back(d,"A");
    for(int i=0;i<length;++i)direct.emplace_back(d,wp(i));
    if(!visit_sampled)direct.emplace_back(C+1,"B");
  }
  ck(direct.size()==effects.size());
  for(std::size_t i=0;i<direct.size();++i)
    ck(direct[i]==std::make_pair(effects[i].tick,effects[i].destination));

  auto log=physical(effects,occupied,duration);
  int count=0;
  std::unordered_map<std::string,int> finish;
  for(const auto& v:log)for(auto& [t,s]:v){++count;ck(finish.emplace(s,t).second);}
  ck(count==expected);
  const int a=visit_sampled?C+2:C;
  ck(finish.at("A")==a+duration);
  if(expected>1){
    ck(finish.at("B")==C+1+duration);
    for(int i=0;i<length;++i)ck(finish.at(wp(i))==a+(i+2)*duration);
  }
  for(int D=C-1;D<=C+4+(length+2)*duration;++D){
    int actual=0;for(auto& [_,when]:finish)actual+=int(when<=D);
    int by_cut=expected==1 ? int(D>=a+duration) :
      int(D>=C+1+duration)+std::max(0,std::min(length+1,(D-a)/duration));
    ck(actual==by_cut);
  }
  if(announce)std::cout<<"visitor "<<(visit_sampled?"sampled":"not sampled")
    <<": releases "<<order[0].second<<"@"<<order[0].first<<" "<<order[1].second<<"@"<<order[1].first
    <<", logical grants "<<expected<<", guarded completions by "<<log.back().back().first<<" "<<count<<"\n";
}

int main(){
  int checks=0;
  for(int C:{3,4,7,30,150})for(int n=0;n<=48;++n)
  for(int seen=0;seen<2;++seen)for(int first=0;first<2;++first)for(int duration:{1,2,5}){
    matches(C,n,seen,first,duration,n==4 && C==30 && !first && duration==2);
    ++checks;
  }
  std::cout<<"joined source orders, direct outcomes and guarded physical replays: "<<checks<<" cases\n";
}
