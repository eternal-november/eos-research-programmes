#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <vector>

#define RCLCPP_INFO(...) ((void)0)
#define RCLCPP_DEBUG(...) ((void)0)
#define RCLCPP_ERROR(...) ((void)0)
namespace rclcpp {
struct Node : std::enable_shared_from_this<Node> {};
}
namespace rmf_reservation_msgs::msg {
struct RequestHeader { std::string fleet_name, robot_name; uint64_t request_id=0; };
struct Ticket { RequestHeader header; std::size_t ticket_id=0; };
struct ReleaseRequest { using ConstSharedPtr=std::shared_ptr<const ReleaseRequest>; Ticket ticket; };
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
#include "extracted.inc"

using namespace rmf_reservation_msgs::msg;
void ck(bool p) { if(!p) std::abort(); }
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

int main() {
  int checks=0;
  for(int l=0;l<=128;++l)for(int flip=0;flip<=1;++flip)
  for(int prefersB=0;prefersB<=1;++prefersB)for(int q_first=0;q_first<=1;++q_first){
    Trial f;
    Ticket ar=f.claim({{"A",0}}, {}, true);
    Ticket br=f.claim({{"B",0}}, {}, true);
    auto flex=[&](){ return f.claim({{"A",static_cast<double>(prefersB)},{"B",static_cast<double>(!prefersB)}},{"QF"}); };
    auto strict=[&](){return f.claim({{"A",0}},{wp(0)});};
    Ticket x,y;
    if(q_first){y=strict();x=flex();}else{x=flex();y=strict();}
    std::vector<Ticket> followers;
    for(int i=1;i<=l;++i)followers.push_back(f.claim({{wp(i-1),0}},{wp(i)}));
    auto old=f.count();
    if(flip){f.release(br);f.release(ar);}else{f.release(ar);f.release(br);}
    auto got=f.final_allocs(old);
    std::vector<std::pair<std::size_t,std::string>> want;
    using P=std::pair<std::size_t,std::string>;
    if(flip)want.emplace_back(x.ticket_id,"B");
    if(!flip && !q_first){want.emplace_back(x.ticket_id,"A");}
    else {
      want.emplace_back(y.ticket_id,"A");
      for(int i=0;i<l;++i)want.emplace_back(followers[i].ticket_id,wp(i));
      if(!flip)want.emplace_back(x.ticket_id,"B");
    }
    ck(got==want);
    if(l==4 && !q_first && !prefersB) {
      std::cout<<(flip?"B then A:":"A then B:");
      for(auto& [id,site]:got)std::cout<<" "<<id<<"->"<<site;
      std::cout<<"\n";
    }
    ++checks;
  }
  std::cout<<"native against ordered direct allocation rule: "<<checks<<" cases\n";
}
