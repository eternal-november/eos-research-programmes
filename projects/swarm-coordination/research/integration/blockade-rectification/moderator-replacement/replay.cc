#include <rmf_traffic/blockade/Moderator.hpp>
#include <rmf_traffic/blockade/Participant.hpp>
#include <rmf_traffic/blockade/Rectifier.hpp>
#include <cassert>
#include <iostream>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <vector>
using namespace rmf_traffic::blockade;

struct RelayWriter : Writer {
  Moderator* moderator = nullptr;
  std::vector<std::string> log;
  void set(ParticipantId p, ReservationId r, const Reservation& b) override {
    log.push_back("SET " + std::to_string(p));
    moderator->set(p,r,b);
  }
  void ready(ParticipantId p, ReservationId r, CheckpointId c) override {
    log.push_back("READY " + std::to_string(p) + " " + std::to_string(c));
    moderator->ready(p,r,c);
  }
  void release(ParticipantId p, ReservationId r, CheckpointId c) override {
    log.push_back("RELEASE " + std::to_string(p));
    moderator->release(p,r,c);
  }
  void reached(ParticipantId p, ReservationId r, CheckpointId c) override {
    log.push_back("REACHED " + std::to_string(p) + " " + std::to_string(c));
    moderator->reached(p,r,c);
  }
  void cancel(ParticipantId p, ReservationId r) override {moderator->cancel(p,r);}
  void cancel(ParticipantId p) override {moderator->cancel(p);}
};

Writer::Checkpoint at(double x,double y) {return {{x,y},"civil-bay",true};}
const std::vector<Writer::Checkpoint> west={at(-4,0),at(0,0),at(4,0)};
const std::vector<Writer::Checkpoint> south={at(0,-4),at(0,0),at(0,4)};
const std::vector<Writer::Checkpoint> distant={at(12,-4),at(12,0),at(12,4)};

size_t end(const Moderator& c, ParticipantId p) {
  return c.assignments().ranges().at(p).end;
}

struct Scenario {
  std::shared_ptr<Moderator> live=std::make_shared<Moderator>();
  std::shared_ptr<Moderator> fresh=std::make_shared<Moderator>();
  std::shared_ptr<RelayWriter> w=std::make_shared<RelayWriter>();
  std::shared_ptr<ModeratorRectificationRequesterFactory> rect=
    std::make_shared<ModeratorRectificationRequesterFactory>(fresh);
  Participant a=make_participant(1,.25,w,rect);
  Scenario() {
    w->moderator=live.get();
    a.set(west);
    a.ready(0);
    assert(end(*live,1)==1);
    a.reached(1);
    assert(live->statuses().at(1).last_reached==1);
    // The fixture treats the actual old vehicle as parked at point (0,0).
  }
};

void carried_authority(bool released) {
  Moderator live, fresh;
  auto w=std::make_shared<RelayWriter>();
  w->moderator=&live;
  auto a=make_participant(1,.25,w);
  auto approach=std::vector<Writer::Checkpoint>{at(-4,0),at(-2,0),at(2,0),at(4,0)};
  a.set(approach);
  a.ready(0);
  assert(end(live,1)==1);
  a.reached(1);
  if(released) a.ready(1);
  assert(end(live,1)==(released?2:1));
  // The actual fixture state at the cut is checkpoint 1 in both cases.
  assert(a.last_reached()==1);
  {
    auto b=make_participant(2,.25,w);
    b.set(south);
    b.ready(0);
    assert(end(live,2)==(released?0:1));
  }
  w->moderator=&fresh;
  auto b=make_participant(2,.25,w);
  b.set(south);
  b.ready(0);
  assert(end(fresh,2)==1);
  // At this cut, the old segment -2..2 has not been physically settled.
  // Authorization to traverse it is different in the two old histories.
}
int main() {
  {
    Scenario s;
    auto b=make_participant(2,.25,s.w);
    b.set(south);
    b.ready(0);
    auto d=make_participant(3,.25,s.w);
    d.set(distant);
    d.ready(0);
    assert(end(*s.live,2)==0 && end(*s.live,3)==1);
    std::cout << "old moderator: crossing held, disjoint work admitted\n";
  }
  {
    Scenario s;
    s.w->moderator=s.fresh.get();
    auto b=make_participant(2,.25,s.w);
    b.set(south);
    b.ready(0);
    auto d=make_participant(3,.25,s.w);
    d.set(distant);
    d.ready(0);
    assert(end(*s.fresh,2)==1 && end(*s.fresh,3)==1);
    // Let the participant re-establish its route after the grant.
    s.w->log.clear();
    s.rect->rectify();
    assert((s.w->log==std::vector<std::string>{"SET 1"}));
    const auto& r1=s.fresh->assignments().ranges().at(1);
    assert(r1.begin==0 && r1.end==0);
    assert(end(*s.fresh,2)==1);
    bool error=false;
    try {s.rect->rectify();} catch(const std::runtime_error&) {error=true;}
    const auto st=s.fresh->statuses().at(1);
    assert(error && st.last_reached==0 && st.critical_error);
    assert(end(*s.fresh,1)==0 && end(*s.fresh,2)==1);
    std::cout << "fresh moderator, crossing requested before old route arrives: grant retained\n";
    std::cout << "old route restored without progress; second rectification cannot record reached 1\n";
  }
  {
    Scenario s;
    // Durable native history is the strongest matched stock reconstruction,
    // not an advantage attributed to the new monitor.
    s.fresh->set(1,*s.a.reservation_id(),Writer::Reservation{west,.25});
    s.fresh->ready(1,*s.a.reservation_id(),0);
    s.fresh->reached(1,*s.a.reservation_id(),1);
    s.w->moderator=s.fresh.get();
    auto b=make_participant(2,.25,s.w);
    b.set(south);
    b.ready(0);
    auto d=make_participant(3,.25,s.w);
    d.set(distant);
    d.ready(0);
    assert(end(*s.fresh,2)==0 && end(*s.fresh,3)==1);
    std::cout << "durable native prefix reconstructed: crossing held, disjoint work admitted\n";
    s.a.ready(1);
    assert(end(*s.fresh,1)==2 && end(*s.fresh,2)==1);
    assert(s.fresh->statuses().at(1).last_reached==1);
    // Simulated effector guard: do not cross merely because the call above
    // permits it. A is still modeled at the crossing until it reaches 2.
    bool b_after_physical_exit=s.a.last_reached()>=2;
    assert(!b_after_physical_exit);
    s.a.reached(2);
    b_after_physical_exit=s.a.last_reached()>=2;
    assert(end(*s.fresh,2)==1 && b_after_physical_exit);
    std::cout << "native grants crossing on readiness, before old reached 2\n";
    std::cout << "modeled separation guard permits crossing only after old exit\n";
  }

  carried_authority(false);
  carried_authority(true);
  std::cout << "same old location, old grant ends at one/two: native crossing granted/held\n";
  std::cout << "empty reconstruction grants crossing for both prior authorizations\n";
}
