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
  struct Cue { ParticipantId p; ReservationId r; CheckpointId c; };
  std::vector<Cue> held;
  bool delay=false;
  void set(ParticipantId p, ReservationId r, const Reservation& b) override {
    log.push_back("SET " + std::to_string(p));
    moderator->set(p,r,b);
  }
  void ready(ParticipantId p, ReservationId r, CheckpointId c) override {
    log.push_back("READY " + std::to_string(p) + " " + std::to_string(c));
    if(delay && p==1 && c==1) {held.push_back({p,r,c});return;}
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


const std::vector<Writer::Checkpoint> approach={at(-4,0),at(-2,0),at(2,0),at(4,0)};
struct Row { size_t a,b; bool same_token; };
void setup(Participant& a,Moderator& m) {
  a.set(approach);
  a.ready(0);
  a.reached(1);
  assert(end(m,1)==1 && m.statuses().at(1).last_reached==1);
}
void check(int renew,bool stale,int boundary,int fold,bool revoke,bool exercised) {
  // All traffic is in-memory callback delivery in a civil test fixture.
  // Old drive is modeled stopped at -2; no actual robot controller runs.
  Moderator m, replacement;
  Moderator *active=&m;
  auto w=std::make_shared<RelayWriter>();
  w->moderator=active;
  auto a=std::make_unique<Participant>(make_participant(1,.25,w));
  setup(*a,*active);
  const auto old=*a->reservation_id();
  if(stale){
    w->delay=true;
    a->ready(1);
    w->delay=false;
    assert(w->held.size()==1);
    if(exercised) {
      const auto q=w->held.front();
      active->ready(q.p,q.r,q.c);
      assert(end(*active,1)==2);
    }
    a->release(1);
    assert(end(*active,1)==1);
  }
  if(renew==1) setup(*a,*active);
  if(renew==2){
    a.reset();
    active=&replacement;
    w->moderator=active;
    a=std::make_unique<Participant>(make_participant(1,.25,w));
    setup(*a,*active);
  }
  const auto cur=*a->reservation_id();
  assert(cur==(renew==1?2:1));
  assert(active->statuses().at(1).last_ready==0 && end(*active,1)==1);
  auto b=make_participant(2,.25,w);
  b.set(south); b.ready(0);
  assert(end(*active,2)==1);
  if(boundary>=1){b.reached(1);b.ready(1);assert(end(*active,2)==2);}
  if(boundary>=2)b.reached(2);
  auto d=make_participant(3,.25,w);
  d.set(distant);d.ready(0);d.reached(1);
  assert(end(*active,3)==1);
  if(!stale){
    w->delay=true;a->ready(1);w->delay=false;
    assert(w->held.size()==1);
  }
  const auto q=w->held.front();
  assert(q.p==1 && q.c==1 && q.r==(stale?old:cur));
  const auto before=active->statuses().at(1);
  assert(before.reservation==cur && before.last_ready==0 && before.last_reached==1);
  const auto current_source=[&](){
    return a->reservation_id()==q.r
      && a->last_ready().has_value() && *a->last_ready()>=q.c;
  };
  const bool sampled=current_source();
  assert(sampled==!stale);
  if (revoke) {
    a->release(1);
    assert(!current_source());
  }
  const bool qualified=current_source();
  assert(qualified==(!stale&&!revoke));
  // Fold 1 serializes actual source qualification with forwarding.
  // Fold 2 trusts the earlier source read once, before withdrawal.
  const bool forward=fold==0 || (fold==1 && qualified) || (fold==2 && sampled);
  if(forward) active->ready(q.p,q.r,q.c);
  const auto after=active->statuses().at(1);
  assert(after.reservation==cur && after.last_reached==1);
  const bool ready=after.last_ready==1;
  assert(ready==(forward&&(q.r==cur)));
  assert(end(*active,3)==1&&active->statuses().at(3).last_reached==1);
  std::cout << renew<<" "<<stale<<" "<<boundary<<" "<<fold<<" "<<revoke<<" "<<exercised<<" "
            <<cur<<" "<<q.r<<" "<<ready<<" "<<end(*active,1)<<" "<<end(*active,2)<<"\n";
}
int main(){
 for(int renew:{0,1,2})
  for(bool stale:{false,true})
   for(int boundary:{0,1,2})
    for(int fold:{0,1,2})
     for(bool revoke:{false,true})if(!stale || !revoke)
      for(bool exercised:{false,true})if(stale || !exercised)check(renew,stale,boundary,fold,revoke,exercised);
}
