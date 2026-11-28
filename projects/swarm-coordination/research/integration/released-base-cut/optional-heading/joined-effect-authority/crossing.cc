#include <rmf_traffic/blockade/Moderator.hpp>
#include <rmf_traffic/blockade/Writer.hpp>
#include <cassert>
#include <vector>
using namespace rmf_traffic::blockade;
Writer::Checkpoint p(double x,double y){return {{x,y},"inspection-bay",true};}
struct Crossing {
 Moderator m;
 explicit Crossing(){
  m.set(1,1,Writer::Reservation{{p(-4,0),p(0,0),p(4,0)},.25});
  m.ready(1,1,0);m.reached(1,1,1);
  m.set(2,1,Writer::Reservation{{p(0,-4),p(0,0),p(0,4)},.25});
  m.ready(2,1,0);
  assert(!permit());
  m.set(3,1,Writer::Reservation{{p(12,-4),p(12,4)},.25});
 }
 bool permit(){return m.assignments().ranges().at(2).end>=1;}
 bool clear(){return m.statuses().at(1).last_reached>=2;}
};
void* rmf_start(){return new Crossing();}
void rmf_exit_ready(void* r){auto& q=*static_cast<Crossing*>(r);q.m.ready(1,1,1);assert(q.permit());}
void rmf_exit(void* r){static_cast<Crossing*>(r)->m.reached(1,1,2);}
void rmf_retire(void* r){auto& q=*static_cast<Crossing*>(r);q.m.release(2,1,0);assert(!q.permit());}
void rmf_renew(void* r){auto& q=*static_cast<Crossing*>(r);q.m.ready(2,1,0);assert(q.permit());}
void rmf_unrelated(void* r){auto& q=*static_cast<Crossing*>(r);q.m.ready(3,1,0);q.m.reached(3,1,1);}
bool rmf_permit(void* r){return static_cast<Crossing*>(r)->permit();}
bool rmf_clear(void* r){return static_cast<Crossing*>(r)->clear();}
bool rmf_unrelated_done(void* r){return static_cast<Crossing*>(r)->m.statuses().at(3).last_reached==1;}
void rmf_end(void* r){delete static_cast<Crossing*>(r);}
