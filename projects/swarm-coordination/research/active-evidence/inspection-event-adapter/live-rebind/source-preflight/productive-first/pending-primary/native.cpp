#define TIMED_SOURCE_LIBRARY
#include "driver.cpp"

enum class Phase { QUEUED, BUFFERED, PAID, FAILED, REVOKED };

int main(){
 int launch,old_first,buffered,wire_good,app_good,source_owner,app_owner,H,rule;
 while(std::cin>>launch>>old_first>>buffered>>wire_good>>app_good>>source_owner>>app_owner>>H>>rule){
  now=0;
  TimedSource v(.5);
  for(auto& [id,n]:*v.plant.b.team)n->radio.capacity=8*(2+H);
  unsigned wire=0,alternate=0;
  v.bind("PrimaryDelivery","Second",wire);
  v.bind("AlternateDelivery","Base",alternate);
  v.dispatch(v.preceding);
  v.dispatch({"Independent","Other",1,.125,false});
  const double start=launch/10.;
  const double decision=.4;
  // Native callback and final application effect are explicitly different
  // in the buffered case. Only this authored application owns its commit.
  Phase s=Phase::QUEUED;
  unsigned old_applied=0,source_revoked=0,app_revoked=0;
  double primary_apply_time=-1.;
  auto commit=[&](){
    assert(s==Phase::BUFFERED);
    if(app_good){++old_applied;primary_apply_time=now;s=Phase::PAID;}
    else s=Phase::FAILED;
  };
  auto issue=[&](){
    assert(s==Phase::QUEUED);
    v.dispatch({"P","PrimaryDelivery",3,start,true},!wire_good);
    if(!wire)s=Phase::FAILED;
    else{
      s=Phase::BUFFERED;
      if(!buffered)commit();
    }
  };
  if(start<decision || (start==decision&&old_first))issue();
  const auto at_cut=s;
  auto actual_tx=v.plant.state("P").bytes_sent_this_epoch;
  auto actual_rx=v.plant.state("Base").bytes_received_this_epoch;
  Job f={"P","AlternateDelivery",2,decision,true};
  bool allowed=false;
  if(rule==0) allowed=(s!=Phase::PAID); // isolated naive control
  if(rule==1) allowed=(s==Phase::FAILED); // only true terminal unpaid
  if(rule==2){ // atomic gate owns all effects that it claims to revoke
    // Do not cancel usable old work before checking actual alternate headroom.
    if(v.law(f,"Base",false)){
      if(s==Phase::QUEUED&&source_owner){s=Phase::REVOKED;source_revoked=1;allowed=true;}
      else if(s==Phase::BUFFERED&&app_owner){s=Phase::REVOKED;app_revoked=1;allowed=true;}
      else if(s==Phase::FAILED)allowed=true;
    }
  }
  if(allowed)v.dispatch(f);
  if(s==Phase::QUEUED)issue();
  if(s==Phase::BUFFERED){ // authored application queue may still apply
    assert(now<=.65);now=.65;commit();
  }
  if(old_applied)assert(primary_apply_time>=0.3 && primary_apply_time<=.7);
  assert(v.first==1&&v.independent==1);
  std::cout<<int(at_cut)<<' '<<actual_tx<<' '<<actual_rx<<' '
    <<source_revoked<<' '<<app_revoked<<' '<<wire<<' '<<old_applied<<' '
    <<alternate<<' '<<int(old_applied+alternate==1)<<' '<<v.independent<<'\n';
 }
}
