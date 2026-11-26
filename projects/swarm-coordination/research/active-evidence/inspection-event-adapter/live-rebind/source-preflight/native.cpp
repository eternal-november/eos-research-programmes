#define TIMED_SOURCE_LIBRARY
#include "driver.cpp"

int main(){
 int c,primary_bytes,fallback_bytes,late,pp,fp,pd,fd,pe,fe,probeP,probeF,hold,change;
 while(std::cin>>c>>primary_bytes>>fallback_bytes>>late>>pp>>fp>>pd>>fd>>pe>>fe
               >>probeP>>probeF>>hold>>change){
  now=0;
  TimedSource v(.5);
  for(auto& [_,node]:*v.plant.b.team)node->radio.capacity=8*c;
  v.fresh.bytes=c-2;
  unsigned p=0,f=0;
  v.bind("ProbePrimary","Second",p);
  v.bind("ProbeFallback","Base",f);
  v.dispatch(v.preceding);
  v.dispatch({"Independent","Other",1,.125,false});
  assert(v.acquire(v.version)); // Initial optional claim, before added test choice.
  if(probeP)v.dispatch({"Q","ProbePrimary",unsigned(primary_bytes),.25,false},!pp||pe);
  if(hold)assert(v.cancel_optional());
  auto edit=[&](){
    if(!change)return false;
    Job q=v.tail;q.src="P";
    if(!v.law(q,"Base",false))return false;
    if(v.reserved)v.cancel_optional();
    assert(v.amend(true,true));
    return true;
  };
  bool changed=false;
  if(probeF&&late){
    if(v.reserved)v.execute_new(false);
    v.dispatch({"P","ProbeFallback",unsigned(fallback_bytes),.625,false},!fp||fe);
    changed=edit();
  }else{
    if(probeF)v.dispatch({"P","ProbeFallback",unsigned(fallback_bytes),.375,false},!fp||fe);
    changed=edit();
    if(v.reserved)v.execute_new(false);
  }
  v.dispatch(v.tail,changed?!fd:!pd);
  assert(v.first==1&&v.independent==1);
  std::cout<<(probeP?int(p):-1)<<' '<<(probeF?int(f):-1)<<' '
    <<v.last<<' '<<v.optional<<' '<<int(changed)<<' '<<v.first<<' '<<v.independent<<'\n';
 }
}
