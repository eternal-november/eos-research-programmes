#define TIMED_SOURCE_LIBRARY
#include "driver.cpp"

int main(){
 int mode,h,healthy,first_action,ack,local;
 // mode: 0 path loss / 1 no endpoint (resources still shared)
 // first_action: 0 diagnostic, 1 useful, 2 useful with masked observer
 while(std::cin>>mode>>h>>healthy>>first_action>>ack>>local){
  now=0;
  TimedSource w(.5);
  for(auto& [id,n]:*w.plant.b.team)n->radio.capacity=8*(2+h);
  unsigned diag=0,pri=0,fall=0;
  w.bind("Diagnosis","Second",diag);
  w.bind("UsefulPrimary","Second",pri);
  w.bind("UsefulFallback","Base",fall);
  w.dispatch(w.preceding);
  w.dispatch({"Independent","Other",1,.125,false});
  if(!healthy && mode==1){
    w.plant.b.endpoints.erase("Diagnosis:7");
    w.plant.b.endpoints.erase("UsefulPrimary:7");
  }
  auto primary=[&](double at){
      w.dispatch({"P","UsefulPrimary",3,at,true},!healthy);
  };
  auto fallback=[&](double at){
      w.dispatch({"P","UsefulFallback",2,at,true},healthy&&first_action!=2);
  };
  unsigned observed=0;
  if(first_action==0){
    w.dispatch({"P","Diagnosis",1,.25,false},!healthy);
    observed=diag;
    if(diag)primary(.375);else fallback(.375);
  }else{
    primary(.25);
    assert(diag==0);
    observed=ack?pri:0;
    if(!observed){
      // Aid from a co-located physical terminal callback, not remote ACK.
      // The earlier dispatch completed synchronously in this fixture.
      if(local==1 || (local==2 && pri==0))fallback(.375);
    }
  }
  assert(w.first==1&&w.independent==1);
  auto sent=w.plant.state("P").bytes_sent_this_epoch;
  std::cout<<diag<<' '<<observed<<' '<<pri<<' '<<fall<<' '<<int(pri+fall==1)<<' '<<sent<<'\n';
 }
}
