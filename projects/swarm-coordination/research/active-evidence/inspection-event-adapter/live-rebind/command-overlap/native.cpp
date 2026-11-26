#define TIMED_SOURCE_LIBRARY
#include "driver.cpp"
int main(){
 int s,r,b,drop;
 while(std::cin>>s>>r>>b>>drop){
  now=0;
  TimedSource v(.5);
  unsigned command=0;
  for(auto id:{"ScoutLink","GateLink"}){
    auto n=std::make_shared<TeamNode>();
    n->name=id;n->radio=v.plant.b.team->at("P")->radio;
    v.plant.b.team->emplace(id,n);
  }
  v.bind("ScopedCommand",r?"Base":"GateLink",command);
  v.dispatch(v.preceding);v.dispatch({"Independent","Other",1,.125,false});
  assert(v.acquire(v.version));
  v.dispatch({s?"P":"ScoutLink","ScopedCommand",static_cast<unsigned>(b),.4,false},drop);
  auto tx=v.plant.state("P").bytes_sent_this_epoch;
  auto rx=v.plant.state("Base").bytes_received_this_epoch;
  bool rebind=false;
  if(command){
    Job amended=v.tail;amended.src="P";
    if(v.law(amended,"Base",false)){
      assert(v.cancel_optional());assert(v.amend(true,true));rebind=true;
    }
  }
  if(v.reserved)v.execute_new(false);
  v.dispatch(v.tail,!rebind);
  assert(v.first==1&&v.independent==1);
  std::cout<<command<<' '<<tx<<' '<<rx<<' '<<v.last<<' '
           <<v.optional<<' '<<int(rebind)<<'\n';
 }
}
