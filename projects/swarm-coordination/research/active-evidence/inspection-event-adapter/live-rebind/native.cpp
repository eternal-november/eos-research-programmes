#define TIMED_SOURCE_LIBRARY
#include "driver.cpp"

int main(){
  int failed,receipt,channel;
  while(std::cin>>failed>>receipt>>channel){
    now=0;
    TimedSource v(.5);
    unsigned command=0;
    for(auto id:{"ScoutLink","GateLink"}){
       auto n=std::make_shared<TeamNode>();
       n->name=id;n->radio=v.plant.b.team->at("P")->radio;
       v.plant.b.team->emplace(id,n);
    }
    v.bind("ScopedCommand","GateLink",command);
    v.dispatch(v.preceding);
    v.dispatch({"Independent","Other",1,.125,false});
    assert(v.acquire(v.version));
    const double when=receipt/10.0;
    bool rebind=false;
    auto use=[&](){
      if(channel>0){
        v.dispatch({"ScoutLink","ScopedCommand",1,when,false},channel==2);
        if(!command)return;
      }
      if(when>=.75)return;
      if(v.amend(true,true))rebind=true;
      else if(v.cancel_optional()){
        assert(v.amend(true,true));rebind=true;
      }
    };
    if(receipt>=0 && when<.5) use();
    if(v.reserved)v.execute_new(false);
    if(receipt>=0 && when>=.5 && when<.75) use();
    // This is the family's declared cause law (not RF propagation modeling).
    const bool no_path=(failed==!rebind);
    v.dispatch(v.tail,no_path);
    if(receipt>=0 && when>=.75)use();
    assert(v.first==1&&v.independent==1);
    std::cout<<v.first<<' '<<v.last<<' '<<v.optional<<' '<<v.independent<<' '
             <<int(rebind)<<' '<<command<<'\n';
  }
}
