#define TIMED_SOURCE_LIBRARY
#include "driver.cpp"
enum class E { Req, Primary, Receipt, Fallback };

int main(){
 int rt,delay,tie,reqdrop,replydrop,senderAlias,recvAlias,H,primaryGood,cert,policy;
 while(std::cin>>rt>>delay>>tie>>reqdrop>>replydrop>>senderAlias>>recvAlias>>H
               >>primaryGood>>cert>>policy){
  assert(!cert||!replydrop);
  now=0;
  TimedSource v(.5);
  for(auto& [_,n]:*v.plant.b.team)n->radio.capacity=8*(H+2);
  auto add=[&](std::string name){
    auto n=std::make_shared<TeamNode>();
    n->name=name;n->radio=v.plant.b.team->at("P")->radio;
    v.plant.b.team->emplace(name,n);
  };
  for(auto n:{"Controller","QueueOwner","Returner","FallbackConsumer"})add(n);
  unsigned req=0,receipt=0,primary=0,fallback=0;
  v.bind("Request","QueueOwner",req);
  v.bind("RevokeProof",recvAlias?"Base":"FallbackConsumer",receipt);
  v.bind("OldPrimary","Second",primary);
  v.bind("OldFallback","Base",fallback);
  v.dispatch(v.preceding);
  v.dispatch({"Independent","Other",1,.125,false});
  bool revoked=false,attempted=false;
  unsigned liveTX=0,liveRX=0;
  struct Item{int t,order;E e;};
  std::vector<Item> tape{{rt,tie?1:0,E::Req},{9,tie?0:1,E::Primary},
                         {rt+delay,2,E::Receipt},{11,3,E::Fallback}};
  std::sort(tape.begin(),tape.end(),[](auto a,auto b){
      return a.t!=b.t?a.t<b.t:a.order<b.order;
  });
  for(auto event:tape){
    const double t=event.t/20.;
    if(event.e==E::Req){
      v.dispatch({"Controller","Request",1,t,false},reqdrop);
      if(req&&!attempted){
        // Assume a true admitted certificate only when return is reliable
        // in this controlled family. It is not inferred from actual result.
        bool canReturn=cert && rt+delay<=11;
        auto tx=v.plant.state("P").bytes_sent_this_epoch;
        auto rx=v.plant.state("Base").bytes_received_this_epoch;
        auto cap=v.plant.b.team->at("P")->radio.capacity;
        bool pays=8*(tx+2+2*senderAlias)<=cap&&8*(rx+2+2*recvAlias)<=cap;
        // policy 0: cancel then hope; 1: require qualification first.
        revoked=policy==0 || (canReturn && pays);
      }
    }else if(event.e==E::Primary){
      if(!revoked){
        v.dispatch({"P","OldPrimary",3,t,true},!primaryGood);
        attempted=true;
      }
    }else if(event.e==E::Receipt){
      if(revoked){
        v.dispatch({senderAlias?"P":"Returner","RevokeProof",2,t,false},replydrop);
      }
    }else{
      liveTX=v.plant.state("P").bytes_sent_this_epoch;
      liveRX=v.plant.state("Base").bytes_received_this_epoch;
      if(receipt)v.dispatch({"P","OldFallback",2,t,true});
    }
  }
  assert(v.first==1&&v.independent==1);
  assert(primary+fallback<=1);
  std::cout<<req<<' '<<int(revoked)<<' '<<receipt<<' '<<primary<<' '<<fallback
    <<' '<<int(primary+fallback==1)<<' '<<liveTX<<' '<<liveRX<<' '<<v.independent<<'\n';
 }
}
