#define TIMED_SOURCE_LIBRARY
#include "driver.cpp"

int main(){
 int blocked,partition,closure,notice,pose;
 while(std::cin>>blocked>>partition>>closure>>notice>>pose){
  now=0.;
  TimedSource v(.5);
  for(auto name:{"Scout","Mule","CueOwner"}){
    auto node=std::make_shared<TeamNode>();
    node->name=name; node->radio=v.plant.b.team->at("P")->radio;
    v.plant.b.team->emplace(name,node);
  }
  unsigned read=0,hop=0,at_base=0,unrelated=0;
  int seen=-1, delivered_at=-1;
  v.bind("Cue","Mule",read);
  v.bind("Rendezvous","Mule",hop);
  v.bind("Delivered","Base",at_base);
  v.bind("OtherWork","Far",unrelated);
  v.plant.app.callbacks["Cue:7"]=[&](auto,auto,auto,const auto& payload){
    assert(payload=="u"||payload=="g"||payload=="!");
    seen=payload=="!"?-1:payload=="g";
    ++read;
  };
  auto qualify=[&](int t,bool erased,bool stale) {
    now=t/8.;
    v.plant.path_available=!erased;
    v.plant.b.incomingMsgs.push_back({"CueOwner","Cue",stale?"!":(closure^(notice==4))?"g":"u"});
    v.plant.b.DispatchMessages();
    assert(v.plant.b.incomingMsgs.empty());
    v.plant.path_available=true;
  };
  if(notice!=2)qualify(1,notice==1,notice==3);
  const int actual_view=seen;
  if(pose<0) {
     std::cout<<"view "<<actual_view<<std::endl;
     assert(bool(std::cin>>pose)&&pose>=0&&pose<=2);
  }
  if(!partition){
    v.dispatch({"Scout","Delivered",2,1/8.,true});
    if(at_base)delivered_at=1;
  }else if(!blocked)v.dispatch({"Scout","Rendezvous",2,1/8.,true});
  if(notice==2)qualify(2,false,false);
  if(partition&&blocked&&pose<=1)
    v.dispatch({"Scout","Rendezvous",2,2/8.,true},closure!=pose);
  if(hop){
    v.dispatch({"Mule","Delivered",2,3/8.,true});
    if(at_base)delivered_at=3;
  }
  v.dispatch({"Independent","OtherWork",1,4/8.,true});
  assert(v.plant.state("CueOwner").bytes_sent_this_epoch==1);
  std::cout<<actual_view<<' '<<read<<' '<<hop<<' '<<at_base<<' '<<unrelated<<' '<<delivered_at<<' '
           <<v.plant.state("Scout").bytes_sent_this_epoch<<' '
           <<v.plant.state("Mule").bytes_sent_this_epoch<<'\n';
 }
}
