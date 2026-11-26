#define TIMED_SOURCE_LIBRARY
#include "driver.cpp"

int main(){
  int first,branch,no_request,no_cue,choice;
  while(std::cin>>first>>branch>>no_request>>no_cue>>choice){
    now=0.;
    TimedSource t(.5);
    for(auto name:{"Scout","Mule","Gate","Source","Staff"}){
      auto n=std::make_shared<TeamNode>();
      n->name=name;
      n->radio=t.plant.b.team->at("P")->radio;
      t.plant.b.team->emplace(name,n);
    }
    unsigned req=0,handover=0,base=0,other=0,views=0;
    int actual=-1;
    bool has_probe=(first==2||first==3);
    t.bind("GateRequest","Gate",req);
    t.bind("Cue","Mule",views);
    t.bind("Report","Mule",handover);
    t.bind("BaseEffect","Base",base);
    t.bind("Concurrent","Far",other);
    t.plant.app.callbacks["Cue:7"]=[&](auto,auto,auto,const auto& data) {
      assert(data=="u" || data=="g");
      actual=(data=="g");
      ++views;
    };
    if(has_probe)t.dispatch({"Staff","GateRequest",1,0.,false},no_request);
    const int pause=int(first==2 && req);
    bool active=has_probe?req!=0:true;
    auto read=[&](){
      if(!has_probe||!req)return;
      now=1/8.;
      t.plant.path_available=!no_cue;
      t.plant.b.incomingMsgs.push_back({"Source","Cue",branch?"g":"u"});
      t.plant.b.DispatchMessages();
      assert(t.plant.b.incomingMsgs.empty());
      t.plant.path_available=true;
    };
    const bool inline_check=(choice<0);
    if(inline_check){
      std::cout<<"hold "<<pause<<std::endl;
      int go=-1;
      assert(bool(std::cin>>go)&&go==1);
    }
    read();
    if(inline_check){
      std::cout<<"view "<<actual<<std::endl;
      assert(bool(std::cin>>choice)&&choice>=0&&choice<=2);
    }
    // Fixed movement branches can deliver only along their allowed pose;
    // the variable choice is feasible from J/K only. Index 2 retreats.
    bool legal=first==0?choice==0:first==1?choice==1:active&&choice<=1;
    if(legal){
      t.dispatch({"Scout","Report",2,2/8.,true},choice!=branch);
      if(handover)t.dispatch({"Mule","BaseEffect",2,3/8.,true});
    }
    t.dispatch({"Independent","Concurrent",1,4/8.,true});
    assert(t.plant.state("Staff").bytes_sent_this_epoch==int(has_probe));
    assert(t.plant.state("Source").bytes_sent_this_epoch==int(has_probe&&req));
    assert(t.plant.state("Scout").bytes_sent_this_epoch==2*int(legal));
    assert(t.plant.state("Mule").bytes_sent_this_epoch==2*int(handover));
    std::cout<<int(req)<<' '<<pause<<' '<<actual<<' '<<base<<' '<<other
             <<' '<<int(legal)<<' '<<views<<'\n';
  }
}
