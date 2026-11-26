#define TIMED_SOURCE_LIBRARY
#include "driver.cpp"

int main() {
  int paid,notice,loss,action;
  while(std::cin>>paid>>notice>>loss>>action) {
    now=0;
    TimedSource v(.375);
    auto add=[&](std::string k) {
      auto n=std::make_shared<TeamNode>();
      n->name=k;
      n->radio=v.plant.b.team->at("P")->radio;
      v.plant.b.team->emplace(k,n);
    };
    for(auto k:{"RelayA","RelayB","Owner","Control","Gate"})add(k);
    unsigned first=0,finish=0,mule=0,applied=0,extra=0,reply=0,work=0;
    int view=-1,done=-1;
    unsigned switch_read=0;
    bool via_b=false;
    v.bind("Orig","Base",first);
    v.bind("Mule","RelayA",mule);
    v.bind("Final","Base",finish);
    v.bind("Work","Far",work);
    v.bind("Receipt","Control",reply);
    v.bind("Switch","Q",switch_read);
    v.plant.app.callbacks["Switch:7"]=[&](auto,auto,auto,const auto& text){
      assert(text=="a"||text=="b");
      via_b=text=="b";
      ++switch_read;
    };
    v.plant.app.callbacks["Receipt:7"]=[&](auto,auto,auto,const auto& text){
      assert(text=="1"||text=="0"||text=="s");
      view=text=="s"?-1:text=="1";
      ++reply;
    };
    v.dispatch({"P","Orig",2,0.,true});
    assert(first==1);
    // Authored application transition after the native receive.
    if(paid) {applied=1;done=1;}
    // No application ACK is returned on the old topic. A separate local
    // terminal signal may carry current provenance before the decision.
    auto qualify=[&](int cut,bool stale,bool erase){
      now=cut/8.;
      std::string bit=stale?"s":paid?"1":"0";
      v.plant.path_available=!erase;
      v.plant.b.incomingMsgs.push_back({"Owner","Receipt",bit});
      v.plant.b.DispatchMessages();
      assert(v.plant.b.incomingMsgs.empty());
      v.plant.path_available=true;
    };
    if(notice!=2)qualify(2,notice==3,notice==1);
    int observed=view;
    if(action<0) {
      std::cout<<"terminal "<<observed<<std::endl;
      assert(bool(std::cin>>action) && action>=0 && action<=4);
    }
    if(notice==2)qualify(4,false,false);
    auto send=[&](const std::string& who,int t,bool erased){
        v.dispatch({who,"Final",2,t/8.,true},erased);
        extra+=2; // scheduled bytes attempted, not counted independently as PHY debit
        if(finish&&!applied){applied=1;done=t;}
    };
    if(action==0 || (action==4&&observed!=1))send("P",7,false);
    if(action==1)send("P",5,false);
    if(action==2 || action==3) {
      // Matched late choice: fallback B at the contact-loss cut,
      // also available in the established-policy extension.
      // Option 3 suppresses resend after preparation if receiver
      // already recognizes the report: zero duplicate traffic.
      now=4/8.;
      v.plant.path_available=(loss!=3);
      v.plant.b.incomingMsgs.push_back({"Gate","Switch",(loss==1||loss==3)?"b":"a"});
      v.plant.b.DispatchMessages();
      assert(v.plant.b.incomingMsgs.empty());
      v.plant.path_available=true;
      if(!(action==3&&applied)) {
        const std::string to=via_b?"RelayB":"RelayA";
        v.plant.b.endpoints["Mule:7"]={{to}};
        v.dispatch({"Q","Mule",2,5/8.,true},loss==2||((loss==1||loss==3)&&!via_b));
        extra+=2;
        if(mule)send(to,6,false);
      }
    }
    v.dispatch({"Independent","Work",1,8/8.,true});
    const auto p=v.plant.state("P").bytes_sent_this_epoch-2;
    const auto q=v.plant.state("Q").bytes_sent_this_epoch;
    const auto m=v.plant.state("RelayA").bytes_sent_this_epoch+v.plant.state("RelayB").bytes_sent_this_epoch;
    assert(p+q+m==extra);
    assert(v.plant.state("Owner").bytes_sent_this_epoch==1);
    assert(v.plant.state("Gate").bytes_sent_this_epoch==unsigned(action==2||action==3));
    std::cout<<first<<' '<<observed<<' '<<done<<' '<<applied<<' '<<extra
             <<' '<<mule<<' '<<finish<<' '<<work<<' '<<reply<<' '<<switch_read<<'\n';
  }
}
