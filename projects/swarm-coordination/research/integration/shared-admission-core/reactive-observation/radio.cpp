#define TIMED_SOURCE_LIBRARY
#include "driver.cpp"

int main(){
    int kind,request_erase,reply_erase,reply_late,tx_alias,rx_alias,
        clear,channel,optional,answer;
    while(std::cin>>kind>>request_erase>>reply_erase>>reply_late
                   >>tx_alias>>rx_alias>>clear>>channel>>optional>>answer){
      now=0.;
      TimedSource v(9/24.);
      for (auto key: {"ProbeSender","ProbeOwner","ReceiptSender","Control"}) {
        auto node=std::make_shared<TeamNode>();
        node->name=key;
        node->radio=v.plant.b.team->at("P")->radio;
        v.plant.b.team->emplace(key,node);
      }
      unsigned request=0, reply=0, carry_on=0;
      int received_clear=-1;
      v.bind("Request","ProbeOwner",request);
      v.bind("CarryOn","Far",carry_on);
      v.bind("Reply",rx_alias?"Base":"Control",reply);
      v.plant.app.callbacks["Reply:7"]=[&](auto,auto,auto,const auto& data){
        assert(data=="c!"||data=="o!");
        received_clear=(data=="c!");
        ++reply;
      };
      v.dispatch(v.preceding);
      v.dispatch({"Independent","Other",1,.125,false});
      if(optional)v.dispatch(v.fresh,true);
      unsigned req_spent=0,reply_spent=0;
      if(kind){
        v.dispatch({"ProbeSender","Request",1,10/24.,false},request_erase);
        req_spent=v.plant.state("ProbeSender").bytes_sent_this_epoch;
      }
      const bool exchange=(clear<0);
      if(exchange) {
        std::cout<<"query "<<request<<' '<<req_spent<<std::endl;
        const bool ok=bool(std::cin>>clear>>channel);
        assert(ok&&(clear==0||clear==1)&&(channel==0||channel==1));
      }
      auto respond=[&](){
        if(!request)return;
        now=(reply_late?16:12)/24.;
        std::string from=tx_alias?"P":"ReceiptSender";
        size_t before=v.plant.state(from).bytes_sent_this_epoch;
        v.plant.path_available=!reply_erase;
        v.plant.b.incomingMsgs.push_back({from,"Reply",clear?"c!":"o!"});
        v.plant.b.DispatchMessages();
        assert(v.plant.b.incomingMsgs.empty());
        v.plant.path_available=true;
        reply_spent=v.plant.state(from).bytes_sent_this_epoch-before;
      };
      if(!reply_late)respond();
      int view=received_clear;
      if(exchange){
        std::cout<<"view "<<view<<std::endl;
        assert(bool(std::cin>>answer));
      }
      if(answer>=0) {
        const auto key=answer?"Q":"P";
        const auto dest=answer?"Second":"Base";
        v.plant.b.endpoints["OldTail:7"]={{dest}};
        bool available=answer?channel:clear;
        if(available)v.dispatch({key,"OldTail",2,15/24.,true});
      }
      if(reply_late)respond();
      v.dispatch({"Independent","CarryOn",1,17/24.,false});
      std::cout<<request<<' '<<reply<<' '<<req_spent<<' '<<reply_spent
               <<' '<<view<<' '<<v.last<<' '<<v.first<<' '<<v.independent<<' '<<carry_on<<'\n';
    }
}
