#define TIMED_SOURCE_LIBRARY
#include "driver.cpp"

int main() {
  int send,share_send,share_receive,optional,erase,prior,block;
  while(std::cin>>send>>share_send>>share_receive>>optional>>erase>>prior>>block) {
    now=0;
    TimedSource v(.375);
    v.dispatch(v.preceding);
    v.dispatch({"Independent","Other",1,.125,false});
    if(prior){
      v.plant.b.endpoints["OldTail:7"]={{"Far"}};
      v.dispatch({"Independent","OldTail",2,8/24.,true});
    }
    if(optional)v.dispatch(v.fresh,erase);
    const auto key=share_send?"P":"Q";
    const auto dest=share_receive?"Base":"Second";
    size_t tx_before=v.plant.state(key).bytes_sent_this_epoch;
    size_t rx_before=v.plant.state(dest).bytes_received_this_epoch;
    v.plant.b.endpoints["OldTail:7"]={{dest}};
    if(send>=0)v.dispatch({key,"OldTail",2,send/24.,true},block);
    std::cout<<v.first<<' '<<v.optional<<' '<<v.last<<' '<<v.independent<<' '
      <<tx_before<<' '<<rx_before<<' '<<v.plant.state(key).bytes_sent_this_epoch<<' '
      <<v.plant.state(dest).bytes_received_this_epoch<<'\n';
  }
}
