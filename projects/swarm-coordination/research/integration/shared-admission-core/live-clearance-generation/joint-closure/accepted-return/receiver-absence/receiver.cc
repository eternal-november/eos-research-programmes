using namespace vda5050_core;
using namespace vda5050_core::client::adapter;
types::Order edge(unsigned ver,std::string from,unsigned pos,std::string to,bool rel){
  return {"cell-issue:7",ver,{{from,pos,true,"",{}},{to,pos+2,rel,"",{}}},
     {{from+to,pos+1,rel,from,to,"",std::nullopt}},""};
}
int main(){
  int lowerFirst, stitched;
  while(std::cin>>lowerFirst>>stitched){
    Adapter::Implementation a;
    a.subscribe_orders();
    auto input=[&](types::Order o){
      a.sm.requested=false;
      a.bus.order(std::move(o),std::nullopt);
      assert(a.sm.requested);
    };
    input(edge(0,"A",0,"B",false));
    a.publish_state();assert(a.bus.latest->order_update_id==0);
    if(lowerFirst)input(edge(1,"A",0,"B",true));
    input(edge(2,"A",0,"X",true));
    // A publish request is not itself published state.
    assert(a.bus.latest->order_update_id==0);
    if(!lowerFirst)input(edge(1,"A",0,"B",true));
    if(stitched&&lowerFirst) input(edge(3,"B",2,"X",true));
    a.publish_state();
    const auto& o=a.active_order.order->order;
    const auto& report=*a.bus.latest;
    assert(a.sm.errs>=1 && report.order_update_id==o.order_update_id);
    std::cout<<report.order_id<<' '<<report.order_update_id<<' '
      <<o.nodes.front().node_id<<' '<<o.edges.front().edge_id<<' '
      <<report.edge_states.size()<<std::endl;
  }
}
