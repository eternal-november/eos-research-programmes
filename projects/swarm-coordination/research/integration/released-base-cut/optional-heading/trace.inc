using namespace vda5050_core;
using namespace vda5050_core::client::adapter;
using namespace std;
optional<double> angle(int n) {
 switch(n){case 0:return nullopt;case 1:return 0.;case 2:return 1.;
 case 3:return std::acos(-1.);case 4:return -std::acos(-1.);}
 assert(false);return nullopt;
}
types::Node n(string name,unsigned seq,bool release,int theta){
 types::NodePosition p;
 p.x=4;p.y=2;p.map_id="inspection";p.theta=angle(theta);
 return {name,seq,release,{},p,nullopt};
}
types::Order route(unsigned id,types::Node a,types::Node b) {
 return {"repair",id,{a,b},{{a.node_id+b.node_id,a.sequence_id+1,b.released,a.node_id,b.node_id}}};
}
struct Run {
 StateManager s;
 Protocol p;
 Adapter::Implementation a;
 vector<NodeRequest> dealt;
 vector<OrderExecution> handling;
 Run(){
  a.state_manager=&s;a.protocol_adapter=&p;
  a.navigation_callback=[&](NodeRequest req,optional<EdgeRequest>,OrderExecution op){
   dealt.push_back(std::move(req));handling.push_back(std::move(op));};
  a.subscribe_orders();
 }
 void send(types::Order o){p.receive(o,nullopt);}
 void tick(){a.process_navigation();}
 void finish(){
  assert(!handling.empty());
  handling.back().finished();
 }
 int view(size_t i) {
  auto th=dealt.at(i).node_position()->theta;
  for(int q=0;q<5;q++)if(angle(q)==th)return q;
  assert(false);return -1;
 }
};
int main(){
 for(int seen:{0,1,2})for(int form:{0,1})
  for(int old:{0,1,2,3,4})for(int changed:{0,1,2,3,4}){
   Run a;
   const auto A=n("A",0,true,0);
   a.send(route(0,A,n("B",2,false,old)));
   a.tick();assert(a.dealt.size()==1&&a.dealt[0].sequence_id()==0);
   a.finish();a.tick();assert(a.dealt.size()==1);
   if(seen)a.send(route(1,A,n("B",2,true,old)));
   if(seen==2){a.tick();assert(a.handling[1].version==1&&a.view(1)==old);}
   if(form==0)a.send(route(2,A,n("B",2,true,changed)));
   else a.send(route(2,n("B",2,true,changed),n("C",4,true,2)));
   const bool accepted=a.s.greatest_accepted->order_update_id==2;
   const bool expect=form==0?!seen:seen&&old==changed;
   assert(accepted==expect);
   if(!accepted)assert(a.s.faults.size()==1);
   a.tick();
   const size_t after=a.dealt.size();
   if(seen||accepted){
    assert(after==2&&a.dealt[1].sequence_id()==2);
    assert(a.view(1)==(seen?old:changed));
    const unsigned expectedVersion=seen==2?1:accepted?2:1;
    assert(a.handling[1].version==expectedVersion);
   }else assert(after==1);
   if(accepted&&form==1){
    const auto past=a.view(1);
    assert(a.handling[1].version==1||seen==1);
    a.finish();a.tick();assert(a.dealt.size()==3&&a.dealt[2].sequence_id()==4);
    assert(a.view(1)==past&&a.view(2)==2&&a.handling[2].version==2);
   }
   cout<<seen<<" "<<form<<" "<<old<<" "<<changed<<" "<<accepted
       <<" "<<(after==2?a.view(1):-1)<<" "
       <<(after==2?int(a.handling[1].version):-1)
       <<" "<<(a.dealt.size()==3?a.view(2):-1)<<"\n";
  }
}
