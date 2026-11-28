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

void* rmf_start();
void rmf_exit_ready(void*);
void rmf_exit(void*);
void rmf_retire(void*);
void rmf_renew(void*);
void rmf_unrelated(void*);
bool rmf_permit(void*);
bool rmf_clear(void*);
bool rmf_unrelated_done(void*);
void rmf_end(void*);

int main(){
 for(int vdone:{1,2,3})for(int exit:{1,2,3})for(int retire:{0,1})for(int horizon:{1,2,3,4})
 for(int phase:{0,1})for(int mode:{0,1,2,3,4}){
   auto* r=rmf_start();
   Run a;
   const auto A=n("A",0,true,0);
   const auto B=n("B",2,true,1);
   a.send(route(1,A,B));
   a.tick();a.finish();a.tick();
   assert(a.dealt.size()==2&&a.dealt[1].sequence_id()==2);
   a.send(route(2,B,n("C",4,true,2)));
   assert(a.s.greatest_accepted->order_update_id==2);
   bool cached=false,guarded=false,lawful=true;
   int at=0;
   unsigned matrix=0;
   for(int t=1;t<=4;t++){
    if(t==1){rmf_exit_ready(r);rmf_unrelated(r);}
    if(t==exit)rmf_exit(r); // witnessed original exit in the civil fixture
    if(retire&&t==2&&phase==0)rmf_retire(r); // replacement effect path loses live access
    if(retire&&t==3)rmf_renew(r);
    if(t==vdone)a.finish(); // upstream B work is separately completed
    a.tick();
    const bool c=a.dealt.size()==3&&a.dealt.back().sequence_id()==4
                          &&a.handling.back().version==2&&a.view(2)==2;
    const bool p=rmf_permit(r),f=rmf_clear(r);
    cached=cached||p;
    if(retire&&t==2&&phase==1)rmf_retire(r);
    const bool effect=rmf_permit(r);
    matrix=16*matrix+8*c+4*p+2*effect+f;
    if(t>horizon||at)continue;
    if(mode==0)guarded=a.s.greatest_accepted->order_update_id==2&&cached;
    if(mode==1)guarded=c&&cached;
    if(mode==2)guarded=c&&cached&&f;
    if(mode==3)guarded=c&&p&&f;
    if(mode==4)guarded=c&&effect&&f;
    if(guarded){
     at=t;
     lawful=c&&effect&&f;
     // Physical crossing is a single stipulated interval; no re-entry
     // after witnessed incumbent exit. Old work continues independently.
    }
   }
   assert(rmf_unrelated_done(r));
   if(mode==4)assert(lawful);
   cout<<vdone<<" "<<exit<<" "<<retire<<" "<<horizon<<" "<<phase<<" "<<mode
       <<" "<<at<<" "<<lawful<<" "<<matrix<<"\n";
   rmf_end(r);
 }
}
