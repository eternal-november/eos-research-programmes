#define main upstream_replay_main
#include "subt/replay.cpp"
#undef main
int main(){
 World w(5);
 unsigned new_done=0, unrelated=0, old_buffered=0;
 std::string old_payload="ooo", rescue_copy;
 w.app.callbacks["Base:7"]=[&](auto,auto,auto,const auto& v){
   assert(v=="rrr");++new_done;
 };
 w.app.callbacks["Q:7"]=[&](auto,auto,auto,const auto& v){rescue_copy=v;};
 w.app.callbacks["Cache:7"]=[&](auto,auto,auto,const auto& v){
   assert(v==old_payload);++old_buffered;
 };
 w.app.callbacks["OtherSink:7"]=[&](auto,auto,auto,const auto& v){
   assert(v=="uuu");++unrelated;
 };
 for(auto n:{"Other","OtherSink","Cache"}){
   auto t=std::make_shared<TeamNode>(*w.b.team->at("P"));
   t->name=n;w.b.team->emplace(n,t);
 }
 for(auto n:{"OtherSink","Cache"})
   w.b.endpoints[std::string(n)+":7"].push_back({n});
 auto sender=[](char z){assert(z=='L'||z=='R');return z=='L'?"P":"Q";};
 auto push=[&](std::string s,std::string dst,std::string v){
   w.b.incomingMsgs.push_back({s,dst,v});
 };
 now=-2;
 push("P","Q","rrr");w.b.DispatchMessages();
 assert(rescue_copy=="rrr");
 char op,z;
 while(std::cin>>op>>z){
   now=1;
   if(op=='P'){
     assert(w.b.incomingMsgs.empty());push(sender(z),"Cache",old_payload);
     assert(w.b.incomingMsgs.size()==1);
   }else if(op=='F'){
     assert(w.b.incomingMsgs.size()==1);
   }else if(op=='X'){
     assert(w.b.incomingMsgs.size()==1);w.b.incomingMsgs.clear();
   }else if(op=='O'){
     assert(w.b.incomingMsgs.size()==1);w.b.DispatchMessages();
   }else{
     assert(op=='C'&&w.b.incomingMsgs.empty());
     if(z!='-')push(sender(z),"Base","rrr");
     push("Other","OtherSink","uuu");w.b.DispatchMessages();
   }
   char scope=w.b.incomingMsgs.empty()?'-':
     w.b.incomingMsgs.front().src_address()=="P"?'L':'R';
   std::cout<<scope<<' '<<new_done<<' '<<unrelated<<' '<<old_buffered<<' '
            <<!old_payload.empty()<<std::endl;
 }
}
