#define main inherited_replay_main
#include "subt/replay.cpp"
#undef main

struct Facility {
 World w{5};
 CommsClient gateway;
 bool bad=false, sealed=false, old_paid=false;
 unsigned independent=0;
 bool display_closed=false, scoped_clear=false;
 struct Tail{std::string source,destination,data;unsigned port;char generation;};
 std::vector<Tail> tail;
 char wave='-';
 std::map<std::string,std::string> partial;
 std::string assembled;
 char mode;

 bool old_candidate(const subt::msgs::Datagram& m){
   return m.src_address()=="Q" && m.dst_address()=="Base";
 }

 Facility(char scenario):mode(scenario) {
   for(auto n:{"Bad","Other","OtherSink","OldDock","DebitSink"}){
     auto d=std::make_shared<TeamNode>(*w.b.team->at("P"));
     d->name=n;w.b.team->emplace(n,d);
   }
   for(auto n:{"OtherSink","OldDock","DebitSink"})
     w.b.endpoints[std::string(n)+":7"].push_back({n});
   w.b.pose_update_f=[this](const std::string& n){
      return std::make_tuple(n!="Bad"||!bad,Pose{},now);
   };
   w.b.node.receiver=&gateway;
   gateway.callbacks["OldDock:7"]=[&](auto,auto,auto,const auto& v){assert(v=="ooo");old_paid=true;};
   gateway.callbacks["OtherSink:7"]=[&](auto,auto,auto,const auto& v){if(v=="uuu")++independent;};
   gateway.callbacks["Base:7"]=[&](auto o,auto d,auto port,const auto& v){
       assert(wave=='o'||wave=='n');
       tail.push_back({o,d,v,port,wave});
   };
   w.app.callbacks["Base:7"]=[&](auto o,auto,auto,const auto& v){
       partial[o]=v;
       if(assembled.empty()&&partial.count("P")&&partial.count("Q"))
         assembled=partial["P"]+partial["Q"];
   };
   if(mode=='t'||mode=='p'){
      now=-2;queue_old(); dispatch('o');
      assert(tail.size()==1 && front()==0);
      if(mode=='p')deliver('o');
   }
   now=0;push("P","DebitSink","xxx");dispatch('-');
   w.path_available=(mode!='u');
   push("Q","OldDock","ooo");dispatch('-');
   w.path_available=true;
   assert(old_paid==(mode!='u'));
   if(mode=='q'||mode=='u'){
      queue_old();
      bad=true;dispatch('o');
      assert(front()==1 && count('o')==0);
      bad=false;
   }
 }

 void push(std::string s,std::string d,std::string v){
    w.b.incomingMsgs.push_back({s,d,v});
 }
 void queue_old(){ if(!sealed)push("Q","Base","q"); }
 void dispatch(char g){wave=g;w.b.DispatchMessages();wave='-';}
 size_t front(){
    size_t c=0;
    for(const auto& m:w.b.incomingMsgs) if(old_candidate(m))++c;
    return c;
 }
 size_t count(char g){
    return std::count_if(tail.begin(),tail.end(),[=](const Tail& t){return t.generation==g;});
 }
 void deliver(char g){
    for(auto it=tail.begin();it!=tail.end();){
      const auto& t=*it;
      if(t.generation!=g){++it;continue;}
      subt_msgs::DatagramRos::Request req{t.source,t.destination,t.data,t.port,100};
      subt_msgs::DatagramRos::Response res;
      assert(w.app.OnMessageRos(req,res));
      it=tail.erase(it);
    }
 }
 void close(){
    display_closed=true;
    if(!old_paid)return;
    sealed=true;
    // Authored authority-scoped queue operation. Already emitted messages
    // are not removed from the downstream pending callback outbox.
    auto& in=w.b.incomingMsgs;
    in.erase(std::remove_if(in.begin(),in.end(),
              [&](const auto& m){return old_candidate(m);}),in.end());
 }
 void claim(){std::cout<<sealed<<' '<<front()<<' '<<count('o')<<' '<<old_paid<<std::endl;}
 void final(char decision){
    if(decision=='Y'){
       assert(sealed && front()==0 && count('o')==0 && old_paid);
       partial.clear();scoped_clear=true;
    }
    if(mode=='w')queue_old(); // staged old writer after a publication-only claim
    dispatch('o');deliver('o');
    // Negative control 'X' bypasses the architecture in the fixture only.
    if(decision=='Y'||decision=='X'){
       push("P","Base","ll");push("Q","Base","r");dispatch('n');deliver('n');
    }
    push("Other","OtherSink","uuu");dispatch('-');
    std::cout<<old_paid<<' '<<independent<<' '<<scoped_clear<<' '
             <<(assembled.empty()?"-":assembled)<<std::endl;
 }
};
int main(){
 char mode;std::cin>>mode;Facility f(mode);
 char op;double t;
 while(std::cin>>op>>t){
    now=t;
    if(op=='S')f.close();
    if(op=='A')f.display_closed=true;
    if(op=='D')f.deliver('o');
    if(op=='M')f.claim();
    if(op=='F'){char d;std::cin>>d;f.final(d);}
 }
}
