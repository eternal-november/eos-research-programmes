#define main inherited_replay_main
#include "subt/replay.cpp"
#undef main
int main(){
 World w(5);
 std::string old_copy, rescue_copy;
 unsigned old_done=0,rescue_done=0, independent=0;
 unsigned old_arrivals=0;bool suppress_duplicate=false;
 std::map<std::string,std::string> fragments;
 for(auto n:{"OldDock","Other","OtherSink"}){
   auto t=std::make_shared<TeamNode>(*w.b.team->at("P"));
   t->name=n;w.b.team->emplace(n,t);
 }
 for(auto n:{"OtherSink","OldDock"})
   w.b.endpoints[std::string(n)+":7"].push_back({n});
 w.app.callbacks["Q:7"]=[&](auto,auto,auto,const auto& payload){
    if(payload=="ooo")old_copy=payload;
    else {assert(payload=="rrr");rescue_copy=payload;}
 };
 w.app.callbacks["OldDock:7"]=[&](auto,auto,auto,const auto& p){assert(p=="ooo");++old_arrivals;if(!suppress_duplicate||old_done==0)++old_done;};
 w.app.callbacks["Base:7"]=[&](auto,auto,auto,const auto& p){assert(p=="rrr");++rescue_done;};
 w.b.endpoints["Reassembly:7"].push_back({"Base"});
 w.app.callbacks["Reassembly:7"]=[&](auto origin,auto,auto,const auto& value){
    const auto data=value.front()=='h'?value.substr(1):value;
    fragments[origin]=data;
    if(fragments.count("P")&&fragments.count("Q")){
      assert(fragments["P"]+fragments["Q"]=="rrr");
      ++rescue_done;
    }
 };
 w.app.callbacks["OtherSink:7"]=[&](auto,auto,auto,const auto& p){assert(p=="uuu");++independent;};
 auto push=[&](std::string s,std::string d,std::string p){w.b.incomingMsgs.push_back({s,d,p});};
 // Physically produce both alternate copies through the selected native broker.
 now=-4;push("P","Q","ooo");w.b.DispatchMessages();
 now=-2;push("P","Q","rrr");w.b.DispatchMessages();
 assert(old_copy=="ooo"&&rescue_copy=="rrr");
 std::cout<<"prep "<<(old_copy=="ooo")<<' '<<(rescue_copy=="rrr")<<std::endl;
 bool started=false;char phase,a,b;double t;
 auto live=[&](const char* name){
   unsigned sum=0;
   for(auto x:w.state(name).bytes_sent)
     if(x.first>=now-1.0)sum+=x.second;
   return sum;
 };
 while(std::cin>>phase>>a>>b>>t){
   now=t;
   if(phase=='A'){
     assert(!started && now==0);
     started=true;w.path_available=(a=='Y');
     push("P","OldDock","ooo");w.b.DispatchMessages();
     assert(w.b.incomingMsgs.empty() && live("P")==3);
     w.path_available=true;
   }else if(phase=='C'||phase=='D'||phase=='F'){
     suppress_duplicate=phase=='D'||phase=='F';
     assert(started && (a=='R'||a=='-'));
     if(a=='R')push("Q","OldDock",old_copy);
     if(phase=='F'){
         assert(a=='R'&&(b=='0'||b=='1'));
         std::string header=b=='1'?"h":"";
         push("P","Reassembly",header+std::string("rr"));
         push("Q","Reassembly",header+std::string("r"));
     }else{
         if(b=='L')push("P","Base","rrr");
         if(b=='R')push("Q","Base",rescue_copy);
     }
     push("Other","OtherSink","uuu");w.b.DispatchMessages();
   }
   std::cout<<phase<<' '<<old_done<<' '<<rescue_done<<' '<<independent<<' '
        <<live("P")<<' '<<live("Q")<<' '<<old_arrivals<<std::endl;
 }
}
