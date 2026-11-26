#define main inherited_radio_main
#include "replay.cpp"
#undef main

struct G {
 World w;
 unsigned cap;
 std::map<std::string,unsigned> calls;
 G(unsigned c):w(c),cap(c){
  for(std::string s:{"R0","R1","LateCrew","SideDock"}){
   auto n=std::make_shared<TeamNode>();
   n->name=s;n->radio=w.b.team->at("P")->radio;
   w.b.team->emplace(s,n);
  }
 }
 void bind(std::string label,std::string dst){
  calls[label]=0;
  w.b.endpoints[label+":7"]={{dst}};
  w.app.callbacks[label+":7"]=[this,label](auto,auto,auto,const auto&){++calls[label];};
 }
 bool run(std::string s,std::string name,unsigned bytes,int cut,bool ok=true){
  const auto pre=calls.at(name);
  w.path_available=ok; now=cut/8.0;
  w.b.incomingMsgs.push_back({s,name,std::string(bytes,'r')});
  w.b.DispatchMessages();
  assert(w.b.incomingMsgs.empty()); w.path_available=true;
  return calls[name]>pre;
 }
 template<class L> static unsigned used(const L& ds,int cut){
  unsigned out=0;
  for(auto [t,b]:ds)if(t>=cut/8.0-1.0)out+=b;
  return out;
 }
 bool room(std::string s,std::string dst,unsigned bytes,int cut){
  return used(w.state(s).bytes_sent,cut)+bytes<=cap &&
         used(w.state(dst).bytes_received,cut)+bytes<=cap;
 }
};

int main(){
 unsigned mode,cap,a,b,share,rx,erase,first,due,c,d;
 while(std::cin>>mode>>cap>>a>>b>>share>>rx>>erase>>first>>due>>c>>d){
  G g(cap);
  std::string dest=rx?"R1":"R0";
  g.bind("old",dest);g.bind("peer","R1");g.bind("third","R1");g.bind("side","SideDock");
  int delivery=-1,nativeAttempt=-1;
  unsigned side=0,burn=0;
  if(mode<=1){
   assert(g.run(share?"P":"Q","peer",b,0,!erase)==!erase);
   assert(g.used(g.w.state(share?"P":"Q").bytes_sent,0)==b);
   assert(g.used(g.w.state("R1").bytes_received,0)==(erase?0:b));
   // first is *local receipt* of the named physical authority, not its
   // occurrence on another source clock. No valid receipt by due => no act.
   int from=mode==0?first:std::max(first,9u);
   for(int t=from;t<=static_cast<int>(due);++t){
    if(!g.room("P",dest,a,t))continue;
    nativeAttempt=t;
    assert(g.run("P","old",a,t));
    delivery=t;
    break;
   }
  }else{
   assert(first==10);
   const bool stale=g.room("P",dest,a,first);
   assert(g.run("LateCrew","third",c,first));
   if(mode==2){
    assert(stale);
    nativeAttempt=first;
    if(g.run("P","old",a,first))delivery=first;
    burn=g.used(g.w.state("P").bytes_sent,first);
    side=g.run("P","side",d,first);
   }else{
    // Independently owed co-due side load uses the actual writer first.
    side=g.run("P","side",d,first);
    assert(side);
    for(int t=first;t<=static_cast<int>(due);++t){
     if(!g.room("P",dest,a,t))continue;
     nativeAttempt=t;
     assert(g.run("P","old",a,t));
     delivery=t;
     burn=g.used(g.w.state("P").bytes_sent,t)-(t<=18?d:0);
     break;
    }
   }
  }
  std::cout<<delivery<<' '<<nativeAttempt<<' '<<side<<' '<<burn<<'\n';
 }
}
