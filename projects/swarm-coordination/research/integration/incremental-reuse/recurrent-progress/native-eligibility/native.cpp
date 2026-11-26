#define main inherited_replay_main
#include "replay.cpp"
#undef main

struct Step {std::string src,dst; unsigned bytes; double time; bool path=true;};

struct Fixture{
 World w;
 std::map<std::string,unsigned> got;
 Fixture(unsigned cap):w(cap){
  for(std::string name:{"Alt","Extra","Far"}){
   auto n=std::make_shared<TeamNode>();
   n->name=name;
   n->radio=w.b.team->at("P")->radio;
   w.b.team->emplace(name,n);
  }
  bind("Duty","Base");bind("Tx","Alt");bind("Rx","Base");
  bind("Both","Base");bind("Neither","Alt");bind("Side","Far");
 }
 void bind(std::string app,std::string phys){
  got[app]=0;
  w.b.endpoints[app+":7"]={{phys}};
  w.app.callbacks[app+":7"]=[this,app](auto,auto,auto,const auto&){++got[app];};
 }
 std::string endpoint(const Step& s){return w.b.endpoints.at(s.dst+":7").at(0).address;}
 template <class Ledger> static unsigned used(const Ledger& ds,double t){
  unsigned n=0;
  for(auto [z,k]:ds)if(z>=t-1.0)n+=k;
  return n;
 }
 bool eligible(const Step& s){
  auto& tx=w.state(s.src);auto& rx=w.state(endpoint(s));
  unsigned cap=w.b.team->at(s.src)->radio.capacity/8;
  return s.path && used(tx.bytes_sent,s.time)+s.bytes<=cap
      && used(rx.bytes_received,s.time)+s.bytes<=cap;
 }
 bool dispatch(const Step& s){
  w.path_available=s.path;
  auto old=got.at(s.dst);
  now=s.time;
  w.b.incomingMsgs.push_back({s.src,s.dst,std::string(s.bytes,'c')});
  w.b.DispatchMessages();
  assert(w.b.incomingMsgs.empty());
  w.path_available=true;
  return got.at(s.dst)>old;
 }
};

int main(){
 unsigned cap,s,r,mode,hold,erased,lost;
 while(std::cin>>cap>>s>>r>>mode>>hold>>erased>>lost){
  std::string src=(mode&1)?"P":"Q";
  std::string dst=std::vector<std::string>{"Neither","Tx","Rx","Both"}.at(mode);
  Fixture f(cap);
  std::vector<Step> history;
  unsigned seed=0,attempt=0,admitted=0,other=0,branches=0;
  auto qualify=[&](const Step& duty){
   auto E=f.eligible(duty);
   Fixture fork(cap);
   for(const auto& z:history)fork.dispatch(z);
   assert(E==fork.dispatch(duty));++branches;
   return E;
  };
  for(unsigned i=0;i<4;++i){
   Step duty={"P","Duty",s,2.*i};
   if(qualify(duty))++seed;
   assert(f.eligible(duty));
   Step rival={src,dst,r,2.*i+.5,!erased};
   // 0 = none; 1 = until actual use; 2 = exclusive expiry at rival;
   // 3 = expiry one eighth of a second after this rival.
   const auto expires=2.*i+(hold==2?.5:.625);
   const bool active=hold==1 || (hold>=2 && rival.time<expires);
   const unsigned tx=Fixture::used(f.w.state(duty.src).bytes_sent,rival.time);
   const unsigned rx=Fixture::used(f.w.state(f.endpoint(duty)).bytes_received,rival.time);
   const bool budget = tx+s+(mode&1?r:0)<=cap && rx+s+(mode&2?r:0)<=cap;
   const bool allow=!active || budget;
   if(allow){ admitted+=f.dispatch(rival);history.push_back(rival); }
   duty.time=2.*i+.75;
   duty.path=!lost;
   if(qualify(duty))++attempt;
   Step side={"Extra","Side",1,2.*i+1.0};
   other+=f.dispatch(side);history.push_back(side);
  }
  assert(!f.got.at("Duty"));
  std::cout<<seed<<' '<<attempt<<' '<<admitted<<' '<<other<<' '<<branches<<'\n';
 }
}
