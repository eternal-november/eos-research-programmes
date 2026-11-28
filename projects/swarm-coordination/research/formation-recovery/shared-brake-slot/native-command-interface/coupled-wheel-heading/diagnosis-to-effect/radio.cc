#define main prior_radio_replay
#include "staged_replay.inc"
#undef main

struct Receipt {
 World w;
 int old=0,raw=-1,qualified=-1;
 bool good=true;
 explicit Receipt(int cap):w(cap) {
  for(auto id:{"H","Z","O"}){
   auto n=std::make_shared<TeamNode>();n->name=id;n->radio.capacity=8*cap;
   n->radio.pathloss_f=[this](double,auto&,auto&,bool& route){
       route=false;return Power{good?100.:-std::numeric_limits<double>::infinity(),0};};
   w.b.team->emplace(id,n);w.b.endpoints[std::string(id)+":7"]={{id}};
  }
  w.app.callbacks["O:7"]=[this](auto from,auto,auto,auto payload){
   assert(from=="H"&&payload=="SIDE");++old;
  };
  w.app.callbacks["Q:7"]=[this](auto from,auto,auto,auto payload){
   assert((from=="H"||from=="Z")&&payload.size()==1);
   const auto v=payload[0];raw=(v=='B'||v=='b');
   if(v=='A'||v=='B')qualified=raw;else assert(v=='a'||v=='b');
  };
 }
 void send(std::string f,std::string t,std::string p,double stamp){
  now=stamp;w.b.incomingMsgs.push_back({f,t,p});
  w.b.DispatchMessages();assert(w.b.incomingMsgs.empty());
 }
};
void* setup_radio(int cap,double stamp) {
 auto* r=new Receipt(cap);r->send("H","O","SIDE",stamp);assert(r->old==1);return r;
}
int note_radio(void* radio,int w,int alternate,int mode,double at){
 auto& r=*static_cast<Receipt*>(radio);
 r.good=mode!=2;
 r.send(alternate?"Z":"H","Q",std::string(1,char((mode==1?'a':'A')+w)),at);
 return r.qualified;
}
int raw_radio(void* r){return static_cast<Receipt*>(r)->raw;}
int exact_old_progress(void* r){return static_cast<Receipt*>(r)->old;}
int charged_radio(void* r){
 int count=0;
 auto* x=static_cast<Receipt*>(r);
 for(auto id:{"H","Z"})
 for(auto [t,n]:x->w.state(id).bytes_sent)
  if(t==now)count+=n;
 return count;
}
void end_radio(void* r){delete static_cast<Receipt*>(r);}
