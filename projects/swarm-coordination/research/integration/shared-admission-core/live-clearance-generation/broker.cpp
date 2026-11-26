#define main inherited_radio_main
#include "replay.cpp"
#undef main

struct Live{
 World w;
 unsigned cap;
 std::map<std::string,unsigned> calls;
 Live(unsigned c):w(c),cap(c){
  for(std::string s:{"Far","Side"}){
   auto n=std::make_shared<TeamNode>();
   n->name=s;n->radio=w.b.team->at("P")->radio;
   w.b.team->emplace(s,n);
  }
  bind("probe","Base");bind("owed","Base");bind("unrelated","Far");
 }
 void bind(std::string name,std::string dst){
  calls[name]=0;
  w.b.endpoints[name+":7"]={{dst}};
  w.app.callbacks[name+":7"]=[&,name](auto,auto,auto,const auto& payload){
   assert(!payload.empty());++calls[name];
  };
 }
 template<class M> static unsigned used(const M& xs,int tick){
  unsigned n=0;
  for(auto [t,b]:xs)if(t>=tick/4.0-1.)n+=b;
  return n;
 }
 void status(int tick){
  std::cout<<used(w.state("P").bytes_sent,tick)<<' '
    <<used(w.state("Q").bytes_sent,tick)<<' '
    <<used(w.state("Base").bytes_received,tick)<<std::endl;
 }
 void send(int tick,std::string s,std::string name,unsigned n,bool clear){
  now=tick/4.0;
  auto b=calls.at(name); w.path_available=clear;
  w.b.incomingMsgs.push_back({s,name,std::string(n,'d')});
  w.b.DispatchMessages();
  assert(w.b.incomingMsgs.empty());w.path_available=true;
  std::cout<<(calls[name]-b)<<std::endl;
 }
};

int main(){
 std::unique_ptr<Live> live;
 std::string cmd;
 while(std::cin>>cmd){
  if(cmd=="reset"){
   unsigned cap;std::cin>>cap;
   live=std::make_unique<Live>(cap);
   std::cout<<"ok"<<std::endl;
  }else if(cmd=="sample"){
   int t;std::cin>>t;
   live->status(t);
  }else if(cmd=="send"){
   int t;unsigned bytes;bool ok;std::string s,d;
   std::cin>>t>>s>>d>>bytes>>ok;
   live->send(t,s,d,bytes,ok);
  }else{assert(false);}
 }
}
