#define main earlier_compiled_simulator
#include "upstream_replay.cpp"
#undef main
int main(){
 int cap,n;
 while(std::cin>>cap>>n){
   World w(cap);
   for(const char *name : {"E","W"}){
     auto state=std::make_shared<TeamNode>();
     state->name=name;state->radio=w.b.team->at("P")->radio;
     assert(w.b.team->emplace(name,state).second);
   }
   std::vector<std::pair<std::string,std::string>> seen;
   w.app.callbacks["Base:7"]=[&](auto s,auto,auto,auto msg){seen.emplace_back(s,msg);};
   std::cout<<n;
   for(int i=0;i<n;++i){
     int tick;std::string src,data;std::cin>>tick>>src>>data;
     now=tick/16.0;
     const auto got=seen.size();
     w.b.incomingMsgs.push_back({src,"Base",data});
     w.b.DispatchMessages();
     assert(w.b.incomingMsgs.empty());
     if(seen.size()>got){
       assert(seen.back()==std::make_pair(src,data));
       std::cout<<' '<<seen.back().first<<':'<<seen.back().second;
     }else std::cout<<" -";
   }
   std::cout<<'\n';
 }
}
