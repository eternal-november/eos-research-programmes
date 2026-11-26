#define main inherited_reference_main
#include "replay.cpp"
#undef main

int main() {
  std::unique_ptr<World> w;
  std::map<std::string,std::string> callbacks;
  std::string op,a,b,p;
  while(std::cin>>op) {
    if(op=="reset") {
      w=std::make_unique<World>(4);
      callbacks.clear();
      for(auto s:{"S0","S1","S2","S3","S4","Side","Far","Unused","Old",
                  "D0","D1","D2","D3","D4","Job","Direct","Bypass"}) {
        auto n=std::make_shared<TeamNode>(*w->b.team->at("P"));
        w->b.team->emplace(s,n);
        w->b.endpoints[std::string(s)+":7"]={{s}};
        w->app.callbacks[std::string(s)+":7"]=[&, s](auto,auto,auto,const auto& v){
          callbacks[s]=v;
        };
      }
      std::cout<<"ok"<<std::endl;
    } else {
      int t; unsigned link;
      assert(op=="send");
      std::cin>>t>>a>>b>>p>>link;
      now=t/4.0;
      callbacks.erase(b);
      w->path_available=link;
      w->b.incomingMsgs.push_back({a,b,p});
      w->b.DispatchMessages();
      assert(w->b.incomingMsgs.empty());
      auto bytes=[](const auto& queue){
        unsigned n=0;
        for(auto [x,s]:queue)if(x>=now-1.0)n+=s;
        return n;
      };
      std::cout<<(callbacks.count(b)?callbacks.at(b):"-")<<" "
               <<bytes(w->state(a).bytes_sent)<<" "
               <<bytes(w->state(b).bytes_received)<<std::endl;
    }
  }
}
