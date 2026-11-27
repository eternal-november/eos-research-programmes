#define main prior_radio_main
#include <replay.cpp>
#undef main

int main(){
  std::unique_ptr<World> world;
  std::string cmd,got;
  while(std::cin>>cmd){
    if(cmd=="reset"){
      unsigned cap;std::cin>>cap;
      world=std::make_unique<World>(cap);
      world->app.callbacks["Base:7"]=[&](auto,auto,auto,auto payload){got=payload;};
      std::cout<<"ok"<<std::endl;
    }else if(cmd=="send"){
      unsigned tick;std::string source,hex;std::cin>>tick>>source>>hex;
      assert(hex.size()%2==0);
      std::string body;
      for(size_t i=0;i<hex.size();i+=2)
        body+=char(std::stoi(hex.substr(i,2),nullptr,16));
      ::now=tick/4.;
      got.clear();
      world->b.incomingMsgs.push_back({source,"Base",body});
      world->b.DispatchMessages();
      auto& tx=world->state(source);auto& rx=world->state("Base");
      std::cout<<(got==body?1:0)<<' '<<tx.bytes_sent_this_epoch<<' '
               <<rx.bytes_received_this_epoch<<std::endl;
      assert(got.empty()||got==body);
    }else assert(false);
  }
}
