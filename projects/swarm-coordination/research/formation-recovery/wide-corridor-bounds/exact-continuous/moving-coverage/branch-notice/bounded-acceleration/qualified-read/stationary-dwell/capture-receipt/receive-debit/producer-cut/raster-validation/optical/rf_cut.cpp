#define main inherited_broker_replay
#include "upstream_replay.cpp"
#undef main
int main(){
   int cap,n,partition;
   while(std::cin>>cap>>n>>partition){
      World w(cap);
      std::vector<std::pair<std::string,std::string>> seen;
      w.app.callbacks["Base:7"]=[&](auto sender,auto,auto,auto payload){
         seen.emplace_back(sender,payload);
      };
      std::cout<<n;
      for(int i=0;i<n;++i){
         int t;std::string name,p;std::cin>>t>>name>>p;
         now=t/1024.0;
         w.path_available=!partition||t<1024;
         auto prev=seen.size();
         w.b.incomingMsgs.push_back({name,"Base",p});
         w.b.DispatchMessages();
         assert(w.b.incomingMsgs.empty());
         if(seen.size()==prev)std::cout<<" -";
         else{assert(seen.size()==prev+1&&seen.back()==std::make_pair(name,p));std::cout<<' '<<name<<':'<<p;}
      }
      std::cout<<'\n';
   }
}
