#define main stock_selected_tests
#include "upstream_replay.cpp"
#undef main
int main(){
 int cap,n;
 while(std::cin>>cap>>n){
   World w(cap);
   std::vector<std::pair<std::string,std::string>> seen;
   w.app.callbacks["Base:7"]=[&](auto sender,auto,auto,auto payload){
     seen.emplace_back(sender,payload);
   };
   std::cout<<n;
   for(int i=0;i<n;++i){
     int tick;std::string src,payload;std::cin>>tick>>src>>payload;
     now=tick/1024.0;
     auto last=seen.size();
     w.b.incomingMsgs.push_back({src,"Base",payload});
     w.b.DispatchMessages();
     assert(w.b.incomingMsgs.empty());
     if(last==seen.size())std::cout<<" -";
     else{
       assert(last+1==seen.size()&&seen.back()==std::make_pair(src,payload));
       std::cout<<' '<<seen.back().first<<':'<<seen.back().second;
     }
   }
   std::cout<<'\n';
 }
}
