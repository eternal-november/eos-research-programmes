#define main old_driver_main
#include "replay.cpp"
#undef main

int main(){
 unsigned c,a,b,x,st,rx,cp,cq,cr;
 double h,t;
 while(std::cin>>c>>a>>b>>x>>h>>t>>st>>rx>>cp>>cq>>cr){
   World w(c);
   for(std::string name:{"A2","Independent","Far"}){
      auto n=std::make_shared<TeamNode>();
      n->name=name; n->radio=w.b.team->at("P")->radio;
      w.b.team->emplace(name,n);
   }
   w.b.team->at("Independent")->radio.capacity=8*c;
   w.b.team->at("P")->radio.capacity=8*cp;
   w.b.team->at("Q")->radio.capacity=8*cq;
   w.b.team->at("Base")->radio.capacity=8*cr;
   unsigned first=0,tail=0,added=0,ind=0;
   auto reg=[&](std::string app,std::string physical,unsigned& counter){
      w.b.endpoints[app+":7"].push_back({physical});
      unsigned* slot=&counter;
      w.app.callbacks[app+":7"]=[slot](auto,auto,auto,const auto&){++*slot;};
   };
   reg("OldFirst","Base",first);
   reg("OldTail",rx ? "Base":"A2",tail);
   reg("NewEffect","Base",added);
   reg("Disjoint","Far",ind);
   auto send=[&](std::string s,std::string d,unsigned n,double when){
     now=when;
     w.b.incomingMsgs.push_back({s,d,std::string(n,'v')});
     w.b.DispatchMessages();
     assert(w.b.incomingMsgs.empty());
   };
   send("P","OldFirst",a,0);
   send("Independent","Disjoint",1,.125);
   if(t<h)send("P","NewEffect",x,t);
   send(st?"P":"Q","OldTail",b,h);
   if(t>=h)send("P","NewEffect",x,t);
   assert(first==1 && ind==1 && tail<=1 && added<=1);
   std::cout<<first<<' '<<tail<<' '<<added<<' '<<ind<<'\n';
 }
}
