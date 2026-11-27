#define main prior_radio_main
#include <replay.cpp>
#undef main

double power_for_drop(double target){
 double a=0,b=10;
 for(int i=0;i<100;++i){
  double x=(a+b)/2;
  if(std::erfc(x)>target)a=x;else b=x;
 }
 return -100+10*std::log10((a+b)*(a+b)/4);
}
int main(){
 for(int H:{0,1})for(int first:{250,750})for(int second:{250,750})
 for(int change:{0,1}){
   World w(16);
   auto dest=std::make_shared<TeamNode>();
   dest->name="Side";dest->radio=w.b.team->at("Q")->radio;
   w.b.team->emplace("Side",dest);
   int old=0,side=0;
   w.b.endpoints["Side:7"]={{"Side"}};
   w.app.callbacks["Side:7"]=[&](auto,auto,auto,auto){++side;};
   w.app.callbacks["Base:7"]=[&](auto,auto,auto,auto){++old;};
   if(H){
     auto& s=w.state("Side");
     s.bytes_received.emplace_back(0,16);s.bytes_received_this_epoch=16;
   }else{
     auto& s=w.state("Q");
     s.bytes_sent.emplace_back(0,16);s.bytes_sent_this_epoch=16;
   }
   for(auto [k,n]:*w.b.team){
     double p=power_for_drop(k=="P"?.5005:.1005);
     n->radio.pathloss_f=[p](double,auto&,auto&,bool& c){c=false;return Power{p,0.};};
   }
   subt::msgs::Datagram p{"P","Base","r"},q{"Q","Side","d"};
   reset_draws({first,second});now=0;
   if(change){w.b.incomingMsgs.push_back(p);w.b.incomingMsgs.push_back(q);}
   else{w.b.incomingMsgs.push_back(q);w.b.incomingMsgs.push_back(p);}
   w.b.DispatchMessages();
   assert(side==0);
   assert(draws_consumed==size_t(1+H));
   assert(old==int((H&&!change?second:first)==750));
   assert(w.state("Q").bytes_sent_this_epoch==unsigned(H?1:16));
   std::cout<<H<<' '<<int(first==750)<<' '<<int(second==750)<<' '
            <<change<<' '<<old<<' '<<side<<' '<<draws_consumed<<'\n';
 }
}
