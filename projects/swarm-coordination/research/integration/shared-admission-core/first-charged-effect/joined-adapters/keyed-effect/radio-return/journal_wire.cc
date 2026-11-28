#define main previous_replay
#include "staged_replay.inc"
#undef main
#include "first_effect.hpp"
#include <iomanip>
#include <sstream>

std::string unhex(const std::string& s){
 if(s=="-")return {};
 assert(s.size()%2==0);
 std::string out;
 for(size_t i=0;i<s.size();i+=2)out.push_back(char(std::stoi(s.substr(i,2),nullptr,16)));
 return out;
}
std::string hex(const std::string& s){
 std::ostringstream out;
 for(unsigned char c:s)out<<std::hex<<std::setw(2)<<std::setfill('0')<<int(c);
 return s.empty()?"-":out.str();
}

int main(){
 int qcap,bcap,edge,load,arm,order;
 std::string pref,transfer;
 while(std::cin>>qcap>>bcap>>edge>>load>>arm>>order>>pref>>transfer){
   World w(qcap); 
   for(auto who:{"B","H"}){
     auto x=std::make_shared<TeamNode>();x->name=who;
     w.b.team->emplace(who,x);w.b.endpoints[std::string(who)+":7"]={{who}};
   }
   w.b.team->at("B")->radio.capacity=8*bcap;
   w.b.team->at("H")->radio.capacity=8*16;
   for(auto src:{"H","B"}){
     auto& c=w.b.team->at(src)->radio;
     c.pathloss_f=[](double,auto&,auto&,bool& route){route=false;return Power{100.,0};};
   }
   w.b.team->at("P")->radio.capacity=8*16;
   unsigned report=0,req=0,side=0,prefix=0,sealed=0;
   std::string pendingReply,actual;
   w.app.callbacks["B:7"]=[&](auto from,auto,auto,auto data){
      if(from=="H"){
        assert(!data.empty());
        std::cout<<"H "<<hex(data)<<std::endl;
        unsigned accepted;
        assert(std::cin>>accepted && accepted<=1);
        if(data.at(0)=='M')prefix=accepted;else sealed=accepted;
      } else {
        assert(from=="Q"&&data=="owed");
        ++req;
        std::cout<<"C"<<std::endl;
        std::string s;
        assert(std::cin>>s);
        pendingReply=unhex(s);
      }
   };
   w.app.callbacks["Q:7"]=[&](auto from,auto,auto,auto data){
     if(from=="P"){assert(data==std::string(load,'s'));++side;}
     else{assert(from=="B"&&data.size()==4);actual=hex(data);++report;}
   };
   auto send=[&](std::string from,std::string to,std::string data,double t){
    now=t;w.b.incomingMsgs.push_back({from,to,data});w.b.DispatchMessages();
    assert(w.b.incomingMsgs.empty());
   };
   send("H","B",unhex(pref),-3);               // actual prefix installation
   if(transfer!="-")send("H","B",unhex(transfer),0.);
   const double t=edge==0?1.:17./16.;
   if(load && order==0)send("P","Q",std::string(load,'s'),t); // fixed paid predecessor
   const auto live=[&](const auto& xs){
      unsigned n=0;for(const auto& v:xs)if(v.first>=t-1.)n+=v.second;return n;
   };
   bool radioOK=live(w.state("Q").bytes_sent)+4<=unsigned(qcap)
            &&live(w.state("B").bytes_received)+4<=unsigned(qcap);
   bool returnOK=live(w.state("B").bytes_sent)+4<=unsigned(bcap)
            &&live(w.state("Q").bytes_received)+4<=unsigned(bcap);
   std::cout<<"I"<<std::endl;
   unsigned allowed;
   assert(std::cin>>allowed&&allowed<=1); // local authorization + key + geometry
   auto attempt=[&](std::size_t){
     send("Q","B","owed",t);
     if(!pendingReply.empty())send("B","Q",pendingReply,t);
   };
   if(arm==0)dispatch_one(1,[&](std::size_t){return allowed&&radioOK&&returnOK;},attempt);
   else if(arm==1){if(allowed && (live(w.state("B").bytes_received) <= unsigned(qcap-4))
                            && (live(w.state("Q").bytes_received) <= unsigned(bcap-4)))attempt(0);}
   else if(arm==2?allowed:radioOK)attempt(0);
   if(load && order==1)send("P","Q",std::string(load,'s'),t); // reorder only if allowed
   std::cout<<"O "<<prefix<<" "<<sealed<<" "<<req<<" "<<report<<" "<<side<<" "
     <<w.state("Q").bytes_sent_this_epoch<<" "<<w.state("B").bytes_sent_this_epoch<<" "
     <<(actual.empty()?"-":actual)<<std::endl;
 }
}
