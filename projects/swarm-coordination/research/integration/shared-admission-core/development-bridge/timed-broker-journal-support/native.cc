#define main previous_replay
#include "staged_replay.inc"
#undef main
#include <cstdio>
extern "C" {
struct sqlite3;
int sqlite3_open(const char*,sqlite3**);
int sqlite3_close(sqlite3*);
int sqlite3_exec(sqlite3*,const char*,int(*)(void*,int,char**,char**),void*,char**);
}
struct Journal{
 sqlite3* db=nullptr;
 const char* path="appointment.db";
 Journal(){std::remove(path);open();sql("create table settled(k text primary key, v text)");}
 ~Journal(){close();std::remove(path);}
 void open(){assert(!db&&sqlite3_open(path,&db)==0);}
 void close(){assert(db&&sqlite3_close(db)==0);db=nullptr;}
 void sql(const std::string& s){assert(sqlite3_exec(db,s.c_str(),nullptr,nullptr,nullptr)==0);}
 std::string get(){
  std::string out;
  auto cb=[](void* ptr,int n,char** c,char**){
   assert(n==1&&c[0]);
   *static_cast<std::string*>(ptr)=c[0];return 0;};
  assert(sqlite3_exec(db,"select v from settled where k='OLD'",cb,&out,nullptr)==0);
  return out;
 }
 void put(std::string p){
  assert((p=="SIDE"||p=="TIDE")&&get().empty());
  sql("insert into settled values('OLD','"+p+"')");
 }
 void restart(){close();open();}
};
int main(){
 for(int cap:{3,4,5,8,9})
  for(int spacing:{4,5,6})
   for(int policy:{0,1,2})
    for(int h:{0,1}){
     const std::string value=h?"TIDE":"SIDE";
     std::string order="FPRSW";
     do{
      World w(cap);
      Journal j;
      bool online=true,request=false;
      int probe=0,reply=0,commits=0;
      for(const char* id:{"D","I"}){
       auto node=std::make_shared<TeamNode>();node->name=id;node->radio.capacity=8*cap;
       node->radio.pathloss_f=[&,id](double,auto&,auto&,bool& b){
         b=false;return Power{(std::string(id)=="I"||online)?100:-std::numeric_limits<double>::infinity(),0};};
       w.b.team->emplace(id,node);w.b.endpoints[std::string(id)+":7"]={{id}};
      }
      w.app.callbacks["D:7"]=[&](auto from,auto,auto,auto data){
       if(from=="I"){j.put(data);++commits;}
       else {assert(from=="Q"&&data=="owed");request=true;}
      };
      w.app.callbacks["Q:7"]=[&](auto from,auto,auto,auto data){
       assert(from=="D");
       if(data.size()==1){assert(data=="0"||data=="1");probe=1+(data=="1");}
       else {assert(data==value);reply=1+h;}
      };
      // Send and receive use the pinned broker, not the finite abstraction.
      auto send=[&](std::string src,std::string dst,std::string data){
       w.b.incomingMsgs.push_back({src,dst,data});
       w.b.DispatchMessages();
       assert(w.b.incomingMsgs.empty());
      };
      auto live=[](const auto& v){unsigned n=0;for(auto [t,b]:v)if(t>=now-1.)n+=b;return n;};
      std::cout<<cap<<" "<<spacing<<" "<<policy<<" "<<h<<" "<<order;
      int step=0;
      for(char e:order){
       now=step++*spacing/16.;
       if(e=='F')online=false;
       if(e=='S')send("I","D",value);
       if(e=='W')j.restart();
       if(e=='P'&&(policy==0||(policy==1&&!j.get().empty())))
          send("D","Q",j.get().empty()?"0":"1");
       if(e=='R'){
        send("Q","D","owed");
        if(request&&!j.get().empty())send("D","Q",j.get());
       }
       const auto settled=j.get();
       assert(settled.empty()||settled==value);
       assert(commits==!settled.empty());
       std::cout<<" "<<commits<<probe<<int(request)<<reply
         <<live(w.state("I").bytes_sent)
         <<live(w.state("D").bytes_received)<<live(w.state("D").bytes_sent)
         <<live(w.state("Q").bytes_received)<<live(w.state("Q").bytes_sent);
      }
      std::cout<<"\n";
     }while(std::next_permutation(order.begin(),order.end()));
    }
}
