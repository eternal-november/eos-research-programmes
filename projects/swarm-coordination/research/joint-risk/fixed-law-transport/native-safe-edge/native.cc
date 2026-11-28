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
  assert(p=="SIDE"&&get().empty());
  sql("insert into settled values('OLD','"+p+"')");
 }
 void restart(){close();open();}
};
int main(){
 for(int cap:{2,3,4,5})
 for(int xq:{1,2,3})
 for(int opt:{15,16,17,18})
 for(int gap:{1,2,3})
 for(int bytes:{1,2,3})
 for(int iy:{0,1}) for(int ix:{0,1}) for(int permit:{0,1}){
   World w(cap);
   Journal ledger;
   for (auto id:{"X","Y","O","R","U"}) {
      auto node=std::make_shared<TeamNode>();
      node->name=id;node->radio.capacity=8*cap;
      node->radio.pathloss_f=[](double,auto&,auto&,bool& via){
          via=false;return Power{100,0};};
      w.b.team->emplace(id,node);
   }
   int x=0,y=0,optional=0,redo=0,unrelated=0,commits=0;
   w.app.callbacks["Base:7"]=[&](auto from,auto,auto,auto data){
      if(from=="X"){assert(data=="xx");++x;}
      else if(from=="Y"){assert(data=="s");++y;}
      else if(from=="O"){assert(data==std::string(bytes,'o'));++optional;}
      else {assert(from=="R"&&data=="ss");++redo;}
      if((from=="Y"||from=="R")&&ledger.get().empty()){
         ledger.put("SIDE");++commits;
      }
   };
   w.app.callbacks["Q:7"]=[&](auto from,auto,auto,auto data){
      assert(from=="U"&&data=="u");++unrelated;
   };
   auto send=[&](const char* src,const char* dst,std::string data,int q){
      now=q/16.;
      w.b.incomingMsgs.push_back({src,dst,data});
      w.b.DispatchMessages();assert(w.b.incomingMsgs.empty());
   };
   if(iy)send("Y","Base","s",0);
   if(ix)send("X","Base","xx",xq);
   const bool settled_at_cut=ledger.get()=="SIDE";
   assert(settled_at_cut==y);
   ledger.restart();
   if(permit)send("O","Base",std::string(bytes,'o'),opt);
   send("U","Q","u",opt);
   send("R","Base","ss",opt+gap);
   assert(commits==(ledger.get()=="SIDE"));
   std::cout<<cap<<" "<<xq<<" "<<opt<<" "<<gap<<" "<<bytes<<" "<<iy<<" "<<ix<<" "<<permit<<" "
            <<x<<" "<<y<<" "<<optional<<" "<<redo<<" "<<unrelated<<" "<<commits<<"\n";
 }
}
