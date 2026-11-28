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
 const char* path;
 explicit Journal(const char* p):path(p){std::remove(path);open();sql("create table settled(k text primary key, v text, t real)");}
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
  sql("insert into settled values('OLD','"+p+"',"+std::to_string(now)+")");
 }
 void restart(){close();open();}
};

int is_early(Journal& j, double request_day){
 int answer=-1;
 auto cb=[](void* ptr,int n,char** c,char**){
  assert(n==1&&c[0]);
  *static_cast<int*>(ptr)=std::stoi(c[0]);return 0;};
 const auto query="select t < "+std::to_string(request_day-1.)+" from settled where k='OLD'";
 assert(sqlite3_exec(j.db,query.c_str(),cb,&answer,nullptr)==0);
 assert(answer==0||answer==1);
 return answer;
}

int main(){
 for(int u:{0,1})for(int v:{0,1})for(int a:{0,1})
  for(int h:{0,1})for(int mode:{0,1,2,3,4,5,6,7,8})for(double late:{1.,1.125}){
   World w(4);
   Journal d0("d0.db"),d1("d1.db");
   Journal* records[]={&d0,&d1};
   const std::string docks[]={"D0","D1"};
   const std::string value=h?"TIDE":"SIDE";
   const int early=v^a;
   int delivered=0,request=0,qtag=-1,ttag=-1,reply=0,early_result=0;
   for(auto id:{"D0","D1","I","H","T","Q2"}){
    auto n=std::make_shared<TeamNode>();n->name=id;
    n->radio.capacity=8*(n->name=="I"?16:n->name=="H"?1:4);
    n->radio.pathloss_f=[](double,auto&,auto&,bool& b){b=false;return Power{100,0};};
    w.b.team->emplace(id,n);w.b.endpoints[std::string(id)+":7"]={{id}};
   }
   for(int d:{0,1})w.app.callbacks[docks[d]+":7"]=[&,d](auto from,auto,auto,auto data){
    if(from=="I"){records[d]->put(data);++delivered;}
    else {assert((from=="Q"||from=="Q2")&&data=="owed"&&d==u);++request;}
   };
   w.app.callbacks["Q:7"]=[&](auto from,auto,auto,auto data){
    if(from=="H"){assert(data=="0"||data=="1");qtag=data[0]-'0';}
    else {assert(from==docks[u]&&data==value);reply=1+h;}
   };
   w.app.callbacks["T:7"]=[&](auto from,auto,auto,auto data){
    assert(from=="H"&&(data=="0"||data=="1"));ttag=data[0]-'0';
   };
   w.app.callbacks["Q2:7"]=[&](auto from,auto,auto,auto data){
    assert(from==docks[u]&&data==value);reply=1+h;
   };
   auto send=[&](std::string src,std::string dst,std::string data,double t){
    now=t;w.b.incomingMsgs.push_back({src,dst,data});w.b.DispatchMessages();
    assert(w.b.incomingMsgs.empty());
   };
   send("I",docks[early],value,.875);
   send("I",docks[1-early],value,late);
   assert(delivered==2);
   d0.restart();d1.restart();
   assert(d0.get()==value&&d1.get()==value);
   const double t=mode?2.25:2.;
   if(mode>=2&&mode<=6){
    const int named=mode==6?0:mode==5?1-u:u;
    const int bit=is_early(*records[named],mode==4?t:2.);
    send("H",mode==2?"Q":"T",std::to_string(bit),t);
   }
   if(mode>=7){
    send("Q",docks[u],"owed",2.);
    if(request)send(docks[u],"Q",records[u]->get(),2.);
    early_result=reply;
    if(!reply){
     const auto source=mode==7?"Q":"Q2";
     send(source,docks[u],"owed",2.25);
     if(request)send(docks[u],source,records[u]->get(),2.25);
    }
   }else if(mode!=6){
    send("Q",docks[u],"owed",t);
    if(request)send(docks[u],"Q",records[u]->get(),t);
   }
   unsigned charged=0;
   for(auto id:{"Q","Q2","H","D0","D1"})
    for(auto [ts,bytes]:w.state(id).bytes_sent)
     if(ts>=2.)charged+=bytes;
   std::cout<<u<<" "<<v<<" "<<a<<" "<<h<<" "<<mode<<" "<<int(8*late)
            <<" "<<request<<" "<<reply<<" "<<qtag<<" "<<ttag<<" "<<early_result<<" "<<charged<<"\n";
  }
}
