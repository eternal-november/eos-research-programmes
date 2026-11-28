#define main previous_replay
#include "staged_replay.inc"
#undef main
#include <cstring>
extern "C" {
struct sqlite3;
int sqlite3_open(const char*,sqlite3**);
int sqlite3_close(sqlite3*);
int sqlite3_exec(sqlite3*,const char*,int(*)(void*,int,char**,char**),void*,char**);
int sqlite3_set_authorizer(sqlite3*,int(*)(void*,int,const char*,const char*,const char*,const char*),void*);
}
struct Query {
 sqlite3* db=nullptr;
 bool authorized=false;
 int holder=1, current_epoch=2;
 Query(int b) {
  assert(sqlite3_open(":memory:",&db)==0);
  exec("create table old_job(key text, permit integer, raw_detail text, epoch integer);"
       "create view named_export as select permit from old_job where key='OLD' and epoch=2;");
  exec("insert into old_job values ('OLD',"+std::to_string(b)+",'private measurement',2);");
  assert(sqlite3_set_authorizer(db,auth,this)==0);
 }
 ~Query(){assert(sqlite3_close(db)==0);}
 void exec(const std::string& cmd){assert(sqlite3_exec(db,cmd.c_str(),nullptr,nullptr,nullptr)==0);}
 static int auth(void* ptr,int op,const char* table,const char*,const char*,const char* view) {
  // The gateway prepares a fixed statement and enforces a typed request.
  // This is not a general-purpose SQL execution service.
  if(op==21)return 0; // SQLITE_SELECT
  if(op!=20)return 1; // SQLITE_READ
  const auto* self=static_cast<const Query*>(ptr);
  const bool through=view && std::strcmp(view,"named_export")==0;
  return self->authorized && ((through&&std::strcmp(table,"old_job")==0)
                             || std::strcmp(table,"named_export")==0) ? 0 : 1;
 }
 int query(int role,int epoch,bool correctKey,int port,bool authorizedAlternate){
  authorized=role==holder && epoch==current_epoch && epoch==2 && correctKey && (port==0||authorizedAlternate);
  assert(sqlite3_exec(db,"select raw_detail from old_job",nullptr,nullptr,nullptr)==23); // SQLITE_AUTH
  int result=-1;
  auto cb=[](void* p,int n,char** c,char**){
   assert(n==1&&c[0]);*static_cast<int*>(p)=std::stoi(c[0]);return 0;};
  const int rc=sqlite3_exec(db,"select permit from named_export",cb,&result,nullptr);
  assert(rc==(authorized?0:23));
  return result;
 }
};
int main(){
 for(int graph:{0,1,2,3})for(int split:{0,1,2,3})
  for(int cap:{4,5})for(int lag:{4,8,9})
   for(int shape:{0,1,2})for(int add:{0,1})for(int bind:{0,1})for(int b:{0,1}){
    World w(cap);
    Query store(b);
    const int issuer=split&1;
    assert(store.query(0,1,true,issuer,add)==-1);
    assert(store.query(0,2,true,issuer,add)==-1);
    assert(store.query(1,1,true,issuer,add)==-1);
    assert(store.query(1,2,false,issuer,add)==-1);
    const int permit=store.query(1,2,true,issuer,add);
    assert(permit==(issuer&&!add?-1:b));
    int private_reply=-1,report=0,ack=0;
    for(auto id:{"D","T","H","H2","M","O","ACK"}){
     auto n=std::make_shared<TeamNode>();n->name=id;n->radio.capacity=8*cap;
     n->radio.pathloss_f=[](double,auto&,auto&,bool& d){d=false;return Power{100.,0};};
     w.b.team->emplace(id,n);w.b.endpoints[std::string(id)+":7"]={{id}};
    }
    const std::string h=issuer?"H2":"H";
    const std::string target=split&2?"T":"D";
    const std::string public_src=graph&1?"H":"M";
    const std::string public_dst=graph&2?"D":"O";
    for(auto id:{"D","T","O"})w.app.callbacks[std::string(id)+":7"]=[&,id](auto src,auto,auto,auto data){
     if(data=="SIDE"){
      assert(src==public_src&&id==public_dst);
      report=1;
     }else{
      assert((data=="0"||data=="1")&&id==target&&src==h);
      private_reply=data[0]-'0';
     }
    };
    w.app.callbacks["M:7"]=[&](auto src,auto,auto,auto data){
     assert(src=="ACK"&&data=="1");ack=1;
    };
    auto send=[&](std::string src,std::string dst,std::string data,double t){
     now=t;
     w.b.incomingMsgs.push_back({src,dst,data});
     w.b.DispatchMessages();assert(w.b.incomingMsgs.empty());
    };
    // Shape never / positive only / constant-width cover.
    const bool sent=permit>=0&&(shape==2||(shape==1&&permit==1));
    if(sent)send(h,target,std::to_string(permit),1.);
    assert(private_reply==(sent?permit:-1));
    const double t=1.+lag/8.;
    send(public_src,public_dst,"SIDE",t);
    if(report)send("ACK","M","1",t);
    // A second appointment change is after receipt and before use.
    // Recheck at the application effect; this cannot refund the queue.
    if(bind){store.holder=2;store.current_epoch=3;}
    const int live=store.query(1,2,true,issuer,add);
    assert(live==(bind?-1:permit));
    const int act=private_reply==1&&live==1;
    std::cout<<graph<<" "<<split<<" "<<cap<<" "<<lag<<" "<<shape<<" "<<add<<" "<<bind<<" "<<b
             <<" "<<permit<<" "<<private_reply<<" "<<ack<<" "<<act<<"\n";
   }
}
