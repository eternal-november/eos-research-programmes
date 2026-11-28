#include <cassert>
#include <cstdint>
#include <cstdio>
#include <memory>
#include <array>
#include <set>
#include <map>
#define LOG(...) ((void)0)
#define RAMCLOUD_CLOG(...) ((void)0)
#define HERE 0
struct StaleRpcException { explicit StaleRpcException(int){} };
struct ExpiredLeaseException { explicit ExpiredLeaseException(int){} };
struct ClusterTime{
 uint64_t n=0; explicit ClusterTime(uint64_t p):n(p){}
 bool operator<(const ClusterTime& b)const{return n<b.n;}
 uint64_t getEncoded()const{return n;}
};
namespace WireFormat { struct ClientLease{uint64_t leaseId,leaseExpiration;}; }
struct Valid {
 bool validate(WireFormat::ClientLease,WireFormat::ClientLease*){return true;}
};
struct Log { struct Reference { uint64_t n; explicit Reference(uint64_t n):n(n){} }; };
struct AbstractLog { struct ReferenceFreer {
  std::set<uint64_t> freed;
  void freeLogEntry(Log::Reference r){assert(freed.insert(r.n).second);}
}; };
struct UnackedRpcResults {
 struct Rec {uint64_t id=0; void* result=nullptr;};
 struct Client {
    uint64_t maxAckId=0,maxRpcId=0;
    uint64_t numRpcsInProgress=0;
    ClusterTime leaseExpiration{0};
    static constexpr auto len=1024;
    std::array<Rec,len> rpcs{};
    void recordNewRpc(uint64_t id){auto& r=rpcs.at(id%len);assert(r.id<=maxAckId);r={id,nullptr};}
    bool hasRecord(uint64_t id){return id>maxAckId && rpcs.at(id%len).id==id;}
    void* result(uint64_t id){assert(hasRecord(id));return rpcs.at(id%len).result;}
    void updateResult(uint64_t id,void* p){assert(hasRecord(id));rpcs.at(id%len).result=p;}
    void processAck(uint64_t,AbstractLog::ReferenceFreer*);
 };
 struct Lock { explicit Lock(int){} }; // Fixture is serial.
 int mutex=0;
 Valid lease;
 Valid* leaseValidator=&lease;
 AbstractLog::ReferenceFreer log;
 AbstractLog::ReferenceFreer* freer=&log;
 std::map<uint64_t,Client> clients;
 Client* getOrInitClientRecord(uint64_t id,Lock&){return &clients[id];}
 bool checkDuplicate(WireFormat::ClientLease,uint64_t,uint64_t,void**);
 void recoverRecord(uint64_t,uint64_t,uint64_t,void*);
 enum class LogEntryType {RESULT};
 struct LogEntryTypeHelpers {static const char* toString(LogEntryType){return "RESULT";}};
 bool shouldRecover(uint64_t,uint64_t,uint64_t,LogEntryType);
 void finish(uint64_t lane,uint64_t id,uint64_t value){
    auto& c=clients.at(lane);
    auto& r=c.rpcs.at(id%c.len);
    assert(r.id==id&&r.result==nullptr);r.result=reinterpret_cast<void*>(value);
 }
 bool request(uint64_t lane,uint64_t id,uint64_t ack,uint64_t& value){
    void* ptr=nullptr;
    auto status=checkDuplicate({lane,10},id,ack,&ptr);
    value=reinterpret_cast<uint64_t>(ptr);
    return status;
 }
};
#include "server.inc"

void import(UnackedRpcResults& s,int lane,int id,int prefix,int v){
 if(s.shouldRecover(lane,id,prefix,UnackedRpcResults::LogEntryType::RESULT))
   s.recoverRecord(lane,id,prefix,reinterpret_cast<void*>(uintptr_t(v)));
}
int main(){
 uint64_t v=0;
 for(int prefix=0;prefix<=16;prefix++){
  int key=prefix+1;
  for(int value:{17,256,9999}){
   UnackedRpcResults early,ready,lateOther;
   // New request classified before rebuilding the protected key.
   assert(!early.request(11,key,prefix,v));
   import(early,11,key,prefix,value);
   assert(early.request(11,key,prefix,v)&&v==0);
   // Normal rendezvous; restore before checking the old key.
   import(ready,11,key,prefix,value);
   assert(ready.request(11,key,prefix,v)&&v==(unsigned)value);
   import(ready,11,key,prefix,value); // identical duplicate no change
   assert(ready.request(11,key,prefix,v)&&v==(unsigned)value);
   // Unrelated lane can run while old reconstruction not yet finished.
   assert(!lateOther.request(22,1,0,v));
   lateOther.finish(22,1,8);
   import(lateOther,11,key,prefix,value);
   assert(lateOther.request(11,key,prefix,v)&&v==(unsigned)value);
   assert(lateOther.request(22,1,0,v)&&v==8);
  }
 }
 puts("51 paired early/canonical/independent controls pass");
}
