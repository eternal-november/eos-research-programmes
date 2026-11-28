#include <cassert>
#include <cstdint>
#include <cstdio>
#include <memory>
#include <array>
#include <set>
#include <map>
#define LOG(...) ((void)0)
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
int main(){
 for(unsigned tail:{1,2,8,64,511}){
  for(bool committed:{false,true}) {
   UnackedRpcResults honest, split, unsafePrefix, wrongLane;
   uint64_t v=0;
   for(auto r:{&honest,&split,&unsafePrefix,&wrongLane}){
      assert(!r->request(11,1,0,v));
      if(committed)r->finish(11,1,9999);
   }
   for(unsigned j=1;j<=tail;j++){
     assert(!honest.request(11,j+1,0,v));
     honest.finish(11,j+1,j);
     assert(!unsafePrefix.request(11,j+1,0,v));
     unsafePrefix.finish(11,j+1,j);
     assert(!split.request(22,j,j-1,v));
     split.finish(22,j,j);
   }
   assert(honest.log.freed.empty());
   assert(honest.request(11,1,0,v)&&v==(committed?9999:0));
   assert(!split.request(22,tail+1,tail,v));
   assert(split.log.freed.size()==tail);
   assert(split.request(11,1,0,v)&&v==(committed?9999:0));
   // This negative control models an erroneous local interpretation of the
   // highest received result as a cumulative acknowledgment.
   assert(!unsafePrefix.request(11,tail+2,tail+1,v));
   assert(unsafePrefix.log.freed.size()==tail+committed);
   try { unsafePrefix.request(11,1,0,v);assert(false); } catch(StaleRpcException&) {}
   // Reissuing an old operation under a new live lease is a different key.
   assert(!wrongLane.request(22,1,0,v));
  }
 }
 puts("10 source controls: independent reclamation, old retry preserved, wrong prefix and wrong lane distinguished");
}