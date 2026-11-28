#include <cassert>
#include <cstdint>
#include <cstddef>
#include <cstdio>
#include <set>
#define PUBLIC public
#define PRIVATE private
#define DISALLOW_COPY_AND_ASSIGN(T) T(const T&)=delete; T& operator=(const T&)=delete
#define RAMCLOUD_CLOG(...) ((void)0)
#include "RpcTracker.h"
#include "tracker.inc"
namespace RAMCloud {
struct Gate{};
struct Job : RpcTracker::TrackedRpc {
 RpcTracker& tracker;
 uint64_t id=0;
 int pushes=0;
 explicit Job(RpcTracker& tracker):tracker(tracker){}
 void tryFinish() override { ++pushes; throw Gate{}; }
 uint64_t reserve() { return id=tracker.newRpcId(this); }
 void complete() { tracker.rpcFinished(id); }
};
}
using namespace RAMCloud;
int main(){
 constexpr int window = 512;
 RpcTracker single;
 Job old(single), immediate(single);
 assert(old.reserve()==1);
 for(int i=2;i<=window;i++){
    assert(immediate.reserve()==(unsigned)i);immediate.complete();
 }
 assert(single.ackId()==0);
 try { immediate.reserve();assert(false); } catch(Gate&) {}
 assert(old.pushes==1&&immediate.pushes==0&&single.ackId()==0);
 old.complete();
 assert(single.ackId()==window&&immediate.reserve()==window+1);
 immediate.complete();
 printf("same-lane old=1 independent-before-gate=%d ack-at-cut=0 after-old=%llu\n",
    window-1,(unsigned long long)single.ackId());

 for(int prefix:{0,1,7,509,512,513,1025}){
   for(int unrelated:{0,1,510,511,512,1024,2048}){
     RpcTracker critical, independent;
     Job a(critical), b(independent);
     for(int j=0;j<prefix;j++){a.reserve();a.complete();}
     a.reserve();
     for(int j=0;j<unrelated;j++){b.reserve();b.complete();}
     assert(a.pushes+b.pushes==0);
     assert(critical.ackId()==(unsigned)prefix && independent.ackId()==(unsigned)unrelated);
     a.complete();
     assert(critical.ackId()==(unsigned)prefix+1);
   }
   RpcTracker any;
   Job x(any), y(any);
   for(int j=0;j<prefix;j++){x.reserve();x.complete();}
   x.reserve();
   for(int j=0;j<window-1;j++){y.reserve();y.complete();}
   assert(any.ackId()==(unsigned)prefix);
   try { y.reserve();assert(false); } catch(Gate&) {}
   assert(x.pushes==1&&y.pushes==0);
   x.complete();
   assert(any.ackId()==(unsigned)prefix+window);
   assert(y.reserve()==(unsigned)prefix+window+1);
   y.complete();
 }
 puts("49 separated controls and 7 blocked-and-released controls pass");
}
