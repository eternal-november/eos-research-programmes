#include <cassert>
#include <set>
#define main native_upstream_baseline
#include "staged_replay.inc"
#undef main

using k=std::pair<std::string,bool>; // true is TX, false is RX
struct pkt {std::string u,v; unsigned n; long long cut; bool link; };
struct Profile {
 // One cut per age group. Expired rows can be dropped at every
 // comparison; the retained native ledger need not have pruned yet.
 std::map<k,std::map<long long,unsigned>> live;
 void transport(long long t){
   for(auto& [_,xs]:live)
     while(!xs.empty()&&xs.begin()->first<t-1000000)xs.erase(xs.begin());
 }
 unsigned use(k j)const{
   const auto x=live.find(j);unsigned n=0;
   if(x!=live.end())for(auto [_,v]:x->second)n+=v;
   return n;
 }
 void extend(k p,long long t,unsigned n){live[p][t]+=n;}
 bool admit(unsigned cap,const pkt& d){
   transport(d.cut);
   if(use({d.u,true})+d.n>cap)return false;
   extend({d.u,true},d.cut,d.n);
   if(!d.link||use({d.v,false})+d.n>cap)return false;
   extend({d.v,false},d.cut,d.n);
   return true;
 }
};
static auto active(const std::deque<std::pair<double,uint64_t>>& q,long long cut){
   std::map<long long,unsigned> out;
   for(auto [t,b]:q){
      const auto i=(long long)(t*1000000);
      assert(i/1.e6==t);
      if(i>=cut-1000000)out[i]+=b;
   }
   return out;
}
static auto value(World& w,const std::string& who,bool tx,long long cut){
   const auto& s=w.state(who);
   return tx?active(s.bytes_sent,cut):active(s.bytes_received,cut);
}
static bool real(World& w,const pkt& d){
   w.path_available=d.link;
   const auto n=std::to_string(d.n);
   std::string got;
   w.app.callbacks[d.v+":7"]=[&](auto src,auto,auto,auto bytes){assert(src==d.u);got=bytes;};
   w.send(d.u,d.v,d.n,d.cut/1.e6);
   assert(got.empty()||got.size()==d.n);
   w.app.callbacks.erase(d.v+":7");
   return !got.empty();
}
static unsigned calls, batches, separate_false;
static bool compare(World& w,Profile& model,unsigned cap,const pkt& d){
    const bool good=model.admit(cap,d);
    assert(real(w,d)==good);
    for(const auto& node:{"P","Q","Base"})for(bool tx:{false,true})
      assert(value(w,node,tx,d.cut)==model.live[std::make_pair(node,tx)]);
    ++calls;
    return good;
}
static bool all_fit(Profile p,unsigned cap,std::vector<pkt> jobs){
   // Pasting two local receipt obligations at a shared cut: sum their
   // prospective amounts per *actual* sender or recipient resource.
   long long cut=jobs.at(0).cut;
   p.transport(cut);
   std::map<k,unsigned> claims;
   for(const auto& f:jobs){
     assert(f.cut==cut&&f.link);
     claims[{f.u,true}]+=f.n;
     claims[{f.v,false}]+=f.n;
   }
   for(const auto& [r,n]:claims)if(p.use(r)+n>cap)return false;
   return true;
}
int main(){
 for(unsigned cap=3;cap<=7;cap++)
 for(unsigned debt=0;debt<=4;debt++)
 for(unsigned u=1;u<=5;u++)for(unsigned v=1;v<=5;v++)
 for(long long cut:{250000,1000000,1250000})
 for(bool oneSender:{false,true})for(bool oneReceiver:{false,true})
 for(bool oldLink:{false,true}){
   World w(cap);Profile m;
   if(debt)compare(w,m,cap,{"P","Base",debt,0,oldLink});
   pkt a{"P","Base",u,cut,true},b{oneSender?"P":"Q",oneReceiver?"Base":"Q",v,cut,true};
   if(all_fit(m,cap,{a})&&all_fit(m,cap,{b})&&!all_fit(m,cap,{a,b}))++separate_false;
   const auto together=all_fit(m,cap,{a,b});
   const bool first=compare(w,m,cap,a);const bool second=compare(w,m,cap,b);
   assert(together==(first&&second)); ++batches;
 }
 assert(separate_false>0);
 // Exact writer-effect witness: different sizes partitioned at the same
 // native event age supply the same leaf test and subsequent aging.
 World a(6), b(6);Profile aa,bb;
 assert(compare(a,aa,6,{"P","Base",3,0,true}));
 assert(compare(b,bb,6,{"P","Base",1,0,true}));
 assert(compare(b,bb,6,{"P","Base",2,0,true}));
 assert(aa.live==bb.live);
 for(long long cut:{250000,1000000,1125000,1250000,2250000})
    assert(compare(a,aa,6,{"P","Base",4,cut,true})==compare(b,bb,6,{"P","Base",4,cut,true}));
 assert(aa.live==bb.live);
 std::cout<<"batches "<<batches<<" attempts "<<calls
          <<" both individually fit but not jointly "<<separate_false<<"\n";
}
