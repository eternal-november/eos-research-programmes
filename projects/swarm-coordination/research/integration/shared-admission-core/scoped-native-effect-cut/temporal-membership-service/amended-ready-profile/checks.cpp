#include "temporal_parent.inc"
#include <array>
static constexpr std::array<long long,4> cuts{500000,1250000,1375000,1500000};
static inline unsigned card(unsigned x){return __builtin_popcount(x);}
static unsigned profile(unsigned cap,unsigned s){return card(s)>cap?16:s;}
static bool native(bool debt,unsigned s,unsigned u){
    Driver d;d.seed(false);
    if(debt)assert(d.wire(Radio::F,"Aux","owed",250000));
    EffectCut x(d);
    const auto prep=x.prepare();
    assert(d.w.b.Register("AA-observer")&&d.w.b.Register("ZZ-observer"));
    bool result=false;
    for(unsigned i=0;i<cuts.size()&&!result;++i){
       x.lackingPose.clear();
       if(!(s&(1u<<i)))x.lackingPose.insert("AA-observer");
       if(u&(1u<<i))x.lackingPose.insert("ZZ-observer");
       result=x.commit(prep,cuts[i]);
       assert(d.w.b.incomingMsgs.empty());
    }
    if(result)assert(d.presented["Aux"].back()==std::make_pair(std::string("D"),diag));
    return result;
}
int main(){
    unsigned probes=0,signatures=0,relations=0,revisionFailures=0;
    for(bool debt:{false,true}){
      unsigned W=debt?12:15;
      std::map<std::pair<unsigned,unsigned>,bool> report;
      for(unsigned s=0;s<16;++s)if((s&~W)==0)
      for(unsigned u=0;u<16;++u)if((u&~W)==0){
          auto got=native(debt,s,u);
          assert(got==bool(s&~u));
          report[{s,u}]=got;++probes;
      }
      for(unsigned cap=0;cap<=card(W);++cap){
        std::map<unsigned,std::vector<bool>> sig;
        std::set<std::vector<bool>> distinct;
        for(unsigned s=0;s<16;++s)if((s&~W)==0){
           auto& v=sig[s];
           for(unsigned u=0;u<16;++u)if((u&~W)==0&&card(u)<=cap)
               v.push_back(report.at({s,u}));
           distinct.insert(v);
        }
        for(const auto& [s,p]:sig)for(const auto& [t,q]:sig){
           assert((p==q)==(profile(cap,s)==profile(cap,t)));
           if(cap>0 && profile(cap-1,s)==profile(cap-1,t)&&p!=q)++revisionFailures;
           ++relations;
        }
        signatures+=distinct.size();
      }
      if(!debt){
          // Same cardinality and last ready cut. Under the old cap
          // both are saturated. At the new cap one fails, one still sends.
          const unsigned s=5,t=6,partner=s;
          assert(profile(1,s)==profile(1,t) && profile(2,s)!=profile(2,t));
          assert(!report.at({s,partner})&&report.at({t,partner}));
      }
    }
    assert(probes==272&&relations==1328);
    std::cout<<"native schedule pairs "<<probes<<" equality comparisons "<<relations
             <<" profile classes across cap rows "<<signatures
             <<" ordered pairs splitting on increase "<<revisionFailures<<"\n";
}
