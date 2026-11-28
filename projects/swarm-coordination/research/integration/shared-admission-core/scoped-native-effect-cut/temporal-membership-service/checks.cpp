#include "temporal_parent.inc"
#include <array>
using Tick=long long;
static constexpr std::array<Tick,4> cuts{500000,1250000,1375000,1500000};
static const std::array<std::string,2> names{"AA-observer","ZZ-observer"};
int bits(unsigned x){return __builtin_popcount(x);}
int rule(unsigned eligible,int required,int budget0,int budget1){
    int best=-1;
    for(int m=0;m<4;++m)if((m&required)==required &&
        (m&1?budget0:0)+(m&2?budget1:0)<bits(eligible) &&
        (best<0||bits(m)>bits(best)))best=m;
    return best;
}
int direct(unsigned eligible,int required,int budget0,int budget1){
    int best=-1;
    for(int m=0;m<4;++m){
       if((m&required)!=required)continue;
       bool ok=true;
       for(unsigned a=0;a<16;++a)for(unsigned b=0;b<16;++b){
           if(bits(a&eligible)>budget0||bits(b&eligible)>budget1)continue;
           const unsigned miss=(m&1?a:0)|(m&2?b:0);
           if(!(eligible&~miss))ok=false;
       }
       if(ok&&(best<0||bits(m)>bits(best)))best=m;
    }
    return best;
}
static unsigned qualifiedCuts(Driver& d,EffectCut& x,const EffectCut::Prepared& p){
    unsigned out=0;
    const Request q{"diagnostic","Aux",Radio::D,d.gen};
    const auto *v=d.value(q);
    assert(v);
    for(unsigned i=0;i<cuts.size();++i){
       const auto t=cuts[i];
       bool room=d.used(d.physical[q.subject],t)+v->size()<=6 &&
                 d.used(d.receive[q.dest],t)+v->size()<=6;
       bool ok=cut::check({cut::Act::effect,x.bestDirectScope(p),true,room,true})==cut::enable;
       if(ok)out|=1u<<i;
    }
    return out;
}
static void independentLaterService(Driver &d){
    const auto before=d.presented["Base"].size();
    for(const auto& s:names){
       now=1.625;
       d.w.b.incomingMsgs.push_back({s,"Base",std::string(1,'z')});
       d.w.b.DispatchMessages();
       assert(d.w.b.incomingMsgs.empty() && d.presented["Base"].back()==std::make_pair(s,std::string("z")));
       assert(d.w.state(s).bytes_sent_this_epoch==1);
    }
    assert(d.presented["Base"].size()==before+2);
}
int main(){
    unsigned choices=0;
    for(unsigned e=1;e<16;++e)
    for(int capA=0;capA<=4;++capA)
    for(int capB=0;capB<=4;++capB)
    for(int f=0;f<4;++f){
        assert(rule(e,f,capA,capB)==direct(e,f,capA,capB));++choices;
    }
    int runs=0,old=0,late=0,forcedNoGuarantee=0, opposed=0, aligned=0,rawStalls=0;
    for(bool debt:{false,true})
    for(unsigned a=0;a<16;++a)for(unsigned b=0;b<16;++b)
    for(int force=0;force<4;++force){
      Driver d;
      d.seed(false);
      if(debt)assert(d.wire(Radio::F,"Aux","owed",250000));
      EffectCut x(d);
      const auto prepared=x.prepare();
      unsigned w=qualifiedCuts(d,x,prepared);
      assert(w==(debt?12u:15u));
      if(bits(a&w)>1||bits(b&w)>1)continue;
      const int choose=rule(w,force,1,1);
      const int active=choose<0?force:choose;
      assert((active&force)==force);
      if(choose<0)++forcedNoGuarantee;
      for(unsigned j=0;j<2;++j)
          if(active&(1<<j))assert(d.w.b.Register(names[j]));
      bool got=false;
      const auto before=d.presented["Aux"].size();
      for(unsigned i=0;i<cuts.size();++i){
        const bool deadA=(active&1)&&(a&(1u<<i));
        const bool deadB=(active&2)&&(b&(1u<<i));
        x.lackingPose.clear();
        if(deadA)x.lackingPose.insert(names[0]);
        if(deadB)x.lackingPose.insert(names[1]);
        if(got)continue;
        const bool want=(w&(1u<<i))&&!deadA&&!deadB;
        const bool sent=x.commit(prepared,cuts[i]);
        assert(sent==want&&d.w.b.incomingMsgs.empty());
        got |= sent;
      }
      const unsigned combined=(active&1?a:0u)|(active&2?b:0u);
      assert(got==bool(w&~combined));
      assert(choose<0||got);
      if(debt&&force==3&&bits(a&w)==1&&bits(b&w)==1){
          if((a&w)==(b&w)){assert(got);++aligned;}
          else {assert(!got);++opposed;}
      }
      assert(d.presented["Aux"].size()==before+got);
      if(got){++old;assert(d.presented["Aux"].back()==std::make_pair(std::string("D"),diag));}
      x.lackingPose.clear();
      for(unsigned j=0;j<2;++j)if(!(active&(1<<j)))assert(d.w.b.Register(names[j]));
      independentLaterService(d);++late;++runs;
    }
    // Separate native witness: no FIFO pop/debit, but the earlier
    // scanned node's native stamp changes on an unsuccessful call.
    {
      Driver d;d.seed(false);EffectCut x(d);
      assert(d.w.b.Register(names[0])&&d.w.b.Register(names[1]));
      x.lackingPose={names[1]};
      const auto b=d.presented["Aux"].size();
      const auto was=d.w.state(names[0]).update_stamp;
      d.w.b.incomingMsgs.push_back({"D","Aux",diag});
      now=1.375;
      std::ostringstream log;auto *saved=std::cerr.rdbuf(log.rdbuf());
      d.w.b.DispatchMessages();std::cerr.rdbuf(saved);
      assert(log.str().find(names[1])!=std::string::npos);
      assert(d.w.b.incomingMsgs.size()==1&&d.presented["Aux"].size()==b);
      assert(d.w.state("D").bytes_sent_this_epoch==0);
      assert(d.w.state(names[0]).update_stamp==now && was!=now);
      d.w.b.incomingMsgs.clear();
      ++rawStalls;
    }
    assert(choices==1500&&runs==676&&old==644&&late==676&&forcedNoGuarantee==144&&opposed==32&&aligned==32);
    std::cout<<"mask decision comparisons "<<choices<<" native episodes "<<runs<<" old settled "<<old
      <<" all later observer duties "<<late<<" forced unguaranteed "<<forcedNoGuarantee
      <<" opposed failures "<<opposed<<" aligned successes "<<aligned<<" partial native pose writes "<<rawStalls<<"\n";
}
