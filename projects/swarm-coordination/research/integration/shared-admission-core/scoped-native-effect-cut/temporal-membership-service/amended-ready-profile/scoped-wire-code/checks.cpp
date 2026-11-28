#include "temporal_parent.inc"
#include <map>
#include <numeric>

const unsigned W=(1u<<9)-1;
int card9(unsigned x){return __builtin_popcount(x);}
struct Code{
  unsigned b;
  std::vector<unsigned> values;
  explicit Code(unsigned cap):b(cap){
    for(unsigned s=0;s<=W;++s)if(card9(s)<=int(b))values.push_back(s);
    if(b<9)values.push_back(W+1);
  }
  unsigned idx(unsigned s)const{
    const auto x=card9(s)>int(b)?W+1:s;
    auto it=std::find(values.begin(),values.end(),x);
    assert(it!=values.end());
    return it-values.begin();
  }
  bool decode(unsigned n,unsigned u)const{
    assert(n<values.size()&&card9(u)<=int(b));
    return values[n]==W+1 || (values[n]&~u);
  }
};
// Source controller owns its armed availability calendar. This is an
// explicit qualification/reservation in the replay, not a measurement
// or prediction of unconstrained future physical faults.
struct OwnedCalendar{
    unsigned bound;
    std::array<bool,9> reserved{};
    explicit OwnedCalendar(unsigned b,unsigned m):bound(b){
        for(unsigned i=0;i<9;++i)reserved[i]=m&(1u<<i);
    }
    unsigned exportReadiness()const{
        unsigned m=0;
        for(unsigned i=0;i<9;++i)if(reserved[i])m|=1u<<i;
        return m;
    }
};
static std::string packed(unsigned i,bool two){
    std::string out(1,static_cast<char>(i&255));
    if(two)out.push_back(static_cast<char>(i>>8));
    return out;
}
static unsigned unpack(const std::string& v){
    assert(v.size()==1||v.size()==2);
    return static_cast<unsigned char>(v[0])+
        (v.size()==2?256u*static_cast<unsigned char>(v[1]):0u);
}
static std::string dispatch(EffectCut &x,Driver &d, Radio source,
        const std::string& dest,const std::string& v,long long t){
    const auto n=d.presented[dest].size();
    if(!x.dispatchReady())return {};
    const bool ok=d.wire(source,dest,v,t);
    assert(d.presented[dest].size()==n+ok);
    return ok?d.presented[dest].back().second:"";
}
int main(){
    Code c3(3),c4(4);
    assert(c3.values.size()==131&&c4.values.size()==257);
    int comparisons=0;
    std::set<std::vector<bool>> signatures[2];
    for(unsigned b:{3,4}){
      Code x(b);
      for(unsigned s=0;s<=W;++s){
         std::vector<bool> v;
         for(unsigned u=0;u<=W;++u)if(card9(u)<=int(b)){
           bool exact=bool(s&~u);
           assert(exact==x.decode(x.idx(s),u));
           v.push_back(exact);++comparisons;
         }
         signatures[b-3].insert(v);
      }
      assert(signatures[b-3].size()==x.values.size());
    }

    int compactDuty=0, lostRaw=0, oldCompact=0, oldRaw=0, native=0, cap4full=0,
        optionalEarly=0, unsafeControls=0;
    auto service=[](Driver& d,EffectCut& x, unsigned s,unsigned u,bool admits){
       // Existing observer B's local reserved blackout is u; optional
       // observer A really participates in native readiness if admitted.
       assert(d.w.b.Register("Scheduled-B"));
       d.durable[Radio::D]["diagnostic"]=diag;
       if(admits){
          assert(d.w.b.Register("Optional-A"));
          const auto n=d.presented["Aux"].size();
          now=.625;
          d.w.b.incomingMsgs.push_back({"Optional-A","Aux","new"});
          d.w.b.DispatchMessages();
          assert(d.w.b.incomingMsgs.empty());
          assert(d.presented["Aux"].size()==n+1 && d.presented["Aux"].back()==
                     std::make_pair(std::string("Optional-A"),std::string("new")));
          assert(d.w.state("Aux").bytes_received_this_epoch==3);
          d.receive["Aux"].push_back({625000,3});
       }
       const auto p=x.prepare();
       bool paid=false;
       for(unsigned i=0;i<9&&!paid;++i){
          const auto cut=750000+125000*i;
          x.lackingPose.clear();
          if(u&(1u<<i))x.lackingPose.insert("Scheduled-B");
          if(admits&&!(s&(1u<<i)))x.lackingPose.insert("Optional-A");
          paid=x.commit(p,cut);
       }
       if(paid)assert(d.presented["Aux"].back()==std::make_pair(std::string("D"),diag));
       return paid;
    };
    for(unsigned s=0;s<=W;++s){
      for(bool raw:{false,true}){
        Driver d;
        EffectCut x(d);
        const OwnedCalendar schedule(3,s);
        const unsigned state=schedule.exportReadiness();
        const unsigned query=s&7;  // assigned partner omissions in this run
        const Code code(schedule.bound);
        assert(dispatch(x,d,Radio::F,"Base","prior",0)=="prior");
        // The existing slot fixes scope, cut grid, source and cap.
        // Payload carries only the value.
        const auto v=packed(raw?state:code.idx(state),raw);
        const auto got=dispatch(x,d,Radio::D,"Base",v,500000);
        const bool exact=bool(state&~query);
        if(raw){
           assert(got.empty()&&d.w.state("D").bytes_sent_this_epoch==2);
           ++lostRaw;
        }else{
           assert(got==v&&d.w.state("D").bytes_sent_this_epoch==1);
           assert(code.decode(unpack(got),query)==exact);++compactDuty;
        }
        const auto decision=!got.empty()&&code.decode(unpack(got),query);
        assert(decision==(!raw&&exact));
        assert(service(d,x,state,query,decision));
        optionalEarly+=decision;
        if(raw)++oldRaw;
        else ++oldCompact;
        ++native;
      }
    }
    // A wrong compatibility interpretation can truly stall the old
    // service: both masks fit the declared local cap but cover all cuts.
    {
       Driver a,b;
       EffectCut x(a),y(b);
       assert(!service(a,x,7,7,true));
       assert(service(b,y,7,7,false));
       ++unsafeControls;
    }
    // Old saturated payload is observationally equal at cap 3.
    // At cap 4, actual physical continuation can diverge if either
    // side tries to authorize early membership with the old payload.
    assert(c3.idx(15)==c3.idx(31));
    assert(!c4.decode(c4.idx(15),15)&&c4.decode(c4.idx(31),15));
    {
       Driver a,b; EffectCut x(a),y(b);
       assert(!service(a,x,15,15,true));
       assert(service(b,y,31,15,true));
    }
    // Exactly one additional cap-four query class crosses the one-byte
    // cardinality boundary. Forcing its last valid index into one byte
    // folds two distinct classes together, rather than qualifying it.
    assert(c4.values.back()==W+1&&c4.idx(W)==256);
    assert(!c4.decode(0,0)&&c4.decode(c4.idx(W),0));
    assert(!c4.decode(unpack(packed(c4.idx(W),false)),0));
    for(bool two:{false,true}){
       Driver d; EffectCut x(d);
       assert(dispatch(x,d,Radio::F,"Base","prior",0)=="prior");
       const auto v=packed(c4.idx(W),two);
       const auto got=dispatch(x,d,Radio::D,"Base",v,500000);
       if(two){assert(got.empty());++cap4full;}
       else {assert(got==v&&!c4.decode(unpack(got),0));}
    }
    assert(comparisons==197632&&compactDuty==512&&lostRaw==512&&native==1024&&oldRaw==512&&oldCompact==512&&cap4full==1&&optionalEarly==504&&unsafeControls==1);
    std::cout<<"abstract query tests "<<comparisons<<" exact classes 131/257 native cases "<<native
             <<" qualified one-byte deliveries "<<compactDuty<<" two-byte raw blocked "<<lostRaw
             <<" old audits "<<oldRaw+oldCompact<<" new early reports "<<optionalEarly
             <<" unsafe early admission controls "<<unsafeControls<<" amended stale profile branch failures 1 amended two-byte blocked "<<cap4full<<"\n";
}
