#include <array>
#include <cassert>
#include <set>
#define main embedded_native_tests
#include "staged_replay.inc"
#undef main

enum class Radio {A,B,D,F};
using Word = std::string;
static const Radio dirty = Radio::A;
static const Radio clean = Radio::B;
static const Word payload="x7Z", diag="d#2";
struct Debit{long long tick; unsigned bytes;};
struct Request{std::string key, dest; Radio subject; unsigned gen;};
// Declared physical fixture: P/Q are only transport handles. A/B/D/F
// are actual admitted radio principals in the model. No inference
// from native address or native member identity to a principal.
struct Driver{
    World w{6};
    std::array<std::string,4> addr{"P","Q","D","F"};
    unsigned gen=0;
    std::map<Radio,std::vector<Debit>> physical;
    std::map<std::string,std::vector<Debit>> receive;
    std::map<Radio,std::map<std::string,Word>> durable;
    std::vector<std::tuple<Radio,std::string,Word>> outcomes;
    std::map<std::string,std::vector<std::pair<std::string,Word>>> presented;
    Driver(){
        w.b.default_radio_configuration=w.b.team->at("P")->radio;
        for(std::string n:{"D","F","Aux"})assert(w.b.Register(n));
        for(std::string n:{"Aux","P"})w.b.endpoints[n+":7"].push_back({n});
        for(std::string n:{"Base","Aux","P","Q"})
          w.app.callbacks[n+":7"]=[this,n](auto s,auto,auto,auto v){presented[n].emplace_back(s,v);};
    }
    static unsigned used(const std::vector<Debit>& b,long long t){
        unsigned total=0;
        for(auto d:b)if(d.tick>=t-1000000)total+=d.bytes;
        return total;
    }
    std::string name(Radio p)const{return addr.at(static_cast<int>(p));}
    void rebind(bool swap){
        auto oldP=w.b.team->at("P"),oldQ=w.b.team->at("Q");
        assert(w.b.Unregister("P")&&w.b.Unregister("Q"));
        assert(w.b.Register("P")&&w.b.Register("Q"));
        assert(w.b.team->at("P")!=oldP&&w.b.team->at("Q")!=oldQ);
        addr[0]=swap?"Q":"P"; addr[1]=swap?"P":"Q";
        assert(w.state("P").bytes_sent_this_epoch==0&&w.state("Q").bytes_sent_this_epoch==0);
        ++gen;
    }
    bool wire(Radio p,std::string d,Word v,long long t,bool good=true){
        const auto s=name(p);
        const double at=t/1000000.0;
        const auto before=presented[d].size();
        assert(used(physical[p],t)+v.size()<=6);
        physical[p].push_back({t,static_cast<unsigned>(v.size())});
        w.path_available=good;
        now=at;
        w.b.incomingMsgs.push_back({s,d,v});
        w.b.DispatchMessages();
        assert(w.b.incomingMsgs.empty());
        const bool live=presented[d].size()!=before;
        const bool expected=good&&used(receive[d],t)+v.size()<=6;
        assert(live==expected);
        if(live){
            const auto observed=std::make_pair(s,v);
            assert(presented[d].back()==observed);
            receive[d].push_back({t,static_cast<unsigned>(v.size())});
            assert(w.state(d).bytes_received_this_epoch==used(receive[d],t));
            outcomes.emplace_back(p,d,v);
        }
        return live;
    }
    void seed(bool rxBusy){
        // Two replicas receive the exact old receipt via native broker
        // before the accounting window under study.
        for(auto p:{dirty,clean}){
            const auto d=name(p);
            assert(wire(Radio::F,d,payload,-2000000));
            durable[p]["old-q"]=presented[d].back().second;
        }
        durable[Radio::D]["diagnostic"]=diag;
        assert(!wire(dirty,"Base","lost",0,false));
        assert(w.state("P").bytes_sent_this_epoch==4);
        if(rxBusy)assert(wire(Radio::F,"Base","owed",250000));
    }
    const Word* value(const Request& q)const{
        const auto a=durable.find(q.subject);
        if(a==durable.end())return nullptr;
        const auto v=a->second.find(q.key);
        if(v==a->second.end())return nullptr;
        return &v->second;
    }
    bool apply(const Request& q,long long t,unsigned installed_gen){
        const Word* content=value(q);
        if(!content||installed_gen!=gen||q.gen!=gen)return false;
        if(q.subject==clean||q.subject==dirty){
            if(q.key!="old-q"||q.dest!="Base")return false;
        }else if(q.subject!=Radio::D||q.key!="diagnostic"||q.dest!="Aux")return false;
        if(used(physical[q.subject],t)+content->size()>6||
           used(receive[q.dest],t)+content->size()>6)return false;
        return wire(q.subject,q.dest,*content,t);
    }
};
// Independent reference on physical identities and authenticated payloads,
// with no mention of routing handle or engine version. Captured versions only
// enter the compare as a constraint across the entire commit boundary.
static bool reference(Radio s,std::string key,std::string d,bool current,bool busy,long long cut){
    if(!current)return false;
    if(s==Radio::D)return key=="diagnostic"&&d=="Aux";
    if(s!=dirty&&s!=clean)return false;
    if(key!="old-q"||d!="Base")return false;
    return !(s==dirty&&cut<=1000000) && !(busy&&cut<=1250000);
}
int main(){
    unsigned cases=0,delivered=0,diags=0,staleRefused=0,wrongRefused=0,planEquations=0;
    for(bool firstSwap:{false,true})
    for(bool lastSwap:{false,true})
    for(bool secondChange:{false,true})
    for(bool rxBusy:{false,true})
    for(long long cut:{500000,1000000,1125000,1250000,1375000})
    for(auto req:{0,1,2,3}){
      Driver drv;
      drv.seed(rxBusy);
      drv.rebind(firstSwap);
      const auto prepared=drv.gen;
      const auto dirty_before=drv.name(dirty), clean_before=drv.name(clean);
      std::string key=req==2?"different":"old-q", dest=req==3?"Aux":"Base";
      const Radio selected=req==1?dirty:clean;
      if(secondChange)drv.rebind(lastSwap);
      const auto before=drv.outcomes.size();
      const auto new_credit=drv.w.state(drv.name(selected)).bytes_sent_this_epoch;
      assert(new_credit==0);
      const Request request{key,dest,selected,prepared};
      const bool got=drv.apply(request,cut,prepared);
      const bool expected=reference(selected,key,dest,!secondChange,rxBusy,cut);
      assert(got==expected && drv.outcomes.size()==before+got);
      if(got){
          assert(drv.presented["Base"].back().first==drv.name(selected));
          assert(drv.presented["Base"].back().second==payload);
          ++delivered;
      }else assert(drv.w.state(drv.name(selected)).bytes_sent_this_epoch==0);
      if(secondChange){assert(!got);++staleRefused;}
      if(req>=2){assert(!got);++wrongRefused;}
      // Compare rebinding with recomputing the test at the actual cut.
      // Driver version constrains an ADDRESS-*prepared* request above;
      // explicit fresh, live physical resolution may recover before commit.
      if(secondChange) {
          bool repaired=drv.apply({key,dest,selected,drv.gen},cut,drv.gen);
          const bool fresh=reference(selected,key,dest,true,rxBusy,cut);
          assert(repaired==fresh);
          if(repaired)assert(drv.presented["Base"].back().first==drv.name(selected));
          ++planEquations;
      }
      // Independent activity survives every unrelated denial/rebind.
      assert(drv.apply({"diagnostic","Aux",Radio::D,drv.gen},cut,drv.gen));
      assert(drv.presented["Aux"].back()==std::make_pair(std::string("D"),diag));
      ++diags;++cases;
    }
    assert(cases==320&&delivered==40&&diags==320&&staleRefused==160&&wrongRefused==160&&planEquations==160);
    std::cout<<"fixtures "<<cases<<" first-delivery "<<delivered<<" separate diagnostic "<<diags
             <<" stale refused "<<staleRefused<<" wrong scope refused "<<wrongRefused
             <<" fresh-binding equations "<<planEquations<<"\n";
}
