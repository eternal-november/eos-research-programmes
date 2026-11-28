#include "temporal_parent.inc"
#include <array>

static constexpr std::array<long long,4> times{500000,1250000,1375000,1500000};
static const std::array<std::string,3> ids{"Observer-A","Observer-B","Observer-C"};
inline int card(unsigned x){return __builtin_popcount(x);}
struct Cover{unsigned eligible;std::array<unsigned,3> support;std::array<int,3> cap;};
int cover(Cover c,unsigned activated){
    // Each capacity is expanded into interchangeable unit slots.
    // Augmenting paths construct a matching of distinct eligible cuts.
    std::vector<unsigned> slot;
    for(int i=0;i<3;++i)if(activated&(1u<<i))
        for(int v=0;v<c.cap[i];++v)slot.push_back(c.support[i]&c.eligible);
    std::vector<int> from(slot.size(),-1);
    std::function<bool(int,std::vector<bool>&)> augment=[&](int cut,std::vector<bool>& touched){
        for(unsigned j=0;j<slot.size();++j){
            if(!(slot[j]&(1u<<cut))||touched[j])continue;
            touched[j]=true;
            if(from[j]<0||augment(from[j],touched)){from[j]=cut;return true;}
        }
        return false;
    };
    int ans=0;
    for(int i=0;i<4;++i)if(c.eligible&(1u<<i)){
        std::vector<bool> seen(slot.size(),false);
        ans+=augment(i,seen);
    }
    return ans;
}
int direct(Cover c,unsigned active){
    // Literal powerset product, independent of the matching algorithm.
    std::set<unsigned> total{0};
    for(int i=0;i<3;++i)if(active&(1u<<i)){
        std::set<unsigned> next;
        const unsigned choices=c.support[i]&c.eligible;
        for(unsigned sub=choices;;sub=(sub-1)&choices){
            if(card(sub)<=c.cap[i]) for(auto v:total)next.insert(sub|v);
            if(!sub)break;
        }
        total=std::move(next);
    }
    int answer=0;
    for(auto v:total)answer=std::max(answer,card(v));
    return answer;
}
unsigned activate(Cover c,bool exact,unsigned roster){
    unsigned best=0;
    for(unsigned s=0;s<8;++s){
        if(s&~roster)continue;
        int size=0;
        if(exact)size=cover(c,s);
        else for(int i=0;i<3;++i)if(s&(1u<<i))size+=c.cap[i];
        if(size<card(c.eligible)&&card(s)>card(best))best=s;
    }
    return best;
}
void otherWork(Driver &d,const std::string& actor,double t){
    auto before=d.presented["Base"].size();
    now=t;
    d.w.b.incomingMsgs.push_back({actor,"Base",std::string(1,'s')});
    d.w.b.DispatchMessages();
    assert(d.w.b.incomingMsgs.empty()&&d.presented["Base"].size()==before+1);
    assert(d.presented["Base"].back()==std::make_pair(actor,std::string("s")));
}
int main(){
    int checks=0;
    for(unsigned w=1;w<16;++w)
    for(unsigned a=0;a<16;++a)for(unsigned b=0;b<16;++b)for(unsigned c=0;c<16;++c){
      Cover f{w,{a,b,c},{1,2,1}};
      for(unsigned active=1;active<8;++active){
        assert(cover(f,active)==direct(f,active));
        ++checks;
      }
    }
    unsigned r=0,old=0,advanced=0,same=0;
    // Native case: both admission strategies see the same declared support
    // and complete the same later observer duties; the direct powerset
    // method would pick the same active set as the matching policy.
    for(unsigned c0:{4u,8u,12u})for(unsigned c1:{4u,8u,12u}){
      Cover f{12,{c0,c1,0},{1,1,1}};
      const auto exact=activate(f,true,3);
      const auto coarse=activate(f,false,3);
      assert(exact==((c0==c1&&c0!=12)?3u:1u)&&coarse==1);
      for(unsigned a:{0u,4u,8u})for(unsigned b:{0u,4u,8u}){
        if((a&~c0)||(b&~c1))continue;
        std::array<int,2> early{0,0};
        for(bool detailed:{false,true}){
          const unsigned active=detailed?exact:coarse;
          Driver d;d.seed(false);
          assert(d.wire(Radio::F,"Aux","owed",250000));
          EffectCut x(d);const auto p=x.prepare();
          assert(!x.commit(p,times[0]));
          for(unsigned i=0;i<2;++i)if(active&(1u<<i))assert(d.w.b.Register(ids[i]));
          // Both sources are qualified up to the early observation cut.
          for(unsigned i=0;i<2;++i)if(active&(1u<<i))otherWork(d,ids[i],.75);
          early[detailed]=card(active);
          bool done=false;
          for(unsigned i=1;i<4&&!done;++i){
             x.lackingPose.clear();
             if((active&1)&&(a&(1u<<i)))x.lackingPose.insert(ids[0]);
             if((active&2)&&(b&(1u<<i)))x.lackingPose.insert(ids[1]);
             done=x.commit(p,times[i]);
          }
          assert(done&&d.presented["Aux"].back()==std::make_pair(std::string("D"),diag));
          ++old;
          x.lackingPose.clear();
          for(unsigned i=0;i<2;++i)if(!(active&(1u<<i))){
             assert(d.w.b.Register(ids[i]));
             otherWork(d,ids[i],1.625);
          }
          assert(d.presented["Base"].size()==2);
        }
        if(early[1]>early[0])++advanced;
        else {assert(early[0]==early[1]);++same;}
        ++r;
      }
    }
    assert(checks==430080&&r==49&&old==98&&advanced==8&&same==41);
    std::cout<<"matching versus product "<<checks<<" paired native schedules "<<r
      <<" old results "<<old<<" additional early observer result "<<advanced<<" ties "<<same<<"\n";
}
