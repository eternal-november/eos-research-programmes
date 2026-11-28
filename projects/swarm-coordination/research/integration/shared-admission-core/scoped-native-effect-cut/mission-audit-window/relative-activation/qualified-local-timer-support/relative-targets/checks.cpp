#include "temporal_parent.inc"
using P=std::array<int,2>;
bool viable(P clocks,P h){
    P t{std::max(2,h[0]-clocks[0]),std::max(2,h[1]-clocks[1])};
    return std::min(t[0],t[1])>=3 && std::max(t[0],t[1])<=9
        && (std::max(t[0],t[1])<=4||std::min(t[0],t[1])>6);
}
struct Outcome{bool old; P at; int certificate;};
Outcome run(P clocks,bool full,int policy){
    Driver d;EffectCut guard(d);
    const std::array<std::string,2> names{"IntervalA","IntervalB"};
    P armed{-1,-1},act{-1,-1};
    for(int i=0;i<2;++i){
        const auto& name=names[i];
        assert(d.w.b.Register(name));
        d.w.b.endpoints[name+":7"]={{name}};
        d.w.app.callbacks[name+":7"]=[&,i](auto who,auto,auto,const auto& input){
            assert(who=="F"&&input.size()==1&&armed[i]<0);
            armed[i]=int(input[0]);
        };
    }
    assert(d.wire(Radio::B,"Base",full?"owed!!":"owed!",0));
    // Controlled calibration source observes both actual local clock
    // values at one physical sample. It exports only their difference.
    const auto reference=[](int tick,int offset){return tick+offset;};
    const int delta=reference(1,clocks[1])-reference(1,clocks[0]);
    const auto payload=std::string(1,char(delta+4));
    assert(d.wire(Radio::F,"Base",payload,125000)==!full);
    P plan{-1,-1};
    if(policy==2)plan={5,5}; // diagnostic raw-code ablation
    else if(!full){
        const int supplied=d.presented["Base"].back().second.at(0)-4;
        assert(supplied==delta);
        if(policy==0){
            const int base=supplied<0?4:supplied>0?1:5;
            plan={base,base+supplied};
        }else{
            int best=100;
            for(int x=0;x<=10;++x)for(int y=0;y<=10;++y){
                bool ok=true;
                int worst=0;
                for(int a:{1,-2})for(int b:{1,-2})if(b-a==supplied){
                    ok&=viable({a,b},{x,y});
                    worst=std::max({worst,x-a,y-b,2});
                }
                if(ok&&worst<best){plan={x,y};best=worst;}
            }
        }
    }
    if(plan[0]>=0){
        for(int i=0;i<2;++i){
            now=.25;
            d.w.b.incomingMsgs.push_back({"F",names[i],std::string(1,char(plan[i]))});
            d.w.b.DispatchMessages();
            assert(d.w.b.incomingMsgs.empty()&&armed[i]==plan[i]);
        }
    }
    d.durable[Radio::D]["diagnostic"]=diag;
    const auto prepared=guard.prepare();
    bool old=false;
    for(int t=2;t<=9;++t){
        for(int i=0;i<2;++i)
            if(armed[i]>=0&&act[i]<0&&t+clocks[i]>=armed[i])act[i]=t;
        if(t==4||t==6){
            guard.lackingPose.clear();
            for(int i=0;i<2;++i)if(t==4?act[i]<0:act[i]>=0)guard.lackingPose.insert(names[i]);
            if(!old)old=guard.commit(prepared,125000*t);
        }
    }
    return {old,act,int(!full)};
}
int main(){
    std::map<int,std::vector<P>> histories;
    for(int a:{1,-2})for(int b:{1,-2})histories[b-a].push_back({a,b});
    std::map<int,std::set<P>> feasible;
    for(auto [k,hs]:histories){
      for(int a=0;a<=10;++a)for(int b=0;b<=10;++b)
         if(std::all_of(hs.begin(),hs.end(),[&](auto s){return viable(s,{a,b});}))
             feasible[k].insert({a,b});
      assert(feasible[k].count({5,5+k}));
      if(k)assert(std::none_of(feasible[k].begin(),feasible[k].end(),[](auto p){return p[0]==p[1];}));
    }
    for(const auto &[k,x]:feasible)for(const auto &[j,y]:feasible)if(j!=k)
       for(auto p:x)assert(!y.count(p));
    // Even an encoding of the full hidden pair cannot merge a
    // mixed world with any other world and still output ONE vector.
    for(int k:{-3,3})for(const auto& s:histories[k])
        for(const auto& [l, rest]:histories)if(l!=k)
            for(const auto& t:rest)
                for(int a=0;a<=10;++a)for(int b=0;b<=10;++b)
                    assert(!(viable(s,{a,b})&&viable(t,{a,b})));
    int measured=0,achieved=0,refused=0,rawMiss=0;
    for(int a:{1,-2})for(int b:{1,-2})for(bool full:{false,true}){
       auto x=run({a,b},full,0),y=run({a,b},full,1),z=run({a,b},full,2);
       assert(x.old&&x.old==y.old&&x.at==y.at);
       const int live=full?-1:a==b?5-a:3;
       assert(x.at==(P{live,live})&&x.certificate==!full);
       if(full)++refused;else ++achieved;
       rawMiss+=!z.old;++measured;
    }
    assert(measured==8&&achieved==4&&refused==4&&rawMiss==4);
    std::cout<<"distinct necessary relation classes "<<feasible.size()
      <<" native paired histories "<<measured<<" both deadlines via relative "<<achieved
      <<" safe deferrals after loss "<<refused<<" stale common-target misses "<<rawMiss<<"\n";
}
