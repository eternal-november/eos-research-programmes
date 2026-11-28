#include "temporal_parent.inc"

using Pair=std::array<int,2>;
constexpr int first=4,last=6, earliest=3,deadline=9;
struct History { Pair arm,offset; };
Pair applied(History h,int target){
    return {std::max(h.arm[0],target-h.offset[0]),std::max(h.arm[1],target-h.offset[1])};
}
bool ordinary(History h,int target){
    const auto t=applied(h,target);
    const int lo=std::min(t[0],t[1]),hi=std::max(t[0],t[1]);
    return earliest<=lo&&hi<=deadline&&(hi<=first||lo>last);
}
bool projected(History h,int target){
    bool range=true, early=true, late=true;
    for(int i=0;i<2;++i){
       range&=(h.arm[i]>=earliest||target>=earliest+h.offset[i])
          &&h.arm[i]<=deadline&&target<=deadline+h.offset[i];
       early&=h.arm[i]<=first&&target<=first+h.offset[i];
       late&=h.arm[i]>last||target>last+h.offset[i];
    }
    return range&&(early||late);
}
std::vector<int> candidates(const std::vector<History>& support){
    assert(!support.empty() && support.front().arm[0] <= deadline);
    // At least one reference history limits a valid target above by
    // its deadline + clock offset. No arbitrary upper search cutoff.
    int upper=deadline+support.front().offset[0];
    std::vector<int> result;
    // The command interface here accepts a nonnegative integer sample.
    for(int h=0;h<=upper;++h)
        if(std::all_of(support.begin(),support.end(),[&](auto p){return projected(p,h);}))
            result.push_back(h);
    return result;
}

struct Record { Pair switchAt; bool audit; unsigned armSend; };
Record native(int target,Pair offset,int saturatedReceiver,bool fanout){
    Driver d;
    EffectCut boundary(d);
    Pair switchAt{-1,-1},armed{-1,-1};
    const std::array<std::string,2> ids{"TimedA","TimedB"};
    std::array<CommsClient,2> endpointClients;
    for(unsigned i=0;i<ids.size();++i){
        assert(d.w.b.Register(ids[i]));
        d.w.b.endpoints[ids[i]+":7"]={{ids[i]}};
        d.w.b.node.namedClients[ids[i]]=&endpointClients[i];
        auto armCallback=[&,i](auto from,auto,auto,const auto& payload){
            if(from=="P"){assert(payload=="older!");return;}
            assert(from=="F"&&payload==std::string(1,char(target))&&armed[i]<0);
            armed[i]=int(now*8);
        };
        endpointClients[i].callbacks[ids[i]+":7"]=armCallback;
        endpointClients[i].callbacks["group:7"]=armCallback;
    }
    if(saturatedReceiver>=0){
       now=0;
       d.w.b.incomingMsgs.push_back({"P",ids[saturatedReceiver],"older!"});
       d.w.b.DispatchMessages();
       assert(d.w.state(ids[saturatedReceiver]).bytes_received_this_epoch==6);
    }
    unsigned attempts=0;
    std::string rule(1,char(target));
    now=.125;
    if(fanout){
       d.w.b.endpoints["group:7"]={{ids[0]},{ids[1]}};
       d.w.b.incomingMsgs.push_back({"F","group",rule});++attempts;
    }else for(auto name:ids){d.w.b.incomingMsgs.push_back({"F",name,rule});++attempts;}
    d.w.b.DispatchMessages();
    assert(d.w.b.incomingMsgs.empty());
    assert(d.w.state("F").bytes_sent_this_epoch==2); // per actual native recipient attempt
    for(int i=0;i<2;++i)assert(armed[i]==(i==saturatedReceiver?-1:1));
    d.durable[Radio::D]["diagnostic"]=diag;
    const auto prep=boundary.prepare();
    bool old=false;
    for(int t=2;t<=deadline+1;++t){
        // Each observer's own already-armed timer sees only its local
        // clock. Certification of a support does not reveal its offset.
        for(int i=0;i<2;++i)
            if(armed[i]>=0&&switchAt[i]<0&&t+offset[i]>=target)
                switchAt[i]=t;
        if(t==first||t==last){
            boundary.lackingPose.clear();
            for(int i=0;i<2;++i)
                if(t==first ? switchAt[i]<0 : switchAt[i]>=0)
                    boundary.lackingPose.insert(ids[i]);
            if(!old)old=boundary.commit(prep,125000*t);
        }
    }
    return {switchAt,old,attempts};
}
int main(){
    int algebra=0;
    for(int a=0;a<12;++a)for(int b=0;b<12;++b)
    for(int x=-4;x<=4;++x)for(int y=-4;y<=4;++y)
    for(int h=0;h<15;++h){
        History k{{a,b},{x,y}};
        assert(ordinary(k,h)==projected(k,h));++algebra;
    }
    std::vector<History> common{{{1,1},{1,1}},{{1,1},{-2,-2}}}, product;
    for(int x:{1,-2})for(int y:{1,-2})product.push_back({{1,1},{x,y}});
    const auto target=candidates(common);
    assert((target==std::vector<int>{5})&&candidates(product).empty());
    int success=0,projectedFailure=0,fanoutFailure=0;
    for(int x:{1,-2})for(int y:{1,-2})for(bool broadcast:{false,true}){
       auto r=native(target[0],{x,y},-1,broadcast);
       assert(r.switchAt==applied({{1,1},{x,y}},target[0]));
       assert(r.audit==(x==y));
       assert(r.armSend==(broadcast?1:2));
       success+=r.audit;projectedFailure+=!r.audit;
    }
    for(int blocked:{0,1}){
        auto c=native(target[0],{1,1},blocked,true);
        assert(!c.audit&&c.switchAt[blocked]==-1&&c.switchAt[1-blocked]==4);
        assert(c.armSend==1);
        ++fanoutFailure;
    }
    assert(algebra==174960&&success==4&&projectedFailure==4&&fanoutFailure==2);
    std::cout<<"closed versus direct tests "<<algebra<<" common target 5 product has none"
             <<" native protected "<<success<<" split-clock misses "<<projectedFailure
             <<" same-clock partial-fanout misses "<<fanoutFailure<<"\n";
}
