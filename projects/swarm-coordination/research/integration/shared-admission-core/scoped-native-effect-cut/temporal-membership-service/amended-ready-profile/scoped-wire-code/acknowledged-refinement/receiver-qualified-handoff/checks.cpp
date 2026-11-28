#include "handoff_parent.inc"

struct ScopedAck{std::shared_ptr<TeamNode> allocation; unsigned parent;};
static ScopedAck acknowledgment(Driver& d,unsigned parent,double t,bool available){
    d.w.b.endpoints["D:7"]={{"D"}};
    ScopedAck answer{nullptr,0};
    const auto sender=d.w.b.team->at("Base");
    d.w.app.callbacks["D:7"]=[&](auto from,auto,auto,auto bytes){
        assert(from=="Base"&&unpack(bytes)==parent);
        if(available)answer={sender,unpack(bytes)};
    };
    now=t;
    d.w.b.incomingMsgs.push_back({"Base","D",packed(parent,false)});
    d.w.b.DispatchMessages();
    d.w.app.callbacks.erase("D:7");
    assert(d.w.b.incomingMsgs.empty());
    return answer;
}
int main(){
    Amendment a;
    unsigned cases=0,protectedAudit=0,early=0,staleFailures=0;
    for(unsigned s:{0u,15u,16u,31u,W})
    for(bool transfer:{false,true})
    for(bool nextAck:{false,true})
    for(bool staleProjection:{false,true}){
        if(nextAck&&!transfer)continue;
        Driver d;EffectCut x(d);
        const unsigned parent=a.coarser.idx(s);
        const std::string old=packed(parent,false);
        // An independently authorized archive receives the exact old record.
        d.w.b.endpoints["F:7"]={{"F"}};
        d.w.app.callbacks["F:7"]=[&](auto src,auto,auto,auto payload){
            assert(src=="D");d.presented["F"].emplace_back(src,payload);
        };
        assert(dispatch(x,d,Radio::D,"F",old,-2250000)==old);
        assert(dispatch(x,d,Radio::D,"Base",old,-2000000)==old);
        const auto oldAck=acknowledgment(d,parent,-1.875,true);
        assert(oldAck.allocation&&oldAck.parent==parent);
        unsigned newCache=parent;
        const auto oldOwner=oldAck.allocation;
        assert(d.w.b.Unregister("Base")&&d.w.b.Register("Base"));
        assert(d.w.b.team->at("Base")!=oldOwner);
        d.w.b.endpoints["Base:7"]={{"Base"}};
        d.receive["Base"].clear();d.presented["Base"].clear();
        ScopedAck newest=oldAck;
        if(transfer){
            const auto carried=d.presented["F"].back().second;
            assert(dispatch(x,d,Radio::F,"Base",carried,-1625000)==old);
            newest=acknowledgment(d,parent,-1.5,nextAck);
        }else{
            // A formerly bound, unrelated subject is a distinct receipt,
            // not a usable base for this plan's one-byte amendment.
            newCache=a.coarser.idx(16);
            assert(dispatch(x,d,Radio::F,"Base",packed(newCache,false),-1625000)==packed(newCache,false));
        }
        assert(dispatch(x,d,Radio::F,"Base","prior",0)=="prior");
        const bool scopeGood=newest.allocation==d.w.b.team->at("Base") && newest.parent==parent;
        assert(scopeGood==(transfer&&nextAck));
        bool admit=false;
        const unsigned u=s&15;
        const bool planSafe=bool(s&~u);
        if(scopeGood||staleProjection&&!transfer){
            const auto i=a.indexInFiber(s,parent);
            if(a.fiber.at(parent).size()>1){
               auto msg=dispatch(x,d,Radio::D,"Base",packed(i,false),500000);
               assert(msg==packed(i,false));
            }
            // Diagnostic ablation trusts the alias and ignores that the
            // cache is not the old subject. It can misdecode index 0.
            const auto decoded=i<a.fiber.at(newCache).size()?a.answer(newCache,i,u):false;
            admit=decoded;
            if(scopeGood) assert(admit==planSafe);
        }
        const bool audit=service(d,x,s,u,admit);
        if(!staleProjection||transfer)assert(audit);
        if(!audit){
            assert(staleProjection&&!transfer&&(s==15||s==0));
            ++staleFailures;
        }
        protectedAudit+=audit;early+=admit;++cases;
    }
    assert(cases==30&&staleFailures==2&&protectedAudit==28);
    std::cout<<"native receiver substitutions "<<cases<<" old audits "<<protectedAudit
             <<" early work "<<early<<" stale-alias false admissions "<<staleFailures<<"\n";
}
