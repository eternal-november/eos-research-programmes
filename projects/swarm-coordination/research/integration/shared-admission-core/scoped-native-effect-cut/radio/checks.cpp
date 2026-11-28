#include <sstream>
#include "parent.inc"
#include "cut_contract.h"

struct EffectCut{
    // This cut is controlled by the wrapper. It is not a claim that the
    // stock broker exposes an atomic external check-and-dispatch API.
    Driver &d;
    std::set<std::string> lackingPose;
    unsigned admissionLaw=0;
    explicit EffectCut(Driver &d):d(d){
        d.w.b.pose_update_f=[this](const auto& n){
            return std::make_tuple(lackingPose.count(n)==0,Pose{},now);
        };
    }
    ~EffectCut(){d.w.b.pose_update_f={};}
    std::shared_ptr<TeamNode> node(const std::string& n)const{
        auto it=d.w.b.team->find(n);
        return it==d.w.b.team->end()?nullptr:it->second;
    }
    struct Prepared {
        std::string source,dest;
        std::shared_ptr<TeamNode> from,to;
        unsigned law;
    };
    Prepared prepare()const{
        return {"D","Aux",node("D"),node("Aux"),admissionLaw};
    }
    bool bestDirectScope(const Prepared& p)const{
        // Primitive caller-independent checks for contents/destination and
        // two native allocation instances. No raw global generation guard.
        if(admissionLaw!=p.law || p.source!="D" || p.dest!="Aux")return false;
        if(!p.from||!p.to || node("D")!=p.from || node("Aux")!=p.to)return false;
        auto it=d.w.b.endpoints.find("Aux:7");
        return it!=d.w.b.endpoints.end()&&it->second.size()==1&&it->second[0].address=="Aux";
    }
    bool dispatchReady()const{
        // Explicit independent native dependency: DispatchMessages reads
        // poses for ALL currently registered nodes before any pop or send.
        for(const auto& [n,entry]:*d.w.b.team)
            if(lackingPose.count(entry->name))return false;
        return true;
    }
    bool commit(const Prepared& p,long long cut){
        // This is a NEW native radio effect even though its content
        // is an old stored exact result. It cannot use inspect mode.
        const Request q{"diagnostic","Aux",Radio::D,d.gen};
        const Word* value=d.value(q);
        const bool room=value&&d.used(d.physical[q.subject],cut)+value->size()<=6&&
                               d.used(d.receive[q.dest],cut)+value->size()<=6;
        const auto profile=cut::Profile{cut::Act::effect,bestDirectScope(p),value!=nullptr,room,dispatchReady()};
        if(cut::check(profile)!=cut::enable)return false;
        return d.wire(q.subject,q.dest,*value,cut);
    }
    void replace(const std::string& n) {
        auto prev=node(n);
        assert(prev && d.w.b.Unregister(n) && d.w.b.Register(n));
        assert(prev!=node(n));
    }
};
int main(){
    unsigned cases=0,carried=0,globalInvalidated=0,blockedAdmission=0;
    unsigned nativeGlobalStalls=0,resumed=0,endpointAliases=0;
    for(bool swapped:{false,true})
    for(bool targetMoved:{false,true})
    for(bool sourceMoved:{false,true})
    for(bool lawChanged:{false,true})
    for(bool readied:{false,true})
    for(bool extraSubscriber:{false,true})
    for(bool endpointDebit:{false,true}){
        Driver d;
        d.seed(false);
        if(endpointDebit)assert(d.wire(Radio::F,"Aux","owed",250000));
        EffectCut x(d);
        const auto prepared=x.prepare();
        const auto epoch=d.gen;
        d.rebind(swapped);
        assert(epoch!=d.gen); // every conservative global token invalidates
        if(targetMoved){
            x.replace("Aux");
            // The receiver's same modeled resource keeps its prior debit
            // in the enclosing contract even when native re-registration
            // clears the old receive state. Reusing the prepared token is
            // inadmissible either way; no resource join is inferred here.
        }
        if(sourceMoved)x.replace("D");
        if(lawChanged)++x.admissionLaw;
        assert(d.w.b.Register("NewObserver"));
        if(!readied)x.lackingPose.insert("NewObserver");
        if(extraSubscriber)d.w.b.endpoints["Aux:7"].push_back({"Base"});
        const bool distinct=!targetMoved&&!sourceMoved&&!lawChanged&&!extraSubscriber;
        const auto before=d.outcomes.size();
        const bool sent=x.commit(prepared,500000);
        const bool simple=distinct&&readied&&!endpointDebit;
        assert(sent==simple && d.outcomes.size()==before+sent);
        if(sent){++carried;assert(d.presented["Aux"].back()==std::make_pair(std::string("D"),diag));}
        else{++blockedAdmission;assert(d.w.state("D").bytes_sent_this_epoch==0);}
        assert(d.w.b.incomingMsgs.empty());
        if(extraSubscriber){assert(!sent);++endpointAliases;}
        // Controlled comparison exercising the native check, without a
        // committed validation in the wrapper. Never drain unintended work.
        if(!readied && distinct && !endpointDebit){
            const auto before2=d.presented["Aux"].size();
            d.w.b.incomingMsgs.push_back({"D","Aux",diag});
            now=.5;
            std::ostringstream discarded;
            auto* old=std::cerr.rdbuf(discarded.rdbuf());
            d.w.b.DispatchMessages();
            std::cerr.rdbuf(old);
            assert(discarded.str().find("Problem getting state for NewObserver")!=std::string::npos);
            assert(d.w.b.incomingMsgs.size()==1&&d.presented["Aux"].size()==before2);
            assert(d.w.state("D").bytes_sent_this_epoch==0);
            d.w.b.incomingMsgs.clear();
            ++nativeGlobalStalls;
            // This test authority can remove only the provisional observer.
            // The unchanged diagnostic's two allocations and law then still
            // qualify with no reissue of its original token.
            assert(d.w.b.Unregister("NewObserver"));
            assert(x.commit(prepared,500000));
            assert(d.presented["Aux"].back()==std::make_pair(std::string("D"),diag));
            ++resumed;
        }
        ++globalInvalidated;++cases;
    }
    assert(cases==128&&carried==2&&globalInvalidated==128&&blockedAdmission==126&&
       nativeGlobalStalls==2&&resumed==2&&endpointAliases==64);
    std::cout<<"fixture cases "<<cases<<" retained prepared sends "<<carried
             <<" global epoch refusals "<<globalInvalidated<<" scoped refusals "<<blockedAdmission
             <<" native global pose stalls "<<nativeGlobalStalls<<" resumed after qualified removal "<<resumed
             <<" rejected known fanout changes "<<endpointAliases<<"\n";
}
