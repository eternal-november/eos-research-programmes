#include "prior_code.inc"

struct Amendment{
    Code coarser{3}, finer{4};
    std::vector<std::vector<unsigned>> fiber;
    Amendment():fiber(coarser.values.size()){
        for(unsigned k=0;k<finer.values.size();++k){
            const unsigned s=std::min(finer.values[k],W);
            fiber[coarser.idx(s)].push_back(k);
        }
        assert(fiber.back().size()==127);
        for(unsigned k=0;k+1<fiber.size();++k)assert(fiber[k].size()==1);
    }
    unsigned indexInFiber(unsigned s,unsigned confirmed)const{
        assert(coarser.idx(s)==confirmed);
        const unsigned k=finer.idx(s);
        const auto& x=fiber.at(confirmed);
        auto pos=std::find(x.begin(),x.end(),k);
        assert(pos!=x.end());
        return pos-x.begin();
    }
    bool answer(unsigned confirmed,unsigned supplement,unsigned u)const{
        return finer.decode(fiber.at(confirmed).at(supplement),u);
    }
};
std::string qualifiedPrevious(const Amendment& a,Driver& d,EffectCut& x,unsigned s,bool loseReply=false){
    const auto v=packed(a.coarser.idx(s),false);
    const auto recorded=dispatch(x,d,Radio::D,"Base",v,-2000000);
    assert(recorded==v);
    d.w.b.endpoints["D:7"].push_back({"D"});
    std::string confirmation;
    d.w.app.callbacks["D:7"]=[&](auto from,auto,auto,auto got){
        assert(from=="Base");
        if(!loseReply)confirmation=got;
    };
    now=-1.875;
    d.w.b.incomingMsgs.push_back({"Base","D",recorded});
    d.w.b.DispatchMessages();
    assert(d.w.b.incomingMsgs.empty());
    d.w.app.callbacks.erase("D:7");
    assert(loseReply?confirmation.empty():confirmation==recorded);
    return confirmation;
}
int main(){
    Amendment a;
    int exact=0,noframe=0,one=0,rawMiss=0,early=0,protectedOld=0,controls=0;
    // Check the common interpretation for every actual fine-input and
    // admitted companion query, including all 127 members of the large fiber.
    for(unsigned s=0;s<=W;++s){
       const auto p=a.coarser.idx(s),k=a.indexInFiber(s,p);
       for(unsigned u=0;u<=W;++u)if(card9(u)<=4){
         assert(a.answer(p,k,u)==bool(s&~u));++exact;
       }
    }
    for(unsigned s=0;s<=W;++s)for(bool useHistory:{false,true}){
        Driver d; EffectCut x(d);
        // Context pairs one previously agreed plan scope with a later cap
        // change. Plan identity is fixed by the reservation in this model.
        const auto confirmed=qualifiedPrevious(a,d,x,s);
        const unsigned oldIndex=unpack(confirmed);
        const auto cached=d.presented["Base"].front().second;
        assert(cached==confirmed);
        assert(dispatch(x,d,Radio::F,"Base","prior",0)=="prior");
        const unsigned u=s&15;
        bool admit=false;
        if(!useHistory){
            const auto payload=packed(a.finer.idx(s),true);
            assert(dispatch(x,d,Radio::D,"Base",payload,500000).empty());
            ++rawMiss;
        }else{
            assert(a.coarser.idx(s)==oldIndex);
            const auto k=a.indexInFiber(s,oldIndex);
            if(a.fiber.at(oldIndex).size()==1){
                assert(k==0);++noframe;
                admit=a.answer(unpack(cached),0,u);
            }else{
                auto rx=dispatch(x,d,Radio::D,"Base",packed(k,false),500000);
                assert(rx==packed(k,false));++one;
                admit=a.answer(unpack(cached),unpack(rx),u);
            }
            assert(admit==bool(s&~u));
        }
        assert(service(d,x,s,u,admit));++protectedOld;
        early+=admit;
    }
    {
        // Two precaution controls: the cached old support class may no
        // longer be the parent of the current scope, or timeout may leave
        // the actual old receipt unconfirmed at the source.
        Driver d;EffectCut x(d);
        const auto seen=qualifiedPrevious(a,d,x,0);
        assert(unpack(seen)!=a.coarser.idx(31));
        assert(service(d,x,31,15,false));
        ++controls;
    }
    {
        Driver d;EffectCut x(d);
        assert(qualifiedPrevious(a,d,x,W,true).empty());
        assert(service(d,x,W,15,false));
        ++controls;
    }
    assert(exact==131072&&noframe==130&&one==382&&rawMiss==512&&early==496&&protectedOld==1024&&controls==2);
    std::cout<<"fine-query comparisons "<<exact<<" max split classes 127 same-class no-send "<<noframe
             <<" valid one-byte supplements "<<one<<" full refresh blocked "<<rawMiss
             <<" old audits "<<protectedOld<<" earlier additional reports "<<early
             <<" fallback controls "<<controls<<"\n";
}
