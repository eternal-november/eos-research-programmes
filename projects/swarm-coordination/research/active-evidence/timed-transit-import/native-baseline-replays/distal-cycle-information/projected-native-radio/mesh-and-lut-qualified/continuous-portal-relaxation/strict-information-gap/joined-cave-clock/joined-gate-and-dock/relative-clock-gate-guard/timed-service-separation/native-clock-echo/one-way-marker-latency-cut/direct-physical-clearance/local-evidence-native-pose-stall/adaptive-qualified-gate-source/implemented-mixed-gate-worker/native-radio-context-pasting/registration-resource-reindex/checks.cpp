#include <cassert>
#define main embedded_native_tests
#include "staged_replay.inc"
#undef main

struct Survivor {
    // The independently qualified physical resource is an explicit
    // input to the compatibility decision, not inferred from address.
    unsigned prior_tx;
    long long at;
    bool same_physical;
    unsigned live(long long now)const{
        return same_physical&&now-at<=1000000?prior_tx:0;
    }
};
static bool send(World& w,std::string a,std::string b,unsigned n,double at){
    std::string seen;
    w.app.callbacks[b+":7"]=[&](auto src,auto,auto,auto bytes){assert(src==a);seen=bytes;};
    w.send(a,b,n,at);
    w.app.callbacks.erase(b+":7");
    assert(seen.empty()||seen.size()==n);
    return !seen.empty();
}
int main(){
 int violations=0,allowed=0,rxblocked=0,stable=0;
 for(bool same:{false,true})
 for(bool rereregister:{false,true})
 for(bool rxBusy:{false,true})
 for(bool compatibility:{false,true}){
    if(!rereregister&&!same)continue; // no hidden claim a stable node is physically replaced
    World w(6);
    w.path_available=false;
    assert(!send(w,"P","Base",4,0));
    assert(w.state("P").bytes_sent_this_epoch==4);
    Survivor old{4,0,same};
    w.path_available=true;
    if(rxBusy)assert(send(w,"Q","Base",4,.25));
    auto p=w.b.team->at("P");
    w.b.default_radio_configuration=p->radio;
    if(rereregister)assert(w.b.Unregister("P"));
    assert(w.b.Register("P"));
    if(rereregister){
       assert(w.b.team->at("P")!=p && w.state("P").bytes_sent_this_epoch==0);
    }else{
       assert(w.b.team->at("P")==p && w.state("P").bytes_sent_this_epoch==4);
       ++stable;
    }
    const bool intended=old.live(500000)+3<=6;
    bool result=false;
    if(!compatibility||intended)result=send(w,"P","Base",3,.5);
    if(result){
        assert(rereregister&&!rxBusy);
        if(!intended){
           assert(!compatibility);
           ++violations;
        }else ++allowed;
    }
    if(rereregister&&rxBusy&&(!compatibility||intended)){
        // Distinct receiving state survives the sender rebind. Its
        // rejection can still charge the new sending radio.
        assert(!result && w.state("P").bytes_sent_this_epoch==3);
        ++rxblocked;
    }
    if(compatibility&&same){
       assert(!result&&old.live(1500000)==0);
       assert(send(w,"P","Base",3,1.5));
    }
 }
 assert(violations==1&&allowed==2&&rxblocked==3&&stable==4);
 std::cout<<"recorded same-resource budget violations ignored by address-only check "<<violations
          <<" qualified fresh-edge deliveries "<<allowed
          <<" unchanged receive credit rejections "<<rxblocked
          <<" duplicate stable registrations "<<stable<<"\n";
}
