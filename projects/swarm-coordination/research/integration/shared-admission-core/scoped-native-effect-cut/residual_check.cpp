#include "cut_contract.h"
#include <array>
#include <cassert>
#include <iostream>
#include <set>
using namespace cut;
static Profile state(unsigned key) {
    return {key&16?Act::effect:Act::inspect, bool(key&8),bool(key&4),bool(key&2),bool(key&1)};
}
static Profile restore(Profile a,unsigned mask) {
    const auto b=state(mask);
    return {a.act,a.scope||b.scope,a.value||b.value,a.room||b.room,a.service||b.service};
}
int main(){
    int tested=0;
    std::set<std::array<int,5>> profiles;
    for(unsigned i=0;i<32;++i){
        auto p=state(i);
        std::array<int,5> sig{int(p.act),check(restore(p,7)),check(restore(p,11)),
                             check(restore(p,13)),check(restore(p,14))};
        profiles.insert(sig);
        for(unsigned j=0;j<32;++j){
            auto q=state(j);
            bool reflected=p.act==q.act;
            for(unsigned mask=0;mask<16;++mask){
                bool eq=check(restore(p,mask))==check(restore(q,mask));
                reflected &= eq;
                ++tested;
            }
            assert(reflected==relevantComparison(p,q));
        }
    }
    assert(tested==16384&&profiles.size()==20);
    std::cout<<"profile classes "<<profiles.size()<<" restored comparisons "<<tested<<"\n";
}
