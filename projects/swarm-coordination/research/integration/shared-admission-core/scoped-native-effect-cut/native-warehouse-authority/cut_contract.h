#pragma once

namespace cut {
enum class Act { inspect, effect };
enum Result { past, absent, wrong_scope, no_witness, busy, missing_service, enable };
struct Profile {
    Act act;
    bool scope;        // permission for this act, on its own subject and observer
    bool value;        // exact historical result, or qualified input for an effect
    bool room;         // same-history interpreted resource room
    bool service;      // live readiness of the effect-owning mechanism
};
constexpr Result check(Profile p) {
    if(!p.scope) return wrong_scope;
    if(p.act==Act::inspect) return p.value?past:absent;
    if(!p.value) return no_witness;
    if(!p.room) return busy;
    if(!p.service) return missing_service;
    return enable;
}
constexpr bool relevantComparison(Profile old, Profile fresh) {
    if(old.act!=fresh.act || old.scope!=fresh.scope || old.value!=fresh.value)return false;
    return old.act==Act::inspect || (old.room==fresh.room && old.service==fresh.service);
}
}
