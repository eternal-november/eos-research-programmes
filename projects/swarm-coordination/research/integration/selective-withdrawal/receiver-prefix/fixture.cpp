#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <optional>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

namespace types {
struct NodeState {
 std::string node_id;
 uint32_t sequence_id;
 bool released;
};
struct EdgeState { bool released; };
struct ActionState { std::string action_id; };
struct State {
 std::string order_id="sandbox";
 uint32_t order_update_id=1;
 std::string last_node_id="r";
 uint32_t last_node_sequence_id=0;
 std::vector<NodeState> node_states;
 std::vector<EdgeState> edge_states;
 std::vector<ActionState> action_states;
};
using Node=NodeState;
using Edge=EdgeState;
struct Order {
 std::string order_id="sandbox";
 uint32_t order_update_id;
 std::vector<Node> nodes;
 std::vector<Edge> edges;
};
struct ErrorReference {std::string key,value;};
}
namespace vda5050_core { namespace types = ::types; }
namespace errors {
 const char *ValidationError="",*OrderUpdateError="",*RefNodeId="",*RefSequenceId="";
}
struct Probe { types::State state; types::State get_state() {return state;} };
enum Outcome {ACCEPT,IGNORE,REJECT};
Outcome accepted(){return ACCEPT;}
Outcome ignored(){return IGNORE;}
Outcome rejected(int){return REJECT;}
int make_error(const std::string&,const std::string&,const types::Order&,
               std::vector<types::ErrorReference> = {}) {return 0;}
bool is_busy(const types::State& s){return !s.node_states.empty();}
Outcome validator(Probe* execution,const types::Order& incoming_order) {
#include "release_validate.inc"

void append_node(types::State& state, const types::Node& n){state.node_states.push_back(n);}
void append_edge(types::State& state, const types::Edge& e){state.edge_states.push_back(e);}
#include "release_apply.inc"

enum class StitchDecision {SEND_NOW,IGNORE,REJECT,QUEUE_PENDING};
enum class GuardFailure {NO_STATE_YET,ORDER_ID_MISMATCH,PREV_UPDATE_NOT_CONFIRMED};
struct StitchResult {
 StitchDecision decision=StitchDecision::SEND_NOW;
 GuardFailure first_failed_guard{};
 std::vector<int> errors;
};
struct ActiveOrderSnapshot {
 bool has_active=true,order_complete=false;
 std::string order_id="sandbox",state_order_id="sandbox";
 uint32_t order_update_id=2,state_order_update_id=1,last_node_sequence_id=0;
 std::vector<types::Node> nodes;
};
struct OrderStitcher {
 StitchResult decide(const types::Order&,const ActiveOrderSnapshot&) const;
};
int make_error(const types::Order&,const std::string&,
               std::vector<types::ErrorReference> = {}) {return 0;}
#include "release_master.inc"

void send(Probe& plant,const types::Order& o,Outcome expected){
 auto result=validator(&plant,o);
 assert(result==expected);
 if(result==ACCEPT)apply_order_update(plant.state,o);
}

int main(){
 // Already validated same-order node-only and linear paths. Callbacks and
 // graph validation are intentionally outside these selected native bodies.
 Probe common;
 common.state.node_states={{"r",0,true},{"next",2,false}};
 common.state.edge_states={{false}};
 const types::Order extension{"sandbox",2,{{"r",0,true},{"next",2,true}},{{true}}};
 const types::Order horizon_only{"sandbox",3,{{"r",0,true}},{}};
 const types::Order horizon_after{"sandbox",3,{{"next",2,true}},{}};

 Probe early=common,late=common;
 // Correlation witness in an in-memory fixture, not a stock master policy.
 send(early,extension,ACCEPT);
 send(early,horizon_only,REJECT);
 send(early,horizon_after,ACCEPT);
 assert(early.state.node_states.back().released && early.state.node_states.back().sequence_id==2);
 send(late,horizon_only,ACCEPT);
 send(late,extension,REJECT);
 assert(late.state.node_states.back().released && late.state.node_states.back().sequence_id==0);
 assert(early.state.order_update_id==late.state.order_update_id);
 send(late,horizon_only,IGNORE);

 ActiveOrderSnapshot snapshot; snapshot.nodes={{"r",0,true}};
 const auto m=OrderStitcher{}.decide(horizon_only,snapshot);
 assert(m.decision==StitchDecision::QUEUE_PENDING);
 assert(m.first_failed_guard==GuardFailure::PREV_UPDATE_NOT_CONFIRMED);
 std::cout<<"6 selected client checks: accepted epoch 3 can still denote two different released prefixes\n";
 std::cout<<"1 selected master check: later update queued while previous id unconfirmed\n";
}
