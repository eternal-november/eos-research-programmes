using namespace vda5050_core;
using namespace vda5050_core::client::adapter;

types::Order route(uint32_t ver,std::string id,std::string trajectory,bool release=true) {
  return {"first",ver,
    {{"A",0,true,"",{}},{"X",2,release,"",{}}},
    {{id,1,release,"A","X","",trajectory}},""};
}
std::pair<NarrowState,std::optional<EdgeRequest>> run(types::Order const& o) {
  Adapter::Implementation impl;
  impl.sm.set_order(o);
  ActiveOrder active;
  active.order=o;
  active.last_completed_node_sequence_id=0;
  for(size_t i=0;i<o.nodes.size();++i)
    active.node_lookup.emplace(o.nodes[i].sequence_id,i);
  for(size_t i=0;i<o.edges.size();++i)
    active.edge_lookup.emplace(o.edges[i].sequence_id,i);
  impl.active_order.order=std::move(active);
  std::optional<EdgeRequest> selected;
  impl.navigation_callback=[&](auto node,auto edge,auto) {
    assert(node.id=="X" && edge && !selected);
    selected=std::move(edge);
  };
  impl.process_navigation();
  return {impl.sm.state_,selected};
}
int main() {
  auto current=route(0,"HORIZON","unsent",false);
  auto left=route(1,"LEFT","west");
  auto right=route(1,"RIGHT","east");
  assert(validation::is_valid_graph(current) &&
    validation::is_valid_update(current,left) &&
    validation::is_valid_update(current,right));
  auto [left_state,left_selected]=run(left);
  auto [right_state,right_selected]=run(right);
  assert(left_state==right_state && left_state.edge_states.empty());
  assert(left_state.order_update_id==1 && left_state.node_states.size()==1 &&
    left_state.node_states.front().node_id=="X" && left_state.node_states.front().released);
  assert(left_selected && right_selected && left_selected->id=="LEFT" &&
    right_selected->id=="RIGHT" && left_selected->trajectory=="west" &&
    right_selected->trajectory=="east");
  auto left_initial=left, right_initial=right;
  left_initial.order_update_id=right_initial.order_update_id=0;
  auto init_left=run(left_initial).first,init_right=run(right_initial).first;
  assert(init_left.edge_states.size()==1 && init_right.edge_states.size()==1 &&
    init_left!=init_right);
  auto horizon=route(1,"LEFT","west",false);
  assert(validation::is_valid_update(current,horizon));
  auto [h_state,h_selected]=run(horizon);
  assert(h_state.edge_states.empty() && !h_selected &&
    !h_state.node_states.front().released && h_state!=left_state);
  std::cout << "update 1: identical projected state, callbacks LEFT/west and RIGHT/east\n";
  std::cout << "initial orders: edge reports differ; unreleased update: no callback\n";
}
