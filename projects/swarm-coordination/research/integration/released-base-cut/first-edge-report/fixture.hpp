#include <algorithm>
#include <cassert>
#include <cstdint>
#include <exception>
#include <functional>
#include <iostream>
#include <memory>
#include <mutex>
#include <optional>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

namespace fmt {
template<class... Ts> std::string format(std::string s, Ts...) {return s;}
}
namespace vda5050_core::types {
struct Position { std::string map_id; bool operator==(Position const&) const=default; };
struct Node {
  std::string node_id;
  uint32_t sequence_id;
  bool released;
  std::string node_description;
  std::optional<Position> node_position;
  bool operator==(Node const&) const=default;
};
struct Edge {
  std::string edge_id;
  uint32_t sequence_id;
  bool released;
  std::string start_node_id, end_node_id, edge_description;
  // Labels stand in for otherwise valid, distinct trajectory metadata.
  std::optional<std::string> trajectory;
};
struct Order {
  std::string order_id;
  uint32_t order_update_id;
  std::vector<Node> nodes;
  std::vector<Edge> edges;
  std::string zone_set_id;
};
struct NodeState {
  std::string node_id;
  uint32_t sequence_id;
  bool released;
  std::string node_description;
  std::optional<Position> node_position;
  bool operator==(NodeState const&) const=default;
};
struct EdgeState {
  std::string edge_id;
  uint32_t sequence_id;
  bool released;
  std::string edge_description;
  std::optional<std::string> trajectory;
  bool operator==(EdgeState const&) const=default;
};
struct ErrorReference {std::string key,value;};
enum class ErrorLevel {FATAL};
struct Error {std::string error_type,error_description;};
}
namespace vda5050_core::errors {
constexpr const char *RefOrderId="oid", *RefOrderUpdateId="uid",
  *RefNodeId="nid", *RefSequenceId="sid", *RefEdgeId="eid",
  *GraphValidationError="graph", *OrderUpdateError="update",
  *NavigationFailedError="navigation";
std::string create_error(std::string, std::string desc,
  std::vector<types::ErrorReference>, types::ErrorLevel) {return desc;}
struct ValidationResult {
  std::vector<std::string> details;
  void add_error(std::string s) {details.push_back(s);}
  explicit operator bool() const {return details.empty();}
};
}
#define VDA5050_INFO(...) do {} while (false)
#define VDA5050_ERROR(...) do {} while (false)
namespace vda5050_core::client::adapter {
struct Transformation {};
struct NarrowState {
  std::string order_id;
  uint32_t order_update_id=0;
  std::string zone_set_id;
  std::vector<types::NodeState> node_states;
  std::vector<types::EdgeState> edge_states;
  bool operator==(NarrowState const&) const=default;
};
struct StateManager {
  std::mutex mutex_;
  NarrowState state_;
  void set_order(types::Order const&);
  std::optional<Transformation> transformation(std::string const&) {return {};}
  void edge_traversed(types::Edge const&) {}
  void node_reached(types::Node const&) {}
  void add_error(types::Error const&) {}
};
struct NodeRequest {
  std::string id;
  static NodeRequest from_node(types::Node const& n,std::optional<Transformation>) {
    return {n.node_id};
  }
};
struct EdgeRequest {
  std::string id;
  std::optional<std::string> trajectory;
  static EdgeRequest from_edge(types::Edge const& e) {
    return {e.edge_id,e.trajectory};
  }
};
struct OrderExecution {
  static std::shared_ptr<OrderExecution> make(
    std::string const&,uint32_t,std::function<void()>,
    std::function<void(std::string const&)>) {
    return std::make_shared<OrderExecution>();
  }
};
struct ActiveOrder {
  types::Order order;
  std::optional<uint32_t> last_completed_node_sequence_id;
  bool executing=false;
  std::unordered_map<uint32_t,size_t> node_lookup,edge_lookup;
};
struct TestLock {
  std::optional<ActiveOrder> order;
  TestLock* lock() {return this;}  // Harness is serial.
};
struct Adapter {
  struct Implementation {
    TestLock active_order;
    StateManager sm;
    StateManager* state_manager=&sm;
    std::function<void(NodeRequest,std::optional<EdgeRequest>,
      std::shared_ptr<OrderExecution>)> navigation_callback;
    void request_state_publish() {}
    void process_navigation();
  };
};
}
