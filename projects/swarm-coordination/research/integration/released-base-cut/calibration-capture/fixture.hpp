#include <cassert>
#include <cstdint>
#include <functional>
#include <iostream>
#include <map>
#include <memory>
#include <mutex>
#include <optional>
#include <string>
#include <utility>
#include <vector>
#define VDA5050_INFO(...) ((void)0)
#define VDA5050_ERROR(...) ((void)0)

namespace vda5050_core {
namespace types {
struct AGVPosition {
  double x{},y{},theta{}; std::string map_id; bool position_initialized{};
  bool operator==(const AGVPosition&) const=default;
};
struct State { std::optional<AGVPosition> agv_position; };
struct NodePosition {
  double x{},y{}; std::optional<double> theta; std::string map_id;
};
struct Node {
  std::string node_id; uint32_t sequence_id; bool released;
  std::optional<NodePosition> node_position;
  std::optional<std::string> node_description;
};
struct Order {
  std::string order_id; uint32_t order_update_id;
  std::vector<Node> nodes; std::vector<int> edges;
};
struct Error {std::string error_type,error_description;};
}
namespace errors { constexpr auto NavigationFailedError="unused"; }
namespace client::adapter {
class StateManager {
 public:
  void set_position(double,double,double,const std::string&);
  void initialize_position(double,double,double,const std::string&);
  void set_transformation(const Transformation&,const std::string&);
  std::optional<Transformation> transformation(const std::string&) const;
  types::State state() const;
  void add_error(const types::Error&) {assert(false);}
  void edge_traversed(int) {assert(false);}
  void node_reached(const types::Node&) {assert(false);}
 private:
  mutable std::mutex mutex_;
  types::State state_;
  std::map<std::string,Transformation> transformation_;
};
class NodeRequest;
struct EdgeRequest { static EdgeRequest from_edge(int) {assert(false);return {};} };
struct ActiveOrder {
  types::Order order;
  bool executing{};
  std::optional<uint32_t> last_completed_node_sequence_id;
  std::map<uint32_t,size_t> node_lookup,edge_lookup;
};
struct OrderExecution {
 static int make(std::string, uint32_t, auto, auto) {return 1;}
};
class Adapter {
 public:
  struct Implementation {
    struct Active {std::optional<ActiveOrder> order;};
    struct Box {
      Active value;
      Active* lock() {return &value;} // serial execution, not a concurrency test
    } active_order;
    StateManager* state_manager{};
    std::function<void(NodeRequest,std::optional<EdgeRequest>,int)> navigation_callback;
    void request_state_publish() {assert(false);}
    void process_navigation();
  };
};
}
}
