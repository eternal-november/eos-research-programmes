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
#include <algorithm>
#define VDA5050_INFO(...) ((void)0)
#define VDA5050_ERROR(...) ((void)0)

namespace vda5050_core {
namespace types {
struct AGVPosition {
  double x{},y{},theta{}; std::string map_id; bool position_initialized{};
  bool operator==(const AGVPosition&) const=default;
};
struct State { std::optional<AGVPosition> agv_position; };
struct Action {bool operator==(const Action&) const=default;};
} }
VDA_NATIVE_NODE_TYPES
namespace vda5050_core {
namespace types {
struct Edge {
 std::string edge_id;
 uint32_t sequence_id;
 bool released;
 std::string start_node_id,end_node_id;
};
struct Order {
 std::string order_id;uint32_t order_update_id;
 std::vector<Node> nodes;
 std::vector<Edge> edges;
};
enum class ErrorLevel {FATAL};
struct ErrorReference{std::string key,value;};
struct Error {std::string error_type,error_description;};
}
namespace errors {
constexpr auto NavigationFailedError="navigation";
constexpr const char *RefOrderId="oid",*RefOrderUpdateId="uid",*RefNodeId="nid",
  *RefSequenceId="sid",*RefEdgeId="eid",*GraphValidationError="graph",*OrderUpdateError="update";
types::Error create_error(std::string a,std::string b,std::vector<types::ErrorReference>,types::ErrorLevel){
 return {a,b};
}
struct ValidationResult {
 std::vector<types::Error> details;
 void add_error(types::Error s) {details.push_back(std::move(s));}
 explicit operator bool() const {return details.empty();}
 const auto& fatal_errors() const {return details;}
 std::vector<types::Error> warnings() const {return {};}
};
}
namespace client::adapter {
class StateManager {
 public:
  void set_position(double,double,double,const std::string&);
  void initialize_position(double,double,double,const std::string&);
  void set_transformation(const Transformation&,const std::string&);
  std::optional<Transformation> transformation(const std::string&) const;
  types::State state() const;
  std::vector<types::Error> faults;
  std::optional<types::Order> greatest_accepted;
  void add_error(const types::Error& e){faults.push_back(e);}
  void set_order(types::Order o){greatest_accepted=std::move(o);}
  void edge_traversed(const types::Edge&) {}
  void node_reached(const types::Node&) {}
 private:
  mutable std::mutex mutex_;
  types::State state_;
  std::map<std::string,Transformation> transformation_;
};
class NodeRequest;
struct EdgeRequest { static EdgeRequest from_edge(const types::Edge&) {return {};} };
struct ActiveOrder {
 types::Order order;
 bool executing{};
 std::optional<uint32_t> last_completed_node_sequence_id;
 std::map<uint32_t,size_t> node_lookup,edge_lookup;
};
inline bool is_order_complete(const ActiveOrder&) {return false;} // only active orders
struct OrderExecution {
 std::function<void()> finished;
 uint32_t version;
 static OrderExecution make(std::string, uint32_t v, auto fn, auto) {return {fn,v};}
};
struct Protocol {
 std::function<void(types::Order,std::optional<types::Error>)> receive;
 template <typename T> void subscribe(auto fn,int) {receive=fn;}
};
class Adapter {
 public:
  struct Implementation {
    struct Active {std::optional<ActiveOrder> order;};
    struct Box {
      Active value;
      Active* lock() {return &value;}
    } active_order;
    StateManager* state_manager{};
    Protocol* protocol_adapter{};
    std::function<void(NodeRequest,std::optional<EdgeRequest>,OrderExecution)> navigation_callback;
    unsigned publishes=0;
    void request_state_publish(){++publishes;}
    void process_navigation();
    void subscribe_orders();
  };
};
}
}
