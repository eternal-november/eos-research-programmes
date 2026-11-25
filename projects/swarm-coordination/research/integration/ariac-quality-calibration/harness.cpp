// Extracted NIST function bodies compiled against explicitly mocked dependencies.
#include <array>
#include <cassert>
#include <iostream>
#include <map>
#include <memory>
#include <string>
#include <vector>
#define RCLCPP_WARN(...) do {} while (0)
#define RCLCPP_INFO_STREAM(...) do {} while (0)
namespace ariac_msgs {
namespace msg {
struct QualityIssue {
  bool all_passed=false,missing_part=false,flipped_part=false,faulty_part=false;
  bool incorrect_part_type=false,incorrect_part_color=false;
};
struct CompetitionState { static constexpr int ENDED=1; };
struct Order { static constexpr int KITTING=1; };
}
namespace srv {
struct PerformQualityCheck {
  struct Request { using SharedPtr=std::shared_ptr<Request>; std::string order_id; };
  struct Response {
    using SharedPtr=std::shared_ptr<Response>;
    bool valid_id=false,all_passed=false,incorrect_tray=false;
    msg::QualityIssue quadrant1,quadrant2,quadrant3,quadrant4;
  };
};
}
}
namespace ariac_common {
struct Part { int GetType() const { return 1;} int GetColor() const {return 1;} };
struct Product { int GetQuadrant() const {return 1;} Part GetPart() const {return {};} };
struct KittingTask {
  int GetAgvNumber() const {return 1;}
  int GetTrayId() const {return 2;}
  const std::vector<Product> products={{}};
  const std::vector<Product>& GetProducts() const {return products;}
};
struct TrayPart {
  std::string name;
  std::string GetModelName() const {return name;}
  int GetQuadrant() const {return 1;}
  bool isCorrectType(int x) const {return x==1;}
  bool isCorrectColor(int x) const {return x==1;}
  bool isFlipped() const {return false;}
  bool isFaulty() const {return name.find("faulty")!=std::string::npos;}
};
struct KittingShipment {
  int tray=2;
  std::vector<TrayPart> parts;
  int GetTrayId() const {return tray;}
  const std::vector<TrayPart>& GetTrayParts() const {return parts;}
};
struct FaultyPartChallenge {
  bool checked=false;
  bool IsQuadrantFaulty(int i) const {return i==1;}
  bool WasQuadrantChecked(int i) const {assert(i==1);return checked;}
  void SetQuadrantChecked(int i) {assert(i==1);checked=true;}
  std::string GetOrderId() const {return "kit";}
};
}
struct Order {
  std::string GetId() const {return "kit";}
  int GetType() const {return ariac_msgs::msg::Order::KITTING;}
  auto GetKittingTask() const {return std::make_shared<ariac_common::KittingTask>();}
};
struct Model { std::string name="part_1"; void SetName(std::string s){name=s;} };
struct World {
  Model model;
  Model* ModelByName(std::string n){assert(n==model.name);return &model;}
};
class TaskManagerPluginPrivate {
public:
  using S=ariac_msgs::srv::PerformQualityCheck;
  int current_state_=0;
  std::vector<std::shared_ptr<Order>> all_orders_={std::make_shared<Order>()};
  std::vector<std::shared_ptr<ariac_common::FaultyPartChallenge>> faulty_part_challenges_;
  std::map<int,ariac_common::KittingShipment> agv_tray_images_;
  std::unique_ptr<World> world_=std::make_unique<World>();
  ariac_common::KittingShipment ParseAGVTraySensorImage(ariac_common::KittingShipment s){return s;}
  std::array<bool,4> HandleFaultyParts(std::shared_ptr<ariac_common::FaultyPartChallenge>,ariac_common::KittingTask,ariac_common::KittingShipment);
  ariac_msgs::msg::QualityIssue CheckQuadrantQuality(int,ariac_common::KittingTask,ariac_common::KittingShipment,std::string);
  void PerformQualityCheck(S::Request::SharedPtr,S::Response::SharedPtr);
  void sample(int tray=2){agv_tray_images_[1]={tray,{{world_->model.name}}};}
  auto check(){
    auto req=std::make_shared<S::Request>();
    req->order_id="kit";
    auto res=std::make_shared<S::Response>();
    PerformQualityCheck(req,res);
    return *res;
  }
};
#include "upstream_extract.inc"
void report(const std::string& id, const TaskManagerPluginPrivate::S::Response& r){
  std::cout<<id<<" "<<r.valid_id<<" "<<r.all_passed<<" "<<r.incorrect_tray
   <<" "<<r.quadrant1.faulty_part<<"\n";
}
int main() {
  TaskManagerPluginPrivate p;
  p.faulty_part_challenges_.push_back(std::make_shared<ariac_common::FaultyPartChallenge>());
  p.sample();
  auto first=p.check();
  assert(!first.all_passed && first.quadrant1.faulty_part);
  assert(p.world_->model.name=="part_1_faulty");
  report("first_marks_part",first);
  auto stale=p.check();
  assert(stale.all_passed && !stale.quadrant1.faulty_part);
  assert(p.world_->model.name=="part_1_faulty");
  report("same_cached_image",stale);
  p.sample();
  auto fresh=p.check();
  assert(!fresh.all_passed && fresh.quadrant1.faulty_part);
  report("next_image_unchanged_part",fresh);
  p.world_->model.name="part_2";
  p.sample();
  auto changed=p.check();
  assert(changed.all_passed && !changed.quadrant1.faulty_part);
  report("next_image_replacement",changed);
  p.sample(3);
  auto wrong_tray=p.check();
  assert(wrong_tray.all_passed && wrong_tray.incorrect_tray);
  report("wrong_tray",wrong_tray);
}
