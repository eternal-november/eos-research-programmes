#include <cassert>
#include <iostream>
#include <map>
#include <memory>
#include <string>
#include <utility>
#include <vector>
#define RCLCPP_WARN(...) ((void)0)
namespace KDL {struct Frame{int x=0;}; Frame operator*(Frame a,Frame b){return {a.x+b.x};}}
namespace tf2 {void fromMsg(KDL::Frame f,KDL::Frame& a){a=f;} KDL::Frame toMsg(KDL::Frame p){return p;}}
namespace geometry_msgs::msg {using Pose=KDL::Frame;}
namespace gazebo_ros {template<class T>T Convert(KDL::Frame f){return f;}}
namespace gazebo::msgs {
 KDL::Frame ConvertIgn(KDL::Frame f){return f;}
 struct Model{
  std::string n;int x;
  auto name()const{return n;}
  KDL::Frame pose()const{return {x};}
 };
 struct LogicalCameraImage{
  std::vector<Model> models;
  KDL::Frame pose()const{return {0};}
  auto model_size()const{return int(models.size());}
  const auto& model(int i)const{return models.at(i);}
 };
}
using ConstLogicalCameraImagePtr=std::shared_ptr<const gazebo::msgs::LogicalCameraImage>;
namespace ariac_msgs {
namespace msg {
struct AGVStatus{enum {ELSEWHERE, ASSEMBLY_FRONT, ASSEMBLY_BACK};using SharedPtr=std::shared_ptr<AGVStatus>;unsigned location{};};
struct CompetitionState{enum {STARTED,ENDED};};
struct Order{enum {KITTING,ASSEMBLY,COMBINED};};
struct AssemblyTask{enum {AS1,AS2,AS3,AS4};int GetStation()const{return AS1;}};
struct PartPose{struct Part{int type{},color{};}part;KDL::Frame pose;};
}
namespace srv {
struct GetPreAssemblyPoses {
 struct Request{using SharedPtr=std::shared_ptr<Request>;std::string order_id;};
 struct Response{using SharedPtr=std::shared_ptr<Response>;bool valid_id=false,agv_at_station=false;
     std::vector<msg::PartPose> parts;};
};
}
}
namespace ariac_common {
struct Order {
 bool used=false;
 std::string id;
 explicit Order(std::string i):id(i){}
 auto GetId()const{return id;}
 auto GetType()const{return ariac_msgs::msg::Order::ASSEMBLY;}
 bool WasPreAssemblyServiceCalled()const{return used;}
 void SetPreAssemblyServiceCalled(){used=true;}
 auto GetAssemblyTask()const{return std::make_shared<ariac_msgs::msg::AssemblyTask>();}
 auto GetCombinedTask()const{return GetAssemblyTask();}
};
}
using Service=ariac_msgs::srv::GetPreAssemblyPoses;
using Status=ariac_msgs::msg::AGVStatus;
struct TaskManagerPluginPrivate{
 int current_state_=ariac_msgs::msg::CompetitionState::STARTED;
 std::vector<std::shared_ptr<ariac_common::Order>> all_orders_;
 unsigned agv1_location_=0,agv2_location_=0,agv3_location_=0,agv4_location_=0;
 std::map<int,gazebo::msgs::LogicalCameraImage> agv_tray_images_;
 std::map<std::string,int> part_types_{{"pump",1}},part_colors_{{"red",2}};
 void GetPreAssemblyPoses(Service::Request::SharedPtr,Service::Response::SharedPtr);
 void AGV1TraySensorCallback(ConstLogicalCameraImagePtr&);
 void camera(bool item,int pose){
   auto c=std::make_shared<gazebo::msgs::LogicalCameraImage>();
   if(item)c->models.push_back({"red_pump",pose});
   ConstLogicalCameraImagePtr msg=c;
   AGV1TraySensorCallback(msg);
 }
 auto request(std::string k){
   auto q=std::make_shared<Service::Request>();q->order_id=k;
   auto r=std::make_shared<Service::Response>();
   GetPreAssemblyPoses(q,r);
   return r;
 }
};
struct TaskManagerPlugin{
 TaskManagerPluginPrivate state,*impl_=&state;
 void OnAGV1StatusCallback(const Status::SharedPtr);
 void arrive(){auto s=std::make_shared<Status>();s->location=Status::ASSEMBLY_FRONT;OnAGV1StatusCallback(s);}
};
#include "selected.inc"
int main(){
 int n=0;
 for(bool beforeDock:{false,true})for(bool itemInOld:{false,true})
 for(bool doProbe:{false,true})for(int c=1;c<=20;++c)for(int need=1;need<=20;++need){
   TaskManagerPlugin p;
   auto order=std::make_shared<ariac_common::Order>("A");
   auto other=std::make_shared<ariac_common::Order>("B");
   p.state.all_orders_={order,other};
   p.state.camera(itemInOld,c);
   if(beforeDock)p.arrive();
   if(doProbe){
     auto q=p.state.request("A");
     assert(q->valid_id);
     assert(q->agv_at_station==beforeDock);
     assert(q->parts.size()==unsigned(beforeDock&&itemInOld));
     assert(order->used==beforeDock);
     if(beforeDock&&itemInOld)assert(q->parts.front().pose.x==c);
   }
   if(!beforeDock)p.arrive();
   p.state.camera(true,100+need);
   auto r=p.state.request("A");
   if(beforeDock&&doProbe){
     assert(!r->valid_id&&r->parts.empty());
   }else{
     assert(r->valid_id&&r->agv_at_station&&r->parts.size()==1);
     assert(r->parts.front().pose.x==100+need);
   }
   // The admission latch is per order, not suppression of camera capture.
   auto fresh=p.state.request("B");
   assert(fresh->valid_id&&fresh->parts.at(0).pose.x==100+need);
   ++n;
 }
 std::cout<<n<<" selected arrival, cached-frame, and per-order-read histories\n";
}
