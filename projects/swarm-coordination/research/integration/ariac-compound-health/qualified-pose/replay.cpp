#include <cassert>
#include <iostream>
#include <map>
#include <memory>
#include <mutex>
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

class PoseStub {public: KDL::Frame WorldPose(){return {20};}};
namespace ignition::math {using Pose3d=KDL::Frame;}
KDL::Frame operator+(KDL::Frame a,KDL::Frame b){return {a.x+b.x};}
#define IGN_PROFILE(...) ((void)0)
#define IGN_PROFILE_BEGIN(...) ((void)0)
#define IGN_PROFILE_END(...) ((void)0)
namespace gazebo::msgs {
void Set(KDL::Frame* p,KDL::Frame q){*p=q;}
}
using gazebo::msgs::LogicalCameraImage;
struct CameraBus {
 bool connected=true;
 std::vector<LogicalCameraImage> frames;
 auto HasConnections()const{return connected;}
 void Publish(const LogicalCameraImage& m){frames.push_back(m);}
};
struct CameraMsg:LogicalCameraImage{
 KDL::Frame transform{20};
 void clear_model(){models.clear();}
 KDL::Frame* mutable_pose(){return &transform;}
};
struct World{int pose=100;int Models()const{return pose;}};
struct Sensor{
 bool active=false;
 bool IsActive()const{return active;}
};
namespace msgs=gazebo::msgs;
struct LogicalCameraSensor:Sensor{
 struct Data{
  std::mutex mutex;
  CameraMsg msg;
  PoseStub link,*parentLink=&link;
  CameraBus bus,*pub=&bus;
  struct{void SetPose(KDL::Frame){}} frustum;
  // The scene/frustum seam: one visible part in the selected fixture.
  void AddVisibleModels(const KDL::Frame&,int p){msg.models.push_back({"red_pump",p});}
 } data,*dataPtr=&data;
 KDL::Frame pose{0};
 World content,*world=&content;
 bool UpdateImpl(const bool);
 bool IsActive()const;
 msgs::LogicalCameraImage Image()const;
};
namespace ariac_msgs::msg {
 struct KitTrayPose {int id;KDL::Frame pose;};
 struct Sensors {using SharedPtr=std::shared_ptr<Sensors>;bool logical_camera=true;};
}
struct ROSClock{int t=0;int now()const{return t;}};
struct ROSNode{ROSClock clk;auto get_clock(){return &clk;}};
struct Basic {
 struct{int stamp;std::string frame_id;}header;
 KDL::Frame sensor_pose;
 std::vector<KDL::Frame> part_poses,tray_poses;
};
struct Advanced{
 struct{int stamp;std::string frame_id;}header;
 KDL::Frame sensor_pose;
 std::vector<ariac_msgs::msg::PartPose> part_poses;
 std::vector<ariac_msgs::msg::KitTrayPose> tray_poses;
};
template<class I>struct ROSOutput{
 std::vector<I> sent;
 void publish(const I& m){sent.push_back(m);}
};
struct AriacLogicalCameraPluginPrivate{
 ariac_msgs::msg::Sensors sensor_health_;
 LogicalCameraSensor holder,*sensor_=&holder;
 std::vector<std::string> parts_to_publish_{"pump"},colors_{"red"};
 std::map<std::string,int> part_types_{{"pump",1}},part_colors_{{"red",2}};
 std::string sensor_type_="basic",frame_name_="tray1";
 ROSNode node,*ros_node_=&node;
 Basic basic,*basic_image_msg_=&basic;
 Advanced adv,*advanced_image_msg_=&adv;
 ROSOutput<Basic> basic_pub,*basic_pub_=&basic_pub;
 ROSOutput<Advanced> advanced_pub,*advanced_pub_=&advanced_pub;
 void OnUpdate();
};
struct AriacLogicalCameraPlugin {
 AriacLogicalCameraPluginPrivate state,*impl_=&state;
 void SensorHealthCallback(const ariac_msgs::msg::Sensors::SharedPtr);
 void flag(bool healthy){auto flag=std::make_shared<ariac_msgs::msg::Sensors>();flag->logical_camera=healthy;SensorHealthCallback(flag);}
};
#include "selected.inc"
int main(){
 int n=0,red=0,f=0;
 for(bool healthy:{false,true})for(bool connected:{false,true})
 for(bool force:{false,true})for(bool active:{false,true})
 for(bool delay:{false,true})for(int old=1;old<=25;++old){
   AriacLogicalCameraPlugin a;
   TaskManagerPlugin b;
   auto order=std::make_shared<ariac_common::Order>("A");
   b.state.all_orders_={order};
   b.arrive();
   b.state.camera(true,old);
   a.flag(healthy);
   a.state.holder.active=active;
   a.state.holder.data.bus.connected=connected;
   a.state.holder.world->pose=100+old;
   a.state.node.clk.t=7;
   auto &cam=a.state.holder;
   bool captured=connected||force||active;
   if(cam.IsActive()||force){
      // Selected caller sequence: raw publication precedes updated signal.
      assert(cam.UpdateImpl(force));
      if(!delay&&!cam.data.bus.frames.empty()){
        ConstLogicalCameraImagePtr m=std::make_shared<LogicalCameraImage>(cam.data.bus.frames.back());
        b.state.AGV1TraySensorCallback(m);
      }
      a.state.OnUpdate();
   }
   assert(cam.data.bus.frames.size()==unsigned(captured));
   assert(a.state.basic_pub.sent.size()==unsigned(healthy&&captured));
   if(!a.state.basic_pub.sent.empty()){
     assert(a.state.basic_pub.sent[0].header.stamp==7);
     assert(a.state.basic_pub.sent[0].part_poses.at(0).x==100+old);
   }
   auto x=b.state.request("A");
   assert(x->valid_id&&x->agv_at_station&&x->parts.size()==1);
   assert(x->parts[0].pose.x==((captured&&!delay)?100+old:old));
   red+=!healthy&&captured&&!delay; f+=healthy&&captured&&delay;
   ++n;
 }
 std::cout<<n<<" selected process-cut cases, "<<red<<" internal fresh caches during no public publish, "
          <<f<<" public fresh captures with a stale internal cache at read\n";
}
