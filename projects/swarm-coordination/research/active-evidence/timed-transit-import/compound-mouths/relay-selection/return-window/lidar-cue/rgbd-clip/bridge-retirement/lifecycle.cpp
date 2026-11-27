#include <functional>
#include <memory>
#include <set>
#include <tuple>
#define main earlier_rgbd_replay
#include "rgbd_probe.cpp"
#undef main

#define IGNITION_TRANSPORT_VERSION_NAMESPACE fixture_transport9
#include "storage.inc"
using ignition::transport::TopicStorage;
struct MessagePublisher {
 std::string topic,proc,node,msg,ctrl,addr;
 const std::string& Topic()const{return topic;}
 const std::string& PUuid()const{return proc;}
 const std::string& NUuid()const{return node;}
 const std::string& MsgTypeName()const{return msg;}
 const std::string& Ctrl()const{return ctrl;}
 const std::string& Addr()const{return addr;}
 void SetPUuid(const std::string& x){proc=x;}
};
using MsgAddresses_M=std::map<std::string,std::vector<MessagePublisher>>;
struct Local {
 TopicStorage<MessagePublisher> values;
 bool HasSubscriber(const std::string& t,const std::string& m)const{return values.HasTopic(t,m);}
};
struct NodeShared {
 std::recursive_mutex mutex;
 bool verbose=false;
 std::string pUuid="sensor";
 TopicStorage<MessagePublisher> remoteSubscribers,connections;
 Local localSubscribers;
 void OnNewRegistration(const MessagePublisher&);
 void OnEndRegistration(const MessagePublisher&);
 void OnNewDisconnection(const MessagePublisher&);
};
struct Node {
 struct Publisher {
  struct Data {NodeShared* shared; MessagePublisher publisher;};
  Data* dataPtr;
  bool valid=true;
  bool Valid()const{return valid;}
  bool HasConnections()const;
 };
};
#include "transport.inc"

namespace ignition::msgs { struct Image {}; }
namespace sensor_msgs { struct Image {}; }
namespace ros_ign_bridge {
void convert_ign_to_ros(const ignition::msgs::Image&, sensor_msgs::Image&){}
}
namespace image_transport {
struct Publisher {
 void publish(const sensor_msgs::Image&){}
};
struct ImageTransport {
 std::vector<std::string> advertised;
 Publisher advertise(const std::string& t,int q) {assert(q==1);advertised.push_back(t);return {};}
};
}
namespace ignition::transport {
struct Node {
 std::vector<std::string> subscriptions;
 template<typename C,typename M> void Subscribe(const std::string& t,M,C*){subscriptions.push_back(t);}
};
}
#include "bridge.inc"

using Key=std::tuple<std::string,std::string,std::string,std::string>;
static Key key(const MessagePublisher& e){return {e.topic,e.msg,e.proc,e.node};}
int main(){
 const auto ros=std::make_shared<image_transport::ImageTransport>();
 const auto ign=std::make_shared<ignition::transport::Node>();
 auto init=Handler(depthTopic,ros,ign);
 assert(ros->advertised==ign->subscriptions && ign->subscriptions==std::vector<std::string>{depthTopic});
 const std::string image="ignition.msgs.Image";
 auto make=[&](const std::string& p,const std::string& n,const std::string& t,
               const std::string& m,const std::string& c="sensor"){
   return MessagePublisher{t,p,n,m,c,"fixture:"+p+":"+n};
 };
 auto bridge=make("bridge-old","handler",ign->subscriptions[0],image);
 auto next=make("bridge-new","handler",depthTopic,image);
 auto other=make("other","test",depthTopic,image);
 auto wrongTopic=make("bridge-old","other-topic","/fixture/camera_front/image",image);
 auto wrongType=make("bridge-old","wrong-type",depthTopic,"ignition.msgs.LaserScan");
 auto generic=make("bridge-old","generic",depthTopic,kGenericMessageType);
 auto foreign=make("foreign","handler",depthTopic,image,"elsewhere");
 unsigned turns=0,fields=0; bool witness[3][2]={};
 for(unsigned end=0;end<5;++end)
 for(unsigned extra=0;extra<5;++extra)
 for(unsigned restart=0;restart<3;++restart)
 for(unsigned initial=0;initial<2;++initial)
 for(unsigned local=0;local<2;++local){
   NodeShared native;
   Node::Publisher::Data data{&native,make("sensor","camera",depthTopic,image)};
   Node::Publisher pub{&data};
   RgbdCameraSensorPrivate d;
   d.depthNearClip=depthNear;d.depthFarClip=depthFar;d.pointPub.yes=true;
   Sensor s{&d};
   std::set<Key> held; // Independent restricted extensional oracle: fixed one address per process/node.
   auto add=[&](const MessagePublisher& e){
     native.OnNewRegistration(e);
     if(e.ctrl=="sensor")held.insert(key(e));
   };
   auto remove=[&](const MessagePublisher& e){
     native.OnEndRegistration(e);
     if(e.ctrl=="sensor")held.erase(key(e));
   };
   auto snapshot=[&](){
     const bool ref=local || std::any_of(held.begin(),held.end(),[&](const Key& k){
       return std::get<0>(k)==depthTopic && (std::get<1>(k)==image || std::get<1>(k)==kGenericMessageType);
     });
     assert(pub.HasConnections()==ref);
     d.depthPub.yes=pub.HasConnections();
     const float frame[]={5,10,37};
     const float points[]={5,1,2,0,10,1,2,0,37,1,2,0};
     d.OnNewDepthFrame(frame,3,1,1,"");
     d.OnNewRgbPointCloud(points,3,1,4,"");
     s.trim(3);s.mask(3);
     msgs::PointCloudPacked out{3};
     PointCloudUtil util;util.FillMsg(out,d.pointCloudBuffer,false,nullptr);
     for(int row=0;row<3;++row)
      for(int j=0;j<3;++j){
        auto val=(row==2 && ref)?float(math::INF_D):points[4*row+j];
        assert(val==packed(out,row,j));
        ++fields;
      }
     ++turns;
     return std::isfinite(packed(out,2,0));
   };
   if(local)native.localSubscribers.values.AddPublisher(make("sensor","local",depthTopic,image));
   assert(snapshot()==!local); // Process may be started, without publisher-side registration.
   if(initial)add(bridge);
   if(extra==1)add(other);
   if(extra==2)add(wrongTopic);
   if(extra==3)add(wrongType);
   if(extra==4)add(generic);
   add(foreign); // Must not change the named publisher.
   snapshot();
   if(end==0)remove(bridge); // named end directed to this publisher
   if(end==1)expire(native,bridge.proc); // actual timeout event shape
   if(end==2)bye(native,bridge.proc); // actual process BYE event shape
   if(end==3){native.OnNewDisconnection(bridge);held.erase(key(bridge));}
   if(end==4){auto e=bridge;e.ctrl="elsewhere";remove(e);}
   bool after=snapshot();
   if(initial && !local && extra==0 && end<3)witness[end][after]=true;
   if(restart)add(next);
   if(restart==2)remove(next);
   snapshot();
 }
 assert(witness[0][1] && !witness[0][0]);
 assert(witness[1][0] && !witness[1][1]);
 assert(witness[2][0] && !witness[2][1]);
 assert(turns==1200 && fields==10800);
 std::cout<<"300 lifecycle histories; 1200 fresh point frames; 10800 packed XYZ comparisons\n"
          <<"37 m sample after named end: finite; after process timeout or BYE alone: clipped\n";
}
