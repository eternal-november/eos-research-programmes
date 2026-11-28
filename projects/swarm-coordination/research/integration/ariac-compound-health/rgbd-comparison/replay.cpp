#include <cassert>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <limits>
#include <memory>
#include <mutex>
#include <string>
#include <vector>

namespace builtin_interfaces::msg {using Time=int;}
namespace gazebo::common {using Time=int;}
namespace gazebo_ros {template<class T>T Convert(int x){return x;}}
namespace sensor_msgs {
 namespace image_encodings{inline const std::string TYPE_32FC1="32FC1";}
 namespace msg {
 struct Image {
   struct Header{int stamp=0;std::string frame_id;}header;
   std::string encoding;
   unsigned width{},height{},step{};
   int is_bigendian{};
   std::vector<unsigned char> data;
 };
 }
}
namespace cv {
 struct Scalar {float x;explicit Scalar(float a):x(a){}};
 struct Mat {
   unsigned rows=0,cols=0;float x=0;
   Mat()=default;
   Mat(unsigned h,unsigned w,int,Scalar s):rows(h),cols(w),x(s.x){}
 };
}
constexpr int CV_32FC1=0;
namespace cv_bridge {
 struct CvImage {
   cv::Mat image;
   auto toImageMsg()const{
     auto p=std::make_shared<sensor_msgs::msg::Image>();
     p->width=image.cols;p->height=image.rows;
     p->step=sizeof(float)*p->width;
     p->data.resize(p->width*p->height*sizeof(float));
     for(unsigned i=0;i<p->width*p->height;++i)
       std::memcpy(p->data.data()+sizeof(float)*i,&image.x,sizeof(float));
     return p;
   }
 };
}
namespace ariac_msgs::msg {
 struct Sensors {
   using SharedPtr=std::shared_ptr<Sensors>;
   bool camera{},logical_camera{};
 };
}
struct Output {
 std::vector<sensor_msgs::msg::Image> frames;
 void publish(const sensor_msgs::msg::Image& m){frames.push_back(m);}
 void publish(std::shared_ptr<sensor_msgs::msg::Image> m){frames.push_back(*m);}
};
struct Camera {
 int measured=0;
 int LastMeasurementTime()const{return measured;}
};
struct AriacCameraPlugin {
 static constexpr unsigned FLOAT_SIZE=sizeof(float);
 struct State {
   std::mutex image_mutex_;
   Camera sensor,*depth_parent_sensor_=&sensor;
   std::string frame_name_="assembly-view";
   float min_depth_=0.4f,max_depth_=4.f;
   bool publish_sensor_data_=false;
   Output depth_image_pub_;
 } state,*impl_=&state;
 void OnNewDepthFrame(const float*,unsigned,unsigned,unsigned,const std::string&);
 void SensorHealthCallback(const ariac_msgs::msg::Sensors::SharedPtr);
};
#include "selected.inc"
int main(){
 int i,camera,logical,t,enabled,raw;
 while(std::cin>>i>>camera>>logical>>t>>enabled>>raw){
   AriacCameraPlugin a;
   auto h=std::make_shared<ariac_msgs::msg::Sensors>();
   h->camera=bool(camera);h->logical_camera=bool(logical);
   a.SensorHealthCallback(h);
   a.state.sensor.measured=t;
   float depth=raw/4.f;
   if(enabled)a.OnNewDepthFrame(&depth,1,1,1,"FLOAT32");
   const auto& messages=a.state.depth_image_pub_.frames;
   std::cout<<i<<' '<<messages.size();
   if(!messages.empty()){
     float actual;auto& m=messages.front();
     assert(m.data.size()==4 && m.encoding=="32FC1");
     std::memcpy(&actual,m.data.data(),sizeof(actual));
     assert(m.header.stamp==t);
     int code=std::isfinite(actual)?int(4*actual):(actual<0?-999:999);
     std::cout<<' '<<m.header.stamp<<' '<<code;
   }
   std::cout<<'\n';
 }
}
