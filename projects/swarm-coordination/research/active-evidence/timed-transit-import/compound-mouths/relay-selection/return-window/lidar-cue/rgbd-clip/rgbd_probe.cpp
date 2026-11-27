// Executes extracted callback copies, guarded clipping and XYZ packing on supplied frames.
#include <array>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <limits>
#include <mutex>
#include <string>
#include <vector>
namespace math { constexpr double INF_D = std::numeric_limits<double>::infinity(); }
namespace msgs {
struct Field { int k; unsigned offset() const { return unsigned(k)*4; } };
struct PointCloudPacked {
 unsigned w;
 unsigned width()const {return w;} unsigned height()const{return 1;}
 unsigned point_step()const{return 16;} unsigned row_step()const{return width()*point_step();}
 bool is_bigendian()const{return false;}
 Field field(int k)const{return {k};}
 std::string data;
 std::string* mutable_data(){ return &data; }
};
}
struct PointCloudUtil {
 void FillMsg(msgs::PointCloudPacked&, const float*, bool, unsigned char*, float* = nullptr)const;
 void DecodeRGBAFromFloat(float, uint8_t&, uint8_t&, uint8_t&, uint8_t&)const {} // color not measured
};
struct Connected {
 bool yes=false;
 bool HasConnections() const {return yes;}
};
struct RgbdCameraSensorPrivate {
 std::mutex mutex;
 bool hasDepthNearClip=true,hasDepthFarClip=true;
 float *depthBuffer=nullptr,*pointCloudBuffer=nullptr;
 unsigned channels=0;
 double depthNearClip,depthFarClip;
 Connected depthPub,pointPub;
 void OnNewDepthFrame(const float*,unsigned,unsigned,unsigned,const std::string&);
 void OnNewRgbPointCloud(const float*,unsigned,unsigned,unsigned,const std::string&);
 ~RgbdCameraSensorPrivate(){delete[] depthBuffer;delete[] pointCloudBuffer;}
};
struct Sensor {
 RgbdCameraSensorPrivate* dataPtr;
 void trim(unsigned);
 void mask(unsigned);
};
#include "selected.inc"
static float packed(const msgs::PointCloudPacked& p,unsigned i,unsigned j){
 float f;std::memcpy(&f,p.data.data()+i*p.point_step()+4*j,4);return f;
}
int main(){
 auto inf=std::numeric_limits<float>::infinity();
 const float near=float(depthNear), lower=std::nextafter(near,0.0f);
 const float far=float(depthFar), upper=std::nextafter(far,inf);
 // Exactly representable near values below/above; .1f itself is not .1 as a double.
 const std::array<float,11> frame={.05f,lower,near,1,5,far,upper,37,299,inf,-inf};
 constexpr unsigned n=frame.size();
 std::array<float,4*n> points;
 for(unsigned i=0;i<n;++i){
  points[4*i]=frame[i]; points[4*i+1]=1; points[4*i+2]=2;points[4*i+3]=0;
 }
 RgbdCameraSensorPrivate d;
 d.depthNearClip=depthNear;d.depthFarClip=depthFar;d.pointPub.yes=true;
 Sensor s{&d}; PointCloudUtil util;
 unsigned writes=0;
 for(int bits=0;bits<16;++bits) {
  std::vector<std::array<float,3>> a,b;
  for(unsigned t=0;t<4;++t) {
   d.depthPub.yes=(bits>>t)&1;
   d.OnNewDepthFrame(frame.data(),n,1,1,"");
   d.OnNewRgbPointCloud(points.data(),n,1,4,"");
   s.trim(n);s.mask(n);
   msgs::PointCloudPacked p{n};
   util.FillMsg(p,d.pointCloudBuffer,false,nullptr);
   for(unsigned i=0;i<n;++i) {
    const float z=frame[i];
    const bool upperTest=d.depthPub.yes && z>depthFar;
    const bool lowerTest=d.depthPub.yes && z<depthNear;
    const auto x=upperTest?inf:(lowerTest?-inf:z);
    for(unsigned j=0;j<3;++j){
     const auto expected=std::isinf(x)?x:(j?float(j):x);
     assert(packed(p,i,j)==expected);++writes;
    }
   }
   assert(std::isfinite(packed(p,3,0)) && std::isfinite(packed(p,5,0)));
   assert(std::isinf(packed(p,7,0))==d.depthPub.yes);
  }
 }
 std::cout<<"64 freshly supplied frames, "<<writes
   <<" packed XYZ comparisons; the 37 m finite sample survives exactly without a depth-image subscriber\n";
}
