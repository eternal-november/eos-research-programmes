#include <algorithm>
#include <cfloat>
#include "sensor_base.inc"
namespace ignition::msgs {using PointCloudPacked=::msgs::PointCloudPacked;}
namespace sensor_msgs {
struct PointField {
  enum{INT8,UINT8,INT16,UINT16,INT32,UINT32,FLOAT32,FLOAT64};
  std::string name;unsigned count{},offset{},datatype{};
};
struct PointCloud2 {
 int header{};uint32_t height{},width{},point_step{},row_step{};
 bool is_bigendian{},is_dense{};std::vector<PointField> fields;std::vector<uint8_t> data;
};
}
namespace Eigen {
struct Array4f {
  std::array<float,4> v{};
  void setConstant(float f){v.fill(f);}
  Array4f min(const Array4f& rhs)const{
    Array4f t;for(int j=0;j<4;++j)t.v[j]=std::min(v[j],rhs.v[j]);return t;
  }
  Array4f max(const Array4f& rhs)const{
    Array4f t;for(int j=0;j<4;++j)t.v[j]=std::max(v[j],rhs.v[j]);return t;
  }
};
using Vector4f=Array4f;
}
namespace pcl {
using Array4fMapConst=Eigen::Array4f;
struct PCLPointCloud2: sensor_msgs::PointCloud2 {};
namespace detail {
struct FieldMapping {uint32_t serialized_offset{},struct_offset{},size{};};
}
using MsgFieldMap=std::vector<detail::FieldMapping>;
template<typename T>struct PointCloud {
 int header{};uint32_t height{},width{};bool is_dense{};
 std::vector<T> points;
};
template <typename T>
void removeNaNFromPointCloud(const PointCloud<T>&,PointCloud<T>&,std::vector<int>&);
template<typename T> void getMinMax3D(const PointCloud<T>&,Eigen::Vector4f&,Eigen::Vector4f&);
}
void convert_ign_to_ros(int a,int& b){b=a;} // header not under test
namespace pcl_conversions {
void toPCL(int a,int& b){b=a;}
void toPCL(const std::vector<sensor_msgs::PointField>& a,std::vector<sensor_msgs::PointField>& b){b=a;}
}
#define BOOST_FOREACH(decl,coll) for(decl : coll)
#define pcl_isfinite std::isfinite
#include "converted.inc"
struct XYZ {float x,y,z;Eigen::Array4f getArray4fMap()const{return {{x,y,z,1}};}};
struct Marker {
 RgbdCameraSensorPrivate* dataPtr;
 void flag(){
#include "dense_flag.inc"
 }
};
int main(){
  unsigned rounds=0,false_dense=0,checked=0,restored=0,dangerous_bounds=0;
  using Cloud=pcl::PointCloud<XYZ>;
  for(bool depth:{false,true})
  for(unsigned target=0;target<5;++target)
  for(unsigned inputOrder=0;inputOrder<3;++inputOrder){
    const auto inf=std::numeric_limits<float>::infinity();
    const auto nan=std::numeric_limits<float>::quiet_NaN();
    float z[]={7,37,inf,-inf,nan};
    float raw[]={5,6,8};
    raw[inputOrder]=z[target];
    float points[12]{};
    for(unsigned i=0;i<3;++i){
      points[4*i]=raw[i];points[4*i+1]=1;points[4*i+2]=2;
    }
    RgbdCameraSensorPrivate d;
    d.depthNearClip=depthNear;d.depthFarClip=depthFar;
    d.depthPub.yes=depth;d.pointPub.yes=true;
    d.OnNewDepthFrame(raw,3,1,1,"");
    d.OnNewRgbPointCloud(points,3,1,4,"");
    Sensor s{&d};
    Marker mk{&d};mk.flag();
    s.trim(3);s.mask(3);
    PointCloudUtil util;
    util.FillMsg(d.pointMsg,d.pointCloudBuffer,false,nullptr);
    sensor_msgs::PointCloud2 msg;
    convert_ign_to_ros(d.pointMsg,msg);
    assert(msg.is_dense&&msg.fields.size()==3&&msg.data.size()==48);
    pcl::PCLPointCloud2 v;
    pcl_conversions::toPCL(msg,v);
    assert(v.is_dense&&v.data==msg.data);
    const pcl::MsgFieldMap fieldmap{{0,0,12}};
    Cloud raw_cloud,naive,honest;
    pcl::fromPCLPointCloud2(v,raw_cloud,fieldmap);
    assert(raw_cloud.is_dense);
    std::vector<int> indices,valid;
    std::vector<int> expected;
    for(unsigned i=0;i<3;++i){
      const auto& t=raw_cloud.points[i];
      if(std::isfinite(t.x)&&std::isfinite(t.y)&&std::isfinite(t.z))expected.push_back(i);
      ++checked;
    }
    pcl::removeNaNFromPointCloud(raw_cloud,naive,indices);
    assert(indices==std::vector<int>({0,1,2})&&naive.points.size()==3);
    false_dense+=expected.size()!=3;
    Eigen::Vector4f lo,hi;
    pcl::getMinMax3D(raw_cloud,lo,hi);
    const bool inf_active=std::isinf(lo.v[0])||std::isinf(hi.v[0]);
    if(target!=4)assert(inf_active==(expected.size()!=3));
    dangerous_bounds+=inf_active;
    // A conservative receiver may not trust the producer metadata.
    raw_cloud.is_dense=false;
    pcl::removeNaNFromPointCloud(raw_cloud,honest,valid);
    assert(valid==expected&&honest.is_dense&&honest.points.size()==expected.size());
    pcl::getMinMax3D(honest,lo,hi);
    assert(std::isfinite(lo.v[0])&&std::isfinite(hi.v[0])&&lo.v[0]<=hi.v[0]);
    for(unsigned i=0;i<expected.size();++i){
      auto j=expected[i];assert(honest.points[i].x==raw_cloud.points[j].x);
    }
    if(expected.size()!=3){
      assert(honest.width==2&&honest.height==1);
      assert(std::find(valid.begin(),valid.end(),inputOrder)==valid.end());
      ++restored;
    }
    const bool invalid=target>=2||(depth&&target==1);
    assert(invalid==(expected.size()!=3));
    ++rounds;
  }
  std::cout<<rounds<<" native wire/filter cases; "<<false_dense<<" false dense promises; "
    <<restored<<" finite outputs with retained source indices; "<<dangerous_bounds<<" infinite extrema; "<<checked<<" XYZ predicates\n";
}
