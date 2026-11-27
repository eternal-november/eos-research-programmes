#include <cassert>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <functional>
#include <iostream>
#include <limits>
#include <map>
#include <memory>
#include <string>
#include <tuple>
#include <vector>

struct Silent {
  template<class T> Silent& operator<<(const T&) { return *this; }
  Silent& operator<<(std::ostream& (*)(std::ostream&)){ return *this; }
};
#define ignwarn Silent()
#define igndbg Silent()
namespace ignition { namespace math {
struct Vector3d {
  double x=0,y=0,z=0;
  double X()const{return x;} double Y()const{return y;} double Z()const{return z;}
  double Distance(const Vector3d& q)const{return std::hypot(x-q.x,y-q.y,z-q.z);}
};
}}
using Point=ignition::math::Vector3d;
struct Pose {Point point; Point Pos()const{return point;}};
struct radio_state {Pose pose;};
struct rf_power {double mean,sigma;};
struct rf_configuration {
  double max_range=500, fading_exponent=1.5, L0=40, sigma=10,
      scaling_factor=1,range_per_hop=2;
};
namespace range_model {
using ::rf_configuration;
rf_power log_normal_received_power(const double&,radio_state&,radio_state&,const rf_configuration&);
rf_power log_normal_v2_received_power(const double&,const double&,const unsigned int&,const rf_configuration&);
}
using range_model::log_normal_received_power;
struct VisibilityCost {
  double cost;
  std::vector<uint64_t> route;
  Point posFirstBreadcrumb,posLastBreadcrumb;
  double greatestDistanceSingleHop;
};
struct VisibilityTable {
  std::string lutPath;
  std::map<std::tuple<int32_t,int32_t,int32_t>,uint64_t> vertices;
  std::map<std::pair<uint64_t,uint64_t>,VisibilityCost> visibilityInfo;
  std::map<uint64_t,std::vector<Point>> breadcrumbs;
  bool LoadLUT();
  // Graph shortest costs supplied separately from the pinned .dot.
  void PopulateVisibilityInfo(){}
  const auto& Vertices()const{return vertices;}
  const auto& Breadcrumbs()const{return breadcrumbs;}
  VisibilityCost Cost(const Point&,const Point&)const;
};
struct VisibilityModel {
  struct Config{double commsCostMax=10,visibilityCostToFadingExponent=0.2;};
  Config visibilityConfig;
  rf_configuration defaultRangeConfig;
  VisibilityTable visibilityTable;
  bool ready;
  VisibilityModel(Config c,rf_configuration r,const std::string& p)
      : visibilityConfig(c),defaultRangeConfig(r),visibilityTable{p},ready(visibilityTable.LoadLUT()) {}
  bool Initialized()const{return ready;}
  rf_power ComputeReceivedPower(const double&,radio_state&,radio_state&,bool&);
};
#include "native.inc"
using pathloss_function=std::function<rf_power(const double&,radio_state&,radio_state&,bool&)>;
struct Radio {pathloss_function pathloss_f;};
namespace tinyxml2 {
struct XMLElement {
  const XMLElement *section=nullptr,*mode=nullptr;
  const XMLElement* FirstChildElement(const std::string& s)const {
    return s=="comms_model" ? section : s=="comms_model_type" ? mode : nullptr;
  }
  const char* GetText()const{return "visibility_range";}
};
}
struct Selector {
  std::unique_ptr<VisibilityModel> visibilityModel;
  Radio radio;
  std::string load(const std::string& worldName) {
    rf_configuration rangeConfig;
    VisibilityModel::Config visibilityConfig;
    const tinyxml2::XMLElement leaf,section{nullptr,&leaf},root{&section,nullptr};
    const auto* _elem=&root;
    const tinyxml2::XMLElement* commsModelElem=nullptr;
    #include "mode.inc"
    return commsModelType;
  }
};
int main(int argc,char** argv) {
  assert(argc==3);
  Selector ready,missing;
  auto a=ready.load(argv[1]); auto b=missing.load(argv[2]);
  std::cout<<a<<' '<<b<<'\n';
  auto& table=ready.visibilityModel->visibilityTable.visibilityInfo;
  size_t n; std::cin>>n;
  for(size_t i=0;i<n;++i) {
    uint64_t x,y; double c; std::cin>>x>>y>>c;
    table[{x,y}]={c,{},{},{},0};
  }
  int k; Point p,q;
  while(std::cin>>k>>p.x>>p.y>>p.z>>q.x>>q.y>>q.z) {
    if(k) {
      uint64_t x,y; double cost,largest; Point first,last;
      std::cin>>x>>y>>cost>>largest>>first.x>>first.y>>first.z>>last.x>>last.y>>last.z;
      // Test a declared relay route at the native RF input, not its chooser.
      table[{x,y}]={cost,std::vector<uint64_t>(k),first,last,largest};
    }
    radio_state s{{p}},t{{q}};
    bool via=false,untouched0=false,untouched1=true;
    auto f=ready.radio.pathloss_f(20,s,t,via);
    auto g=missing.radio.pathloss_f(20,s,t,untouched0);
    auto h=missing.radio.pathloss_f(20,s,t,untouched1);
    assert(g.mean==h.mean);
    std::cout.precision(16);
    std::cout<<f.mean<<' '<<g.mean<<' '<<via<<' '<<untouched0<<' '<<untouched1<<'\n';
  }
}
