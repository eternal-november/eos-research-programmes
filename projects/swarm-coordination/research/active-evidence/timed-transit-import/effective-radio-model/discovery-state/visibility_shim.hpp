#define igndbg NullLog()
using namespace ignition;
using Point=math::Vector3d;
using radio_state=rf_interface::radio_state;
using rf_power=Power;
namespace ignition::math::graph {
using VertexId=uint64_t;
constexpr VertexId kNullId=std::numeric_limits<VertexId>::max();
struct Graph {
 std::map<VertexId,int> vertices;
 std::map<VertexId,std::map<VertexId,std::pair<double,int>>> projected;
 const auto& Vertices()const{return vertices;}
};
auto Dijkstra(const Graph& g, VertexId from){return g.projected.at(from);}
}
namespace range_model {
struct rf_configuration {
 double max_range=500,L0=40,fading_exponent=1.5,sigma=0,scaling_factor=1,range_per_hop=2;
};
rf_power log_normal_v2_received_power(const double&,const double&,const unsigned int&,const rf_configuration&);
}
struct VisibilityCost {
 double cost;
 std::vector<uint64_t> route;
 Point posFirstBreadcrumb,posLastBreadcrumb;
 double greatestDistanceSingleHop;
};
using VisibilityInfo=std::map<std::pair<uint64_t,uint64_t>,VisibilityCost>;
struct VisibilityTable{
 std::map<std::tuple<int32_t,int32_t,int32_t>,uint64_t> vertices;
 std::map<uint64_t,std::vector<Point>> breadcrumbs;
 math::graph::Graph visibilityGraph;
 VisibilityInfo visibilityInfo,visibilityInfoWithoutRelays;
 const auto& Vertices()const{return vertices;}
 const auto& Breadcrumbs()const{return breadcrumbs;}
 VisibilityCost Cost(const Point&, const Point&)const;
 void PopulateVisibilityInfo();
 void PopulateVisibilityInfo(const std::set<Point>&);
 bool PopulateVisibilityInfoHelper(const std::set<uint64_t>&,const uint64_t&,const uint64_t&,
                                    std::set<uint64_t>&,VisibilityInfo&);
 double MaxDistanceSingleHop(const VisibilityInfo&,const std::vector<uint64_t>&,const uint64_t&)const;
};
struct VisibilityModel {
 struct Config {double commsCostMax=10,visibilityCostToFadingExponent=0.2;} visibilityConfig;
 range_model::rf_configuration defaultRangeConfig;
 VisibilityTable visibilityTable;
 rf_power ComputeReceivedPower(const double&,radio_state&,radio_state&,bool&);
 void PopulateVisibilityInfo(const std::set<Point>&);
};
#include "visible.inc"
struct Visibility : VisibilityModel {
 size_t rebuilds=0;
 std::set<Point> points;
 void PopulateVisibilityInfo(const std::set<Point>& p){
   ++rebuilds;points=p;
   VisibilityModel::PopulateVisibilityInfo(p);
 }
};
