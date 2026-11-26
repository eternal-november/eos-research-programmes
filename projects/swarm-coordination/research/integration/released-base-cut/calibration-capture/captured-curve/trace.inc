using namespace vda5050_core;
using namespace vda5050_core::client::adapter;
int main(){
  auto run=[](const Transformation& T) {
    using namespace std;
    const string key="floor_1";
    StateManager state; state.set_transformation(T,key);
    Adapter::Implementation a; a.state_manager=&state;
    types::Node from{"A",0,true,types::NodePosition{0,0,nullopt,key},nullopt};
    types::Node to{"B",2,true,types::NodePosition{4,0,nullopt,key},nullopt};
    types::Trajectory route{2,{0,0,0,1,1,1},{{0,0,1},{2,-4,1},{4,0,1}}};
    types::Edge e{"A-B",1,route,nullopt,nullopt,nullopt,nullopt,nullopt,nullopt};
    a.active_order.value.order=ActiveOrder{
        {"inspection",1,{from,to},{e}},false,0,{{0,0},{2,1}},{{1,0}}};
    size_t seen=0;
    a.navigation_callback=[&](NodeRequest n,optional<EdgeRequest> observed,int id){
      assert(id==1 && n.sequence_id()==2 && n.node_position()->map_id==key);
      assert(observed && observed->edge_id()=="A-B" && observed->sequence_id()==1);
      assert(observed->trajectory()==optional<types::Trajectory>(route));
      auto local=T.to_agv_pose({4,0,0});
      assert(abs(n.node_position()->x-local.x)<1e-12 &&
             abs(n.node_position()->y-local.y)<1e-12 && !n.node_position()->theta);
      if (T.to_world_pose({0,0,0}).x==0) {
        for (const auto& p:observed->trajectory()->control_points)
          std::cout<<p.x<<' '<<p.y<<' '<<p.weight<<'\n';
      }
      ++seen;
    };
    a.process_navigation();
    assert(seen==1);
  };
  run(Transformation::calibrate({0,0,0},{0,0,0}));
  run(Transformation::calibrate({1,-2,0},{0,0,0}));
  run(Transformation::calibrate({8,0,std::numbers::pi},{0,0,0}));
  std::cout<<"three transforms: node converted, world control points unchanged\n";
}
