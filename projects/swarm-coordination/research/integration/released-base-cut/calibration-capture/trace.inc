using namespace vda5050_core;
using namespace vda5050_core::client::adapter;
using namespace std;
struct Run {
  StateManager state;
  Adapter::Implementation adapter;
  vector<NodeRequest> outputs;
  const string key="floor_1";
  Run(double x,double y,bool heading) {
    adapter.state_manager=&state;
    optional<double> theta;
    if(heading)theta=0;
    types::NodePosition pos{x,y,theta,key};
    adapter.active_order.value.order=ActiveOrder{
      {"inspection",1,{{"B",0,true,pos,nullopt}},{}},false,nullopt,{{0,0}},{}};
    adapter.navigation_callback=[&](NodeRequest req,optional<EdgeRequest> edge,int id) {
      assert(!edge&&id==1);
      outputs.push_back(std::move(req));
    };
    state.initialize_position(0,0,0,key);
  }
  void calibrate(Pose2D p) {
    state.set_transformation(Transformation::calibrate(p,{0,0,0}),key);
  }
  void dispatch() {adapter.process_navigation();}
  auto request() const {return outputs.at(0).node_position().value();}
};
int main(){
  Run old(4,0,true),fresh(4,0,true);
  old.calibrate({1,0,0});fresh.calibrate({1,0,0});
  old.dispatch(); // old callback still pending
  old.calibrate({0,0,0});fresh.calibrate({0,0,0});
  fresh.dispatch();
  assert(old.state.state().agv_position==fresh.state.state().agv_position);
  old.state.set_position(0,0,0,old.key);fresh.state.set_position(0,0,0,fresh.key);
  assert(old.state.state().agv_position==fresh.state.state().agv_position);
  auto a=old.request(),b=fresh.request();
  assert(a.map_id==b.map_id&&a.map_id==old.key&&a.x==3&&b.x==4);
  old.dispatch();fresh.dispatch();
  assert(old.outputs.size()==1&&fresh.outputs.size()==1);
  cout<<"same order, current transform, initialized pose and fresh pose\n"
      <<"callback local x: "<<a.x<<" versus "<<b.x
      <<"; no redispatch while outstanding\n";

  // A generation mismatch alone is not a reason to retire a position-only request.
  Run before(0,0,false),after(0,0,false);
  before.calibrate({0,0,1.0});before.dispatch();before.calibrate({0,0,0});
  after.calibrate({0,0,0});after.dispatch();
  auto c=before.request(),d=after.request();
  assert(c.x==d.x&&c.y==d.y&&!c.theta&&!d.theta);
  Run oriented(0,0,true);
  oriented.calibrate({0,0,1.0});oriented.dispatch();
  assert(oriented.request().theta==optional<double>(-1.0));
  cout<<"rotation about target: position-only unchanged; explicit yaw changes\n";

  unsigned examined=0;
  for(int dx=-4;dx<=4;dx++)for(int px=-4;px<=4;px++)for(int yaw=0;yaw<2;yaw++){
    Run a(px,2,yaw),b(px,2,yaw);
    a.calibrate({double(dx),0,0});a.dispatch();
    a.calibrate({0,0,0});b.calibrate({0,0,0});b.dispatch();
    assert(a.request().x==px-dx && b.request().x==px);
    assert(a.request().y==2 && b.request().y==2);
    assert((a.request().x==b.request().x)==(dx==0));
    examined++;
  }
  cout<<"exact integer translation cases: "<<examined<<"\n";
}
