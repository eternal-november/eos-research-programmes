using rmf_fleet_adapter::lift_supervisor::Node;
LiftRequest request(std::string name,std::string floor,int type=LiftRequest::REQUEST_AGV_MODE) {
  LiftRequest r;
  r.session_id=name;r.destination_floor=floor;r.request_type=type;
  return r;
}
int test(bool busy,bool occupied,bool late_entry=false) {
  Node n;
  LiftPlugin sp;
  EntityComponentManager e;
  for (auto id:{1,2,3}) {
    PoseData pose;
    pose.p.x=id==1?0:id==2?(occupied?.25:2):8;
    e.poses.emplace(id,components::Pose(pose));
    e.vels[id]=components::LinearVelocityCmd();
  }
  sp._initial_poses[1]=e.poses.at(1).Data();
  sp._initial_aabbs[1]={{-1,-1,-1},{1,1,1}};
  sp._last_lift_command[1]=LiftCommand{}; // native startup retains a command
  auto send=[&](const LiftRequest& r) {
    n._adapter_lift_request_update(std::make_unique<LiftRequest>(r));
  };
  auto apply=[&]() {sp.apply(&e,std::make_unique<LiftRequest>(n._lift_request_pub->sent.back()));};
  auto state=[&]() {return sp.get_current_state(1,e,e.lift.Data(),e.active?&*e.active:nullptr);};
  send(request("fleetA","A"));apply();assert(state().session_id=="fleetA");
  if (!busy) e.active.reset(); // native floor+door command completes at this cut
  send(request("fleetA","A",LiftRequest::REQUEST_END_SESSION));apply();
  if (busy) assert(state().session_id=="fleetA" && e.active);
  else {
    assert(state().session_id=="" && e.active);
    e.active.reset(); // END destination is current floor, doors have settled
  }
  auto disclosed=state(); // replacing disclosed cabin occupancy would be unsound
  assert(disclosed.session_id==(busy?"fleetA":""));
  send(request("fleetB","B"));apply();
  if (busy) {
    assert(state().session_id=="fleetA");
    e.active.reset();  // old floor/door command completed, not proof of body exit
    n._lift_state_update(std::make_unique<LiftState>(state()));
    assert(n._lift_request_pub->sent.back().session_id=="fleetB");
    apply();
  }
  assert(state().session_id=="fleetB" && e.active);
  assert(sp.get_payloads(e,1).size()==size_t(occupied));
  if (late_entry) {
    assert(!occupied);
    e.poses.at(2).Data().p.x=.25; // actual late pose; all lift session fields unchanged
  }
  sp.velocity(e,1,.625); // authored nonzero cabin velocity; unchanged payload write
  assert(e.vels.at(3).Data()[2]==0);
  return e.vels.at(2).Data()[2] != 0;
}
int main() {
  assert(test(false,true)==1);
  assert(test(true,true)==1);
  assert(test(false,false)==0);
  assert(test(true,false)==0);
  assert(test(false,false,true)==1);
  std::cout<<"end accepted or end refused while busy: successor command accepted after command completion\n"
     <<"old body with modeled pose in cabin: native payload write follows successor motion\n"
     <<"old body moved clear, same session/command cuts: no payload write to it\n"
     <<"clear at successor acceptance, enters before modeled velocity cut: native payload write\n";
}
