#include <set>
using rmf_fleet_adapter::lift_supervisor::Node;

struct Ride {
  std::string session,floor;
  int identity; // authored nonreusable identity at the gate, not a native field
};
struct Grant {
  Entity body;
  int ride,first,last;
  bool live;
};
struct Scene {
  Node n;
  LiftPlugin p;
  EntityComponentManager e;
  Ride ride{"successor","B",42};
  std::vector<Grant> rights;
  Scene(){
    for (auto id:{1,2,3,4}) {
      PoseData pose;
      pose.p.x=id==1?0:id==2?2:id==3?.5:8;
      e.poses.emplace(id,components::Pose(pose));
      e.vels[id]=components::LinearVelocityCmd();
    }
    p._initial_poses[1]=e.poses.at(1).Data();
    p._initial_aabbs[1]={{-1,-1,-1},{1,1,1}};
    p._last_lift_command[1]=LiftCommand{};
    LiftRequest r;
    r.session_id=ride.session;r.destination_floor=ride.floor;
    n._adapter_lift_request_update(std::make_unique<LiftRequest>(r));
    p.apply(&e,std::make_unique<LiftRequest>(n._lift_request_pub->sent.back()));
    assert(e.active&&e.active->Data().session_id==ride.session);
    rights={{3,42,5,8,true}}; // successor's own payload
  }
  void place(Entity b,double x){e.poses.at(b).Data().p.x=x;}
  double command(Entity b){return e.vels.at(b).Data()[2];}
  bool eligible(int t) {
    // Authored serial effect-side check. Native pose selector actually executed.
    if(!e.active || e.active->Data().session_id!=ride.session ||
       e.active->Data().destination_floor!=ride.floor) return false;
    for (auto a:p.get_payloads(e,1)) {
      if(!e.EntityHasComponentType(a,components::LinearVelocityCmd().TypeId()))continue;
      bool permitted=false;
      for (const auto& g:rights) {
        permitted|=g.body==a&&g.ride==ride.identity&&g.live&&g.first<=t&&t<=g.last;
      }
      if(!permitted)return false;
    }
    return true;
  }
  bool proposed_write(int t,double speed) {
    assert(speed!=0);
    if(!eligible(t)) return false; // no claim that inhibition clears old values
    p.velocity(e,1,speed);        // unchanged native payload-write logic
    return true;
  }
};
int main() {
  {
    Scene a;
    assert(a.eligible(5)); // only the successor body, at a valid command version
    a.place(2,.25);
    assert(!a.proposed_write(5,.625));
    assert(a.command(2)==0&&a.command(3)==0); // stops the entire modeled batch
    std::cout<<"unpermitted late physical entry: entire new write refused\n";
  }
  {
    Scene a;
    a.place(2,.25);
    a.rights.push_back({2,42,5,8,true});
    assert(a.proposed_write(5,.625)&&a.command(2)==.625&&a.command(3)==.625);
    assert(a.command(4)==0);
    a.rights.back().live=false;
    assert(!a.proposed_write(6,.75));
    assert(a.command(2)==.625&&a.command(3)==.625); // old commands unreconciled
    a.p.velocity(a.e,1,0.0);
    assert(a.command(2)==.625&&a.command(3)==.625); // selected zero path skips writes
    std::cout<<"authorized residual carried at write; refusal and zero branch leave earlier values in modeled storage\n";
  }
  {
    Scene a;
    a.place(2,.25);
    a.rights.push_back({2,41,0,30,true}); // proper owner, wrong command epoch
    assert(!a.proposed_write(5,.5));
    a.rights.push_back({2,42,6,7,true});
    assert(!a.eligible(5)&&a.proposed_write(6,.5)&&a.proposed_write(7,.75)&&!a.eligible(8));
    assert(a.command(2)==.75);
    std::cout<<"wrong command version refused; current permission valid at inclusive edges only\n";
  }
  {
    Scene a;
    a.place(2,.25);
    a.e.vels.erase(2);
    assert(a.proposed_write(5,.625));
    // No selected native velocity effect on entity 2; not a clearance result.
    assert(a.command(3)==.625);
    std::cout<<"effect guard scopes selected velocity-command writes, not physical cabin occupancy\n";
  }
}
