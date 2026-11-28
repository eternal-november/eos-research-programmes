// Compiled against the pinned selected native #726 extraction.
#include <array>
#include <fstream>
#define main earlier_replay
#include "staged_replay.inc"
#undef main


#include "load.inc"

int main(){
 const std::array<uint64_t,6> ids{18,39,16,13,42,6};
 const std::array<Point,6> p{Point{100,-25,0},Point{50,25,0},Point{100,100,6},
  Point{100,50,9},Point{100,75,8},Point{75,100,6}};
 std::ifstream tbl("dist6.tsv");
 double d[6][6];for(auto& row:d)for(auto& v:row)assert(tbl>>v);
 int closed,omission;double arrival,ix,iy,iz,ax,ay,az;
 while(std::cin>>closed>>omission>>arrival>>ix>>iy>>iz>>ax>>ay>>az){
    World w(256);auto& tr=w.tracker;auto& m=*tr.visibilityModel;auto& t=m.visibilityTable;
    m.defaultRangeConfig.max_range=72.;m.defaultRangeConfig.scaling_factor=.55;
    for(unsigned i=0;i<ids.size();++i){
      t.visibilityGraph.vertices.emplace(ids[i],0);
      for(unsigned j=0;j<ids.size();++j)t.visibilityGraph.projected[ids[i]][ids[j]]={d[i][j],0};
    }
    t.lutPath="cave.dat";assert(t.LoadLUT());
    auto I=std::make_shared<TeamNode>(*w.b.team->at("P"));
    I->name="I";(*w.b.team)["I"]=I;
    w.b.endpoints["I:7"].push_back({"I"});
    for(const auto& id:{"P","Q","I","Base"}){
       auto &cfg=w.b.team->at(id)->radio;cfg.default_tx_power=80;
       cfg.pathloss_f=[&](double watts,auto& a,auto& b,bool& used){return m.ComputeReceivedPower(watts,a,b,used);};
    }
    Point q=p[2],i{100,50,8};
    w.b.pose_update_f=[&](auto who){
      return std::make_tuple(true,Pose{who=="Base"?p[1]:(who=="P"?p[0]:(who=="Q"?q:i))},now);
    };
    bool old=false,oldAck=false,receipt=false,qAck=false;char bit='?';
    w.app.callbacks["Base:7"]=[&](auto who,auto,auto,auto v){
      if(who=="P"){assert(v=="aa");old=true;}
      else {assert(who=="Q"&&v=="rr");receipt=true;}
    };
    w.app.callbacks["I:7"]=[&](auto who,auto,auto,auto v){assert(who=="Base"&&v=="p");oldAck=true;};
    w.app.callbacks["Q:7"]=[&](auto who,auto,auto,auto v){
      if(who=="I"){assert(v=="0"||v=="1");bit=v[0];}
      else {assert(who=="Base"&&v=="q");qAck=true;}
    };
    auto offer=[&](auto src,auto dst,auto data,double at){
       now=at;w.b.incomingMsgs.push_back({src,dst,data});w.b.DispatchMessages();
       assert(w.b.incomingMsgs.empty());
    };
    offer("P","Base","aa",0);assert(old);
    i=Point{100,50.0078125,8};
    offer("Base","I","p",.125);assert(oldAck);
    // One modeled positive return (gate / farther panel), not a raw
    // caller-visible geometry bit. Decode from the physical range seam.
    const auto range=(closed?4.5:6.0)*std::sqrt(1.0004);
    const char cue=range<5?'0':'1';
    assert(omission>=0&&omission<=2);
    // One authored omission skips offer, no simulated send/capacity
    // effects. Wait for positive feedback; a retry does not infer delivery.
    const double cueTime=omission==1?4.725:4.6;
    const auto dT=cueTime-13./3.;
    i=Point{100,58+2*dT-dT*dT/2,8};
    offer("I","Q",std::string(1,cue),cueTime);
    assert(bit==cue&&now+0.2<=5.0);
    // Courier selects from its named received value only.
    const int branch=bit=='0'?5:4;
    assert(closed==(branch==5));
    if(branch==5){
       assert(oldAck);
       i=Point{100,50,8};now=14.;
       tr.poses["tracked__breadcrumb__wall_mounted__static__"]=Pose{p[3]};
       tr.UpdateIfNewBreadcrumbs();assert(m.rebuilds==1);
    }
    q=p[branch];i=Point{ix,iy,iz};
    offer("Q","Base","rr",arrival+(omission==2?.25:.125));assert(receipt&&old);
    i=Point{ax,ay,az};
    offer("Base","Q","q",arrival+.375);assert(qAck);
    std::cout<<(closed?"near":"far")<<" "<<omission<<" old, old receipt, addressed gate read, "
             <<(closed?"one registered relay":"no relay")<<", new and new receipt checked\n";
 }
}
