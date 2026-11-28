#include <array>
#include <fstream>
#include "pinned_broker.h"
const std::array<uint64_t,5> ids{18,39,16,13,42};
const std::array<Point,5> p{Point{100,-25,0},Point{50,25,0},
   Point{100,100,0},Point{100,50,0},Point{100,75,0}};
void attach_visibility(Live& live,const char* matrix) {
 std::ifstream is(matrix);
 double d[5][5]; for(auto& row:d)for(auto& w:row)assert(is>>w);
 World& w=live.w;
   auto& tr=w.tracker;
   auto& m=*tr.visibilityModel;
   auto& t=m.visibilityTable;
   m.defaultRangeConfig.max_range=72.;
   m.defaultRangeConfig.scaling_factor=.55;
   for(unsigned i=0;i<ids.size();++i){
     t.vertices.emplace(std::make_tuple((int32_t)p[i].x,(int32_t)p[i].y,
                                         (int32_t)p[i].z),ids[i]);
     t.visibilityGraph.vertices.emplace(ids[i],0);
     for(unsigned j=0;j<ids.size();++j)
       t.visibilityGraph.projected[ids[i]][ids[j]]={d[i][j],0};
   }
   t.PopulateVisibilityInfo();

 w.b.pose_update_f=[](const auto& id){
    return std::make_tuple(true,Pose{id=="Base"?p[1]:(id=="P"?p[0]:p[2])},now);
 };
}

int main(int argc,char** argv) {
    assert(argc==2);
    std::unique_ptr<Live> live;
    std::string cmd, payloadReceived;
    while (std::cin >> cmd) {
        if (cmd == "reset") {
            live=std::make_unique<Live>(320);
            attach_visibility(*live,argv[1]);
            live->bind("setup","Q");
            live->bind("proof","Far");
            for(auto key:{"Free","X"}) {
                auto n=std::make_shared<TeamNode>(*live->w.b.team->at("Far"));
                live->w.b.team->emplace(key,n);
            }
            live->bind("unrelated","Free");
            live->bind("extra","X");
            live->bind("sink","X");
            live->bind("preq","Q");live->bind("preP","P");
            for (auto tag : {"setup","owed","proof","extra","sink","preq","preP"}) {
                live->w.app.callbacks[std::string(tag)+":7"] = [&](auto,auto,auto,const auto& bytes){
                    assert(payloadReceived.empty());
                    payloadReceived=bytes;
                };
            }
            std::cout<<"ok"<<std::endl;
        } else if(cmd=="relay") {
            int tick;std::string kind;std::cin>>tick>>kind;
            assert(tick/4.0>=now);now=tick/4.0;
            auto& tr=live->w.tracker;
            const bool moving=kind=="moving";
            assert(moving || kind=="near" || kind=="far");
            tr.poses[moving?"probe__breadcrumb__moving":"probe__breadcrumb__1__static__"]=Pose{p[kind=="far"?4:3]};
            auto before=tr.visibilityModel->rebuilds;
            tr.UpdateIfNewBreadcrumbs();
            std::cout<<tr.visibilityModel->rebuilds-before<<std::endl;
        } else if (cmd == "side") {
            int tick; std::cin>>tick;
            live->send(tick,"Side","unrelated",1,true);
        } else if (cmd == "sample") {
            int tick; std::cin>>tick;
            live->status(tick);
        } else if (cmd == "send") {
            int tick; int link; std::string src,dst,bytes;
            std::cin>>tick>>src>>dst>>bytes>>link;
            payloadReceived.clear();
            now=tick/4.0;
            auto was=Live::used(live->w.state(src).bytes_sent,tick);
            assert(link>=0 && link<=2);
            auto& cfg=live->w.b.team->at(src)->radio;
            const auto saved=cfg.pathloss_f;const auto power=cfg.default_tx_power;
            live->w.path_available=bool(link);
            if(link==2){
                assert((src=="P"||src=="Q")&&dst=="owed");
                cfg.default_tx_power=80;
                cfg.pathloss_f=[&](double watts,auto& a,auto& b,bool& used){
                    return live->w.tracker.visibilityModel->ComputeReceivedPower(watts,a,b,used);
                };
            }
            live->w.b.incomingMsgs.push_back({src,dst,bytes});
            live->w.b.DispatchMessages();
            assert(live->w.b.incomingMsgs.empty());
            live->w.path_available=true;cfg.pathloss_f=saved;cfg.default_tx_power=power;
            std::cout<<(payloadReceived.empty() ? "-" : payloadReceived)
                <<' '<<Live::used(live->w.state(src).bytes_sent,tick)-was<<std::endl;
        } else {
            assert(false);
        }
    }
}
