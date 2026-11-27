#include "pinned_broker.h"
int main() {
    std::unique_ptr<Live> live;
    std::string cmd, payloadReceived;
    int sender_pose=0;
    while (std::cin >> cmd) {
        if (cmd == "reset") {
            unsigned cap; std::cin>>cap;
            live=std::make_unique<Live>(cap);
            sender_pose=0;
            live->w.b.pose_update_f=[&](std::string id){
                return std::make_tuple(true,Pose{{id=="P"?sender_pose:0}},now);
            };
            live->bind("setup","Q");
            live->bind("proof","Far");
            for(auto key:{"Free","X"}) {
                auto n=std::make_shared<TeamNode>(*live->w.b.team->at("Far"));
                n->name=key;
                live->w.b.team->emplace(key,n);
            }
            live->bind("unrelated","Free");
            live->bind("extra","X");
            live->bind("sink","X");
            for (auto tag : {"setup","owed","proof","extra","sink"}) {
                live->w.app.callbacks[std::string(tag)+":7"] = [&](auto,auto,auto,const auto& bytes){
                    assert(payloadReceived.empty());
                    payloadReceived=bytes;
                };
            }
            std::cout<<"ok"<<std::endl;
        } else if (cmd == "pose") {
            std::cin>>sender_pose;
            std::cout<<"ok"<<std::endl;
        } else if (cmd == "side") {
            int tick; std::cin>>tick;
            live->send(tick,"Side","unrelated",1,true);
        } else if (cmd == "sample") {
            int tick; std::cin>>tick;
            live->status(tick);
        } else if (cmd == "send") {
            int tick; bool link; std::string src,dst,bytes;
            std::cin>>tick>>src>>dst>>bytes>>link;
            payloadReceived.clear();
            now=tick/4.0;
            auto was=Live::used(live->w.state(src).bytes_sent,tick);
            live->w.path_available=link;
            live->w.b.incomingMsgs.push_back({src,dst,bytes});
            live->w.b.DispatchMessages();
            assert(live->w.b.incomingMsgs.empty());
            if(src=="P") assert(live->w.state(src).pose.Pos().x==sender_pose);
            live->w.path_available=true;
            std::cout<<(payloadReceived.empty() ? "-" : payloadReceived)
                <<' '<<Live::used(live->w.state(src).bytes_sent,tick)-was<<std::endl;
        } else {
            assert(false);
        }
    }
}
