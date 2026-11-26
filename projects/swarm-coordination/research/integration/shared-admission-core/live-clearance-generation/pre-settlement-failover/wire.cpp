#include "pinned_broker.h"
int main() {
    std::unique_ptr<Live> live;
    std::string cmd, payloadReceived;
    while (std::cin >> cmd) {
        if (cmd == "reset") {
            live=std::make_unique<Live>(5);
            live->bind("setup","Q");
            live->bind("proof","Far");
            for (auto tag : {"setup","owed","proof"}) {
                live->w.app.callbacks[std::string(tag)+":7"] = [&](auto,auto,auto,const auto& bytes){
                    assert(payloadReceived.empty());
                    payloadReceived=bytes;
                };
            }
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
            live->w.path_available=link;
            live->w.b.incomingMsgs.push_back({src,dst,bytes});
            live->w.b.DispatchMessages();
            assert(live->w.b.incomingMsgs.empty());
            live->w.path_available=true;
            std::cout<<(payloadReceived.empty() ? "-" : payloadReceived)<<std::endl;
        } else {
            assert(false);
        }
    }
}
