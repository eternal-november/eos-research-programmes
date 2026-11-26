#include "pinned_broker.h"

int main() {
    std::unique_ptr<Live> live;
    std::string cmd, payloadReceived;
    while (std::cin >> cmd) {
        if (cmd == "reset") {
            unsigned int cap; std::cin >> cap;
            live = std::make_unique<Live>(cap);
            live->w.app.callbacks["owed:7"] = [&](auto,auto,auto,const auto& bytes){
                assert(payloadReceived.empty());
                payloadReceived = bytes;
            };
            std::cout << "ok" << std::endl;
        } else if (cmd == "sample") {
            int tick; std::cin >> tick;
            live->status(tick);
        } else if (cmd == "side") {
            int tick; std::cin >> tick;
            live->send(tick,"Side","unrelated",1,true);
        } else if (cmd == "notify") {
            int tick; bool link; std::string src, bytes;
            std::cin >> tick >> src >> bytes >> link;
            payloadReceived.clear();
            now=tick/4.0;
            live->w.path_available=link;
            live->w.b.incomingMsgs.push_back({src,"owed",bytes});
            live->w.b.DispatchMessages();
            assert(live->w.b.incomingMsgs.empty());
            live->w.path_available=true;
            std::cout << (payloadReceived.empty() ? "-" : payloadReceived) << std::endl;
        } else {
            assert(false);
        }
    }
}
