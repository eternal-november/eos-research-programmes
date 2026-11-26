#define main inherited_replay_main
#include "subt/replay.cpp"
#undef main
int main(){
 for(bool charged:{false,true})for(bool tag:{false,true}){
   std::vector<std::vector<std::tuple<std::string,std::string>>> tapes;
   for(bool old_right:{false,true}){
     World w(5);
     std::map<std::string,std::string> parts;
     std::vector<std::tuple<std::string,std::string>> tape;
     auto spare=std::make_shared<TeamNode>(*w.b.team->at("Base"));
     spare->name="OtherSink";w.b.team->emplace("OtherSink",spare);
     w.b.endpoints["OtherSink:7"].push_back({"OtherSink"});
     w.app.callbacks["OtherSink:7"]=[](auto,auto,auto,const auto&){};
     w.app.callbacks["Base:7"]=[&](auto sender,auto,auto,const auto& payload){
       tape.emplace_back(sender,payload);parts[sender]=payload;
     };
     auto push=[&](std::string who,std::string to,std::string payload){
       w.b.incomingMsgs.push_back({who,to,payload});
     };
     // Same already incurred source debits in the compared histories, no
     // legacy payload observation available other than the later callback.
     if(charged){now=0;push("P","OtherSink","xxx");push("Q","OtherSink","yyy");w.b.DispatchMessages();}
     now=1;
     std::string l=tag?"nll":"ll",r=tag?(old_right?"oq":"nq"):"q";
     push("P","Base",l);push("Q","Base",r);w.b.DispatchMessages();
     bool accepted=parts.size()==2&&(!tag||parts["P"][0]==parts["Q"][0]);
     assert(tape.size()==(charged&&tag?1:2));
     assert(accepted==(!(charged&&tag)&&!(tag&&old_right)));
     tapes.push_back(tape);
     std::cout<<"charged="<<charged<<" tag="<<tag<<" old_right="<<old_right
              <<" arrivals="<<tape.size()<<" accept="<<accepted
              <<" coherent_truth="<<!old_right<<'\n';
   }
   assert((tapes[0]==tapes[1])==!tag);
 }
}
