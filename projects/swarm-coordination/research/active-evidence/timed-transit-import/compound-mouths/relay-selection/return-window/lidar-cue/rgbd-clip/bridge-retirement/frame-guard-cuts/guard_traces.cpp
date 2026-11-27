// Source traces for the projected clipping guard, with explicit valid publisher.
#include "lifecycle_selected.inc"
int main(){
 const std::string image="ignition.msgs.Image";
 unsigned count=0;
 for(unsigned code=0;code<4096;++code){
   NodeShared state;
   MessagePublisher member{depthTopic,"bridge","handler",image,"sensor","addr"};
   MessagePublisher sender{depthTopic,"sensor","camera",image,"","camera-addr"};
   Node::Publisher::Data data{&state,sender};
   Node::Publisher publisher{&data};
   unsigned seq=code;std::string pattern,ops;
   pattern.push_back(publisher.HasConnections()?'1':'0');
   for(int i=0;i<6;++i){
     unsigned op=seq%4;seq/=4;
     if(op==1)state.OnNewRegistration(member);
     if(op==2)state.OnEndRegistration(member);
     if(op==3)expire(state,member.proc);
     ops+=char('0'+op);pattern.push_back(publisher.HasConnections()?'1':'0');
   }
   std::cout<<ops<<' '<<pattern<<'\n';++count;
 }
 assert(count==4096);
}
