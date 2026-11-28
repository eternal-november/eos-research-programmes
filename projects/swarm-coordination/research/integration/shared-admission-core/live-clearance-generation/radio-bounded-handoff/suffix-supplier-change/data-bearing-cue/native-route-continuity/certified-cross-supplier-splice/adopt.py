from pathlib import Path
p=Path
def extract(file,start):
    src=p(file).read_text()
    i=src.index(start)
    j=src.index("\n}",src.index("\n{",i))+2
    return src[i:j]+"\n"
def swap(s,a,b):
    assert s.count(a)==1,a
    return s.replace(a,b)
s=p("staged_replay.inc").read_text()
def adopt(s):
    s=swap(s,"struct CommsBrokerPlugin{",'''namespace ignition { namespace msgs {
 struct Time {int seconds,nanos; int sec()const{return seconds;} int nsec()const{return nanos;}};
 struct Header {Time t; bool has_stamp()const{return true;} const Time& stamp()const{return t;}};
 struct Entry {
   std::string key; Pose pose;
   const std::string& name()const{return key;}
 };
 inline Pose Convert(const Entry& row){return row.pose;}
 struct Pose_V {
  Header h; std::vector<Entry> entries;
  bool has_header()const{return true;} const Header& header()const{return h;}
  int pose_size()const{return int(entries.size());}
  const Entry& pose(int i)const{return entries.at(i);}
 };
}}
struct Broker;
struct PoseClock{
 void Set(int sec,int nsec){ now=sec+nsec/1000000000.; }
};
struct CommsBrokerPlugin{
 Broker* brokerTarget=nullptr;
 PoseClock simTime;
 void OnPose(const ignition::msgs::Pose_V& msg);''')
    s=swap(s," void DispatchMessages();",''' std::function<void()> beforeDispatch;
 void NotifyNeighbors(){if(beforeDispatch)beforeDispatch();}
 void SetCommunicationFunction(decltype(communication_function) fn){communication_function=fn;}
 void OnMessage(const subt::msgs::Datagram& req);
 void DispatchMessages();''')
    on=extract("broker.cc","void CommsBrokerPlugin::OnPose(")
    on=swap(on,"\n{","\n{\n  auto& broker=*brokerTarget;")
    # Bind the plugin-owned broker to the fixture instance.
    assert on.count("this->broker.")==2
    on=on.replace("this->broker.","broker.")
    enq=extract("src1","void Broker::OnMessage(")
    s=swap(s,'#include "dispatch.inc"','#include "dispatch.inc"\n'+enq+on)
    return s
p("staged_replay.inc").write_text(adopt(s))
