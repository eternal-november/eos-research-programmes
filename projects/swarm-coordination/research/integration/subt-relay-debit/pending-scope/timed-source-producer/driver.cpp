#define main inherited_old_main
#include "replay.cpp"
#undef main

struct Job { std::string src,app; unsigned bytes; double when; bool old; };
using Debits=std::vector<std::pair<double,uint64_t>>;
struct TimedSource {
  World plant;
  Job preceding={"P","OldFirst",2,0,true}, tail={"Q","OldTail",2,.75,true},
      fresh={"P","New",3,.5,false};
  unsigned first=0,last=0,optional=0,independent=0;
  int version=0,read_count=0,forecast_jobs=0;
  bool reserved=false;
  TimedSource(double time):plant(5){
    fresh.when=time;
    for(std::string name:{"Second","Independent","Far"}){
      auto n=std::make_shared<TeamNode>();
      n->name=name;n->radio=plant.b.team->at("P")->radio;
      plant.b.team->emplace(name,n);
    }
    bind("OldFirst","Base",first);bind("OldTail","Second",last);
    bind("New","Base",optional);bind("Other","Far",independent);
  }
  void bind(std::string app,std::string physical,unsigned& count){
    plant.b.endpoints[app+":7"]={{physical}};
    auto result=&count;
    plant.app.callbacks[app+":7"]=[result](auto,auto,auto,const auto&){++*result;};
  }
  std::string endpoint(std::string app){
    const auto& x=plant.b.endpoints.at(app+":7");
    assert(x.size()==1);
    return x.front().address;
  }
  void dispatch(const Job& j, bool erased=false){
    assert(j.when>=now || j.when==0);
    now=j.when;
    plant.path_available=!erased;
    plant.b.incomingMsgs.push_back({j.src,j.app,std::string(j.bytes,'e')});
    plant.b.DispatchMessages();
    assert(plant.b.incomingMsgs.empty());
    plant.path_available=true;
    ++version; // A real attempt changes the source ledger qualification.
  }
  bool law(const Job& next,std::string dst,bool plus){
    std::map<std::string,Debits> sends,arrivals;
    for(auto& [id,node]:*plant.b.team){
      auto& st=node->rf_state;
      sends[id]={st.bytes_sent.begin(),st.bytes_sent.end()};
      arrivals[id]={st.bytes_received.begin(),st.bytes_received.end()};
      read_count+=st.bytes_sent.size()+st.bytes_received.size();
    }
    std::vector<Job> pending={next};
    if(plus)pending.push_back(fresh);
    std::sort(pending.begin(),pending.end(),[](auto& a,auto& b){
      if(a.when!=b.when)return a.when<b.when;
      return a.old && !b.old;
    });
    for(auto& j:pending){
      ++forecast_jobs;
      if(j.when<now)return false;
      const auto final=(j.app=="OldTail"?dst:endpoint(j.app));
      const auto& tx=plant.b.team->at(j.src);
      auto legal=[&](const Debits& other){
        uint64_t bytes=j.bytes;
        for(auto [w,c]:other)if(w>=j.when-1.)bytes+=c;
        return bytes*8<=tx->radio.capacity;
      };
      // Forecast reliable required effects on all declared candidate paths.
      if(!legal(sends[j.src])||!legal(arrivals[final]))return false;
      sends[j.src].emplace_back(j.when,j.bytes);
      arrivals[final].emplace_back(j.when,j.bytes);
    }
    return true;
  }
  bool acquire(int received){
    if(received!=version || reserved || !law(tail,endpoint(tail.app),true))return false;
    reserved=true;
    return true;
  }
  bool amend(bool share_tx,bool share_rx){
    Job q=tail;
    q.src=share_tx?"P":"Q";
    std::string dst=share_rx?"Base":"Second";
    if(!law(q,dst,reserved))return false;
    tail=q;
    plant.b.endpoints[tail.app+":7"]={{dst}};
    ++version;
    return true;
  }
  bool cancel_optional(){
    if(!reserved)return false;
    reserved=false;++version;return true;
  }
  void execute_new(bool erase){
    assert(reserved);
    dispatch(fresh,erase);
    reserved=false; // Post-attempt forecast sees the actual persistent debit.
  }
};

#ifndef TIMED_SOURCE_LIBRARY
int main(){
  int kind,s,r,late;
  while(std::cin>>kind>>s>>r>>late){
    now=0;
    const double time=late?1.25:.5;
    TimedSource model(time);
    model.dispatch(model.preceding);
    model.dispatch({"Independent","Other",1,.125,false});
    assert(model.first==1 && model.independent==1);
    int at_cut=model.version;
    bool first_acq=false,refresh=false,edit=false;
    unsigned tDebit=0,rDebit=0;
    if(kind==0){ // Amendment wins and invalidates an already observed record.
      edit=model.amend(s,r);
      first_acq=model.acquire(at_cut);
      refresh=model.acquire(model.version);
    }else{
      first_acq=model.acquire(at_cut);
      assert(first_acq);
      if(kind==1){
        edit=model.amend(s,r);
      }else{
        assert(!late); // Edit after the optional actual attempt, before tail.
        model.execute_new(kind==3);
        tDebit=model.plant.state("P").bytes_sent_this_epoch;
        rDebit=model.plant.state("Base").bytes_received_this_epoch;
        edit=model.amend(s,r);
      }
    }
    if(model.reserved && model.fresh.when<model.tail.when) model.execute_new(false);
    model.dispatch(model.tail);
    if(model.reserved)model.execute_new(false);
    assert(model.first==1&&model.last==1&&model.independent==1);
    std::cout<<int(first_acq)<<' '<<int(refresh)<<' '<<int(edit)<<' '
      <<model.first<<' '<<model.last<<' '<<model.optional<<' '<<model.independent<<' '
      <<tDebit<<' '<<rDebit<<' '<<model.read_count<<' '<<model.forecast_jobs<<'\n';
  }
}

#endif
