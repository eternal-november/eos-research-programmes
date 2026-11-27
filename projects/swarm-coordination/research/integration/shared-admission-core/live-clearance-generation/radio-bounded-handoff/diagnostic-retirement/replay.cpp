#include "scope.cpp"
#include "unregister.inc"
#include "enqueue.inc"

struct OutcomeNow {
  uint64_t initial, after_probe, final_tx, old_rx;
  size_t pending_initial, side_work;
  bool reached, remaining_binding;
  std::string received;
  int supplier;
  bool extra;
  uint64_t q_tx;
  int old_attempts;
};

static OutcomeNow exercise(unsigned cap, unsigned prior, unsigned probe,
                           bool retire_early, bool shared_address,
                           double deadline, const std::string &body, int arm) {
  Fixture f(cap);
  for (const std::string n : {"Fail", "Diag", "Hold"}) {
    auto t=std::make_shared<TeamNode>();
    t->name=n;t->radio=f.w.b.team->at("P")->radio;
    f.w.b.team->emplace(n,t);
  }
  auto &b=f.w.b;
  b.endpoints["diag:7"].push_back({"Diag"});
  if (shared_address) b.endpoints["diag:7"].push_back({"Hold"});
  b.endpoints["fail:7"].push_back({"Fail"});
  std::string received, sender, received_sender;
  bool extra=false;
  f.w.app.callbacks["Far:7"]=[&](auto src,auto,auto,const auto &p){
    assert(src=="Q");
    if (p=="side") f.side.push_back(now);
    else { assert(p==std::string(160,'e') && !extra); extra=true; }
  };
  f.w.app.callbacks["Base:7"]=[&](auto src,auto,auto,const auto &payload){
    assert((src==sender || (arm==5 && src=="Q")) && payload==body && received.empty());
    received_sender=src;
    received=payload;
  };
  auto sample=[&](double t, bool j, bool retire) {
    auto v=pins(900,j?40:-1);
    v.push_back({"Fail",{{3000}}});
    if (!retire) v.push_back({"Diag",{{3000}}});
    v.push_back({"Hold",{{3000}}});
    f.frame(t,v);
  };
  // Same cutoff for both debits. Registering a fixture participant
  // without its first sample is an authored lifecycle event.
  auto unused=b.team->extract("J");
  sample(.25,false,false);
  if (prior) {
    b.OnMessage({"P","fail",std::string(prior,'p')});
    b.DispatchMessages();
  }
  assert(f.w.state("P").bytes_sent_this_epoch==prior);
  b.team->insert(std::move(unused));
  b.OnMessage({"P","diag",std::string(probe,'d')});
  b.OnMessage({"Q","Far","side"});
  b.DispatchMessages();
  const auto pending=b.incomingMsgs.size();
  const auto initial=f.w.state("P").bytes_sent_this_epoch;
  assert(pending==2 && initial==prior && f.side.empty());
  if (retire_early) assert(b.Unregister("Diag"));
  const auto &bindings=b.endpoints.at("diag:7");
  assert(bindings.size()==size_t(shared_address)+(retire_early?0:1));
  sample(.25,true,retire_early);
  b.DispatchMessages();
  assert(b.incomingMsgs.empty() && f.side==std::vector<double>{.25});
  const auto after=f.w.state("P").bytes_sent_this_epoch;
  if (!retire_early) assert(b.Unregister("Diag"));
  assert(bindings.size()==size_t(shared_address));
  // Authored two-prepositioned-qualified-copy campaign (arms 1--3).
  // The source-local policy reads only P's charged row and a fixed no-more-
  // sends premise, not a hidden fault ID, endpoint count or callback oracle.
  // The deadline rule here has only the one known cohort at .25.
  const auto live=(deadline<=1.25?after:0);
  const bool preferP=live+body.size()<=cap;
  sender=(arm==1 || (arm==2 && !preferP))?"Q":"P";
  sample(deadline,true,true);
  b.OnMessage({sender,"Base",body});
  if (arm==5) b.OnMessage({"Q","Base",body});
  if (arm && arm!=4) b.OnMessage({"Q","Far",std::string(160,'e')});
  b.DispatchMessages();
  assert(b.incomingMsgs.empty());
  int attempts=arm==5?2:1;
  if (arm==4 && received.empty()) {
    sender="Q";
    b.OnMessage({sender,"Base",body});
    b.DispatchMessages();
    assert(b.incomingMsgs.empty());
    ++attempts;
  }
  if (arm==4) {
    b.OnMessage({"Q","Far",std::string(160,'e')});
    b.DispatchMessages();
    assert(b.incomingMsgs.empty());
  }
  return {initial,after,f.w.state("P").bytes_sent_this_epoch,
          f.w.state("Base").bytes_received_this_epoch,pending,
          f.side.size(),bool(received.size()),bool(bindings.size()),received,(received_sender.empty()?sender:received_sender)=="P"?1:2,extra,f.w.state("Q").bytes_sent_this_epoch,attempts};
}
static void emit(const OutcomeNow &v){
  std::cout<<v.initial<<' '<<v.after_probe<<' '<<v.final_tx<<' '<<v.old_rx<<' '
           <<v.pending_initial<<' '<<v.side_work<<' '<<v.reached<<' '
           <<v.remaining_binding<<' '<<v.supplier<<' '<<v.extra<<' '<<v.q_tx<<' '<<v.old_attempts<<' '<<(v.received.empty()?"-":v.received)<<'\n';
}
int main(int argc,char**argv){
  if (argc!=2)return 2;
  const std::string body=argv[1];
  assert(body.size()==173);
  unsigned cap,prior,probe; bool early,fanout; double deadline; int arm;
  while(std::cin>>cap>>prior>>probe>>early>>fanout>>deadline>>arm)
    emit(exercise(cap,prior,probe,early,fanout,deadline,body,arm));
}
