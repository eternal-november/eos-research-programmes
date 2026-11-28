#include "temporal_parent.inc"

struct Result{bool old;std::array<bool,2> transition;std::array<int,2> missing;};
Result run(std::array<int,2> proposal,bool defer){
   Driver d; EffectCut x(d);
   constexpr std::array<long long,5> timeline{125000,500000,625000,750000,1000000};
   std::array<std::string,2> actors{"ObserveA","ObserveB"};
   std::array<bool,2> live{false,false};
   for(unsigned i=0;i<2;++i){
      auto name=actors.at(i);
      assert(d.w.b.Register(name));
      d.w.b.endpoints[name+":7"]={{name}};
      d.w.app.callbacks[name+":7"]=[&,i](auto from,auto,auto,const auto& bytes){
         assert(from=="F"&&bytes=="s"&&!live[i]);
         // The source activates only on actual receipt of its named
         // schedule replacement, not on the proposal or a local retry.
         live[i]=true;
      };
   }
   if(defer)proposal={2,2};
   d.durable[Radio::D]["diagnostic"]=diag;
   const auto old=x.prepare();
   bool got=false;
   std::array<int,2> missing{};
   for(unsigned j=0;j<timeline.size();++j){
      x.lackingPose.clear();
      if(j%2==0){
         const int phase=j/2;
         for(unsigned i=0;i<2;++i)if(proposal[i]==phase){
            const auto t=timeline[j];
            now=t/1e6;
            d.w.b.incomingMsgs.push_back({"F",actors[i],"s"});
            d.w.b.DispatchMessages();
            assert(live[i]&&d.w.b.incomingMsgs.empty());
         }
      }else{
         const bool last=j==3;
         for(unsigned i=0;i<2;++i){
            // Old operation makes the FIRST cut unavailable; changed
            // operation makes the SECOND unavailable when current.
            const bool unavailable=last?live[i]:!live[i];
            if(unavailable)x.lackingPose.insert(actors[i]);
            missing[last]+=unavailable;
         }
         if(!got)got=x.commit(old,timeline[j]);
         assert(d.w.b.incomingMsgs.empty());
      }
   }
   assert(live[0]&&live[1]);
   assert(got==(!missing[0]||!missing[1]));
   return {got,live,missing};
}
int main(){
   int cases=0,old=0,deferred=0,midFailure=0,mixedFailure=0;
   for(int a:{0,1,2})for(int b:{0,1,2}){
      const auto experienced=run({a,b},false);
      // Conservative comparison: unknown delivery times anywhere in
      // the declared support. Where authorized, keep both old schedules
      // through the two cuts instead of speculating on joint activation.
      const auto delayed=run({a,b},true);
      assert(delayed.old);
      assert(experienced.old==((a==0&&b==0)||(a==2&&b==2)));
      if(a==1&&b==1){assert(!experienced.old);++midFailure;}
      if((a==0&&b==2)||(a==2&&b==0)){assert(!experienced.old);++mixedFailure;}
      ++cases;old+=experienced.old;deferred+=delayed.old;
   }
   assert(cases==9&&old==2&&deferred==9&&midFailure==1&&mixedFailure==2);
   std::cout<<"qualified native activation pairs "<<cases<<" old audits "<<old
      <<" old audits under lawful delay "<<deferred<<" simultaneous mid-window failures "<<midFailure
      <<" split early-late failures "<<mixedFailure<<"\n";
}
