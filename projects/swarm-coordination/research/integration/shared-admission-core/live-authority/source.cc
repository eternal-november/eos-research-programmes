#define main prior_replay
#include "replay.cc"
#undef main

// A disjoint candidate route for participant 2; identical approach origin.
const std::vector<Writer::Checkpoint> southeast={
    at(0,-4), at(3,-4), at(6,-4)};

int main() {
    int phys,edit,change,request,receipt,commit;
    while(std::cin>>phys>>edit>>change>>request>>receipt>>commit) {
        Scenario s;
        s.fresh->set(1,*s.a.reservation_id(),Writer::Reservation{west,.25});
        s.fresh->ready(1,*s.a.reservation_id(),0);
        s.fresh->reached(1,*s.a.reservation_id(),1);
        s.w->moderator=s.fresh.get();
        auto b=make_participant(2,.25,s.w);
        b.set(south);
        b.ready(0);
        assert(end(*s.fresh,2)==0);
        auto d=make_participant(3,.25,s.w);
        d.set(distant);
        d.ready(0);
        assert(end(*s.fresh,3)==1);
        int site=0, capture_site=-1;
        ReservationId capture_id=0;
        bool marked=false;
        const auto initial=*b.reservation_id();
        for(int t=0;t<=20;++t) {
            if(t==4)s.a.ready(1);
            if(t==phys)s.a.reached(2);
            if(t==edit) {
                b.set(change?southeast:south);
                site=change;
                auto id=*b.reservation_id();
                assert(id!=initial);
            }
            // Relay ordinary late readiness for the previous reservation;
            // do not fabricate a new authority from successful message delivery.
            if(t==receipt)s.fresh->ready(2,initial,0);
            if(t==request)b.ready(0);
            if(t==12&&commit) {
                // This controlled gate reads locally in the same ordered
                // process. It is not a fast promise sent on a wireless link.
                if(end(*s.fresh,2)>=1 && (site||s.a.last_reached()>=2)){
                    capture_site=site;
                    capture_id=*b.reservation_id();
                }
            }
            if(t==13) {
                d.reached(1);
                if(capture_id && *b.reservation_id()==capture_id &&
                   end(*s.fresh,2)>=1 && (capture_site||s.a.last_reached()>=2)){
                    b.reached(1);
                    marked=s.fresh->statuses().at(2).last_reached==1;
                }
            }
            const auto bst=s.fresh->statuses().at(2);
            assert(bst.reservation==*b.reservation_id());
            assert(!bst.critical_error);
            std::cout<<t<<' '<<site<<' '<<unsigned(bst.reservation!=initial)<<' '
                     <<end(*s.fresh,2)<<' '<<s.fresh->statuses().at(1).last_reached<<' '
                     <<end(*s.fresh,3)<<' '<<s.fresh->statuses().at(3).last_reached
                     <<'\n';
        }
        if(commit) std::cout<<capture_site<<' '<<marked<<' '<<s.fresh->statuses().at(3).last_reached<<'\n';
    }
}
