#include <cassert>
#include <iostream>
#include <limits>
#include <string>
#include <vector>
#include <map>

struct SUMOVehicle {
    int id;
    double speed=0, wait=0;
    double getSpeed() const { return speed; }
    double getWaitingTime() const { return wait; }
    int getNumericalID() const { return id; }
};
struct MSTrafficLightLogic { virtual ~MSTrafficLightLogic()=default; };
struct MSLink {
    struct ApproachingVehicleInformation {
        double arrivalSpeedBraking=1, arrivalTime=10, dist=0;
    };
    std::map<const SUMOVehicle*,ApproachingVehicleInformation> approaching;
    auto const& getApproaching() const { return approaching; }
    std::pair<const SUMOVehicle* const,const ApproachingVehicleInformation> getClosest() const;
    MSTrafficLightLogic* owner;
    const MSTrafficLightLogic* getTLLogic() const { return owner; }
    int getTLIndex() const { return 0; }
};
using Approaching=std::pair<const SUMOVehicle* const,const MSLink::ApproachingVehicleInformation>;
using MSEdgeVector=std::vector<int>;
struct MSDriveWay {
    bool occupiedFlag=false, isConflict=true;
    std::vector<MSLink*> myConflictLinks;
    const SUMOVehicle* myActive=nullptr;
    bool foeDriveWayOccupied(bool,const SUMOVehicle*,MSEdgeVector&) const {return occupiedFlag;}
    bool overlap(const MSDriveWay& d) const {return d.isConflict;}
    bool isFoeOrSubFoe(const MSDriveWay*) const {return true;}
    std::pair<bool,int> canUseSiding(const SUMOVehicle*,const MSDriveWay*) const {return {false,0};}
    std::string getID() const {return "authored-driveway";}
    void conflictLaneOccupied() const { assert(false); }
    void foeDriveWayApproached() const { assert(false); }
    bool reserve(const Approaching&,MSEdgeVector&);
    bool hasLinkConflict(const Approaching&,const MSLink*) const;
    static bool mustYield(const Approaching&,const Approaching&);
};
struct MSRailSignal: MSTrafficLightLogic {
    struct LinkInfo {
        MSLink* myLink;
        std::vector<MSDriveWay*> myDriveways;
        MSDriveWay& getDriveWay(const SUMOVehicle*) {return *myDriveways.at(0);}
    };
    std::vector<LinkInfo> myLinkInfos;
    static inline std::vector<const SUMOVehicle*> myBlockingVehicles,myRivalVehicles,myPriorityVehicles;
    static inline std::vector<int> myBlockingDriveWays;
    static inline std::string myConstraintInfo,myRequestedDriveWay;
    static inline bool myStoreVehicles;
    static bool storeVehicles() { return myStoreVehicles; }
    static auto& rivalVehicles() { return myRivalVehicles; }
    static auto& priorityVehicles() { return myPriorityVehicles; }
    void resetStored();
    void storeTraCIVehicles(const MSDriveWay*);
    void storeTraCIVehicles(int);
    bool constraintsAllow(const SUMOVehicle*) { return true; }
    const MSDriveWay& retrieveDriveWayForVeh(int i,const SUMOVehicle* v) {return myLinkInfos[i].getDriveWay(v);}
};
#include "native.inc"
using std::vector;
using std::string;
vector<int> ids(const vector<const SUMOVehicle*>& a) {
    vector<int> s;for(auto v:a)s.push_back(v->id);return s;
}
struct Outcome {
    bool pass;
    vector<int> rivals, priority;
};
struct Fixture {
    SUMOVehicle E{10},P{1},Q{2},N{15};
    MSRailSignal se,sa,sb;
    MSLink le,la,lb;
    MSDriveWay de,da,db;
    Fixture() {
        le.owner=&se;la.owner=&sa;lb.owner=&sb;
        se.myLinkInfos.push_back({&le,{&de}});
        sa.myLinkInfos.push_back({&la,{&da}});
        sb.myLinkInfos.push_back({&lb,{&db}});
        le.approaching[&E]={1,10,0};
        de.myConflictLinks={&la,&lb};
    }
    Outcome run() {
        // Separately run the uninstrumented native decision first.
        MSEdgeVector x;
        bool pass=de.reserve(le.getClosest(),x);
        de.myActive=nullptr;
        se.storeTraCIVehicles(0);
        assert((de.myActive!=nullptr)==pass);
        return {pass,ids(se.myRivalVehicles),ids(se.myPriorityVehicles)};
    }
};
int main() {
    Fixture f;
    f.la.approaching[&f.P]={1,10,0};
    auto first=f.run();
    f.lb.approaching[&f.Q]={1,10,0};
    auto both=f.run();
    assert(!first.pass && !both.pass && first.rivals==both.rivals &&
           first.priority==both.priority && both.rivals==vector<int>{1});
    f.la.approaching.clear();
    auto q=f.run();
    assert(!q.pass && q.rivals==vector<int>{2});
    f.lb.approaching.clear();
    auto none=f.run();
    assert(none.pass && none.rivals.empty());
    f.la.approaching[&f.N]={1,10,1}; // farther than ego at equal brake speed and arrival
    f.la.approaching[&f.P]={1,10,2};
    // P has later arrival distance than ego, so must outrank on a prior key.
    f.la.approaching[&f.P].arrivalSpeedBraking=2;
    auto ok=f.run();
    assert(ok.pass && ok.rivals==vector<int>{15} && ok.priority.empty());
    f.la.approaching.erase(&f.N);
    auto promotion=f.run();
    assert(!promotion.pass && promotion.priority==vector<int>{1});
    f.de.occupiedFlag=true;
    auto occ=f.run();
    assert(!occ.pass && occ.rivals.empty() && occ.priority.empty());
    std::cout<<"same prefix P; hidden Q survives deletion; deletion promotes a previously hidden blocker; empty report can block\n";
}
