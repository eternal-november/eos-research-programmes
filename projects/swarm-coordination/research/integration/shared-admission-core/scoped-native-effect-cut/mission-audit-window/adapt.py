from pathlib import Path
import adapt_base

p=Path("mission.cpp")
s=p.read_text()
a=''' for(unsigned i=0;i<2;++i) if(fits(auditCut[i]))w|=1<<i;
 assert(w==3);'''
b=''' // An admitted old audit still occupies its byte at the new primary cut.
 const bool keepsPrimary=live(r.w.state("R").bytes_sent,secs(auditCut[1]))+1+5<=cap;
 for(unsigned i=0;i<2;++i) if(fits(auditCut[i])&&keepsPrimary)w|=1<<i;
 assert(w==3);'''
assert s.count(a)==1
s=s.replace(a,b)
a='''    const auto qualified=cut::check({cut::Act::effect,true,true,fits(auditCut[i]),!deadA&&!deadB});
    if(qualified!=cut::enable)continue;
    // Readiness was established in the fixture's serialized current cut,
    // and the actual native callback agrees. No fabricated queue wake.
    r.w.b.pose_update_f=[&](auto name){
       if((deadA&&name==added[0])||(deadB&&name==added[1]))return std::make_tuple(false,Pose{},now);
       return normal_pose(name);
    };
    aux1=r.route("R","Audit",one(0),secs(auditCut[i]));
    r.w.b.pose_update_f=normal_pose;
    assert(aux1==one(0));used=1+i;'''
b='''    // The caller only consumes CURRENT pose source replies. The
    // injected schedule controls the source, never the admission output.
    r.w.b.pose_update_f=[&](auto name){
       if((deadA&&name==added[0])||(deadB&&name==added[1]))return std::make_tuple(false,Pose{},now);
       return normal_pose(name);
    };
    now=secs(auditCut[i]);
    bool ready=true;
    for(const auto& [name,node]:*r.w.b.team)
       ready &= std::get<0>(r.w.b.pose_update_f(node->name));
    assert(ready==(!deadA&&!deadB)&&r.w.b.incomingMsgs.empty());
    const auto qualified=cut::check({cut::Act::effect,true,true,
        bool(w&(1u<<i))&&fits(auditCut[i]),ready});
    if(qualified==cut::enable){
       aux1=r.route("R","Audit",one(0),secs(auditCut[i]));
       assert(aux1==one(0));used=1+i;
    }
    r.w.b.pose_update_f=normal_pose;'''
assert s.count(a)==1
p.write_text(s.replace(a,b))
p=Path("bridge.py")
s=p.read_text()
a='''        for pair,(s1,s2,miss1,miss2) in enumerate(((1,1,1,1),(1,2,1,2),(3,3,0,0))):
            part=[trace(binary,sites,w,miss,3,6,dc,'checked',"clearance",gc,0,"resource-scoped",
                     (policy,s1,s2,miss1,miss2))
                   for w,miss,dc,gc in product(range(2),range(3),("before","after"),("before","after"))]
            expected=(pair!=1 or policy!=3)'''
b='''        calendars=((s1,s2,a,b) for s1,s2 in ((1,1),(1,2),(3,3)) for a,b in product((0,1,2),repeat=2)
                   if not(a&~s1 or b&~s2))
        for s1,s2,miss1,miss2 in calendars:
            # Fix the already-verified survey at both physical beam sources.
            # Cross every declared later pose mask with both geometries and
            # both sides of the actual gate and dock crash cuts.
            part=[trace(binary,sites,w,2,3,6,dc,'checked',"clearance",gc,0,"resource-scoped",
                     (policy,s1,s2,miss1,miss2))
                   for w,dc,gc in product(range(2),("before","after"),("before","after"))]
            expected=(policy!=3 or (miss1|miss2)!=3)'''
assert s.count(a)==1
s=s.replace(a,b)
s=s.replace('summary[1]["independent_early"]-summary[0]["independent_early"]==24','summary[1]["independent_early"]-summary[0]["independent_early"]==32').replace('summary[3]["old_audits"]==48','summary[3]["old_audits"]==112')
p.write_text(s)
