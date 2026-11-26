"""Exact finite decision tree and independent typed-packet ledger comparator."""
from collections import defaultdict
from itertools import product

# Worlds: primary/fallback live at measurement, primary/fallback live at due,
# plus measurement-only drops. All values are physical/source variables.
P=(1,0,1,0,0,0)
F=(0,1,0,1,0,0)
PE=(1,0,1,0,1,0)
FE=(0,1,0,1,0,1)
B=(1,1,1,1,0,0)
BE=(1,1,1,1,1,0)
DRIFT=(1,0,0,1,0,0)
DARK=(0,0,0,0,0,0)
CASES={
 'stable':(P,F),
 'one_sided_erasure':(P,PE,F),
 'both_up_admitted':(P,PE,F,B,BE),
 'two_silent_branches':(PE,F,FE),
 'drift':(P,DRIFT),
 'both_routes_can_fail':(P,F,DARK),
}
WORLDS=tuple(sorted(set(w for gs in CASES.values() for w in gs)))
ACTS=tuple(product((0,1),repeat=4))

def direct(params,w,acts):
    c,pbytes,fbytes,late=params
    pp,fp,pd,fd,pe,fe=w
    useP,useF,hold,rebind=acts
    tx=defaultdict(int);rx=defaultdict(int)
    def attempt(s,r,b,path=True):
        if tx[s]+b>c:return 0
        tx[s]+=b
        if not path or rx[r]+b>c:return 0
        rx[r]+=b
        return 1
    # All checked times are separated from time 0 by strictly less than one.
    old0=attempt('P','Base',2)
    independent=attempt('R','D',1)
    u=attempt('Q','Second',pbytes,pp and not pe) if useP else -1
    pending=not hold
    optional=0
    if useF and late and pending:
        optional=attempt('P','Base',c-2)
        pending=False
    v=attempt('P','Base',fbytes,fp and not fe) if useF else -1
    change=bool(rebind and tx['P']+2<=c and rx['Base']+2<=c)
    if change:pending=False
    if pending:optional=attempt('P','Base',c-2)
    oldtail=attempt('P' if change else 'Q','Base' if change else 'Second',2,fd if change else pd)
    return (u,v,oldtail,optional,int(change),old0,independent)

def partition(ws,key):
    groups=defaultdict(list)
    for w in ws:groups[key(w)].append(w)
    return groups

def exact(table,worlds):
    """Max optional sum among robust mandatory policies, or None."""
    first=[]
    for useP in (0,1):
        uGroups=partition(worlds,lambda w:table[w,(useP,0,0,0)][0])
        answers={}
        for u,group in uGroups.items():
            scans=[]
            for useF,hold in product((0,1),repeat=2):
                vGroups=partition(group,lambda w:table[w,(useP,useF,hold,0)][1])
                sub={}
                for v,cohort in vGroups.items():
                    opt=[]
                    for change in (0,1):
                        rows=[table[w,(useP,useF,hold,change)] for w in cohort]
                        if all(row[2] for row in rows):
                            opt.append((sum(row[3] for row in rows),change))
                    if not opt:break
                    sub[v]=max(opt)
                if len(sub)==len(vGroups):
                    scans.append((sum(q[0] for q in sub.values()),
                                  (useF,hold,{v:a[1] for v,a in sub.items()})))
            if not scans:break
            answers[u]=max(scans,key=lambda x:x[0])
        if len(answers)==len(uGroups):
            first.append((sum(q[0] for q in answers.values()),
                          (useP,{u:val[1] for u,val in answers.items()})))
    return max(first,key=lambda q:q[0]) if first else None


def feasible_at_same_info(table,worlds):
    # Separate direct synthesis: enumerate all allowed action assignments
    # to the observed prefix and check if any preserves mandatory service.
    for useP in (0,1):
        uGroups=partition(worlds,lambda w:table[w,(useP,0,0,0)][0])
        good=True
        for _,group in uGroups.items():
            uGood=False
            for useF,hold in product((0,1),repeat=2):
                vGroups=partition(group,lambda w:table[w,(useP,useF,hold,0)][1])
                if all(any(all(table[w,(useP,useF,hold,change)][2]
                                  for w in cohort) for change in (0,1))
                       for cohort in vGroups.values()):
                    uGood=True;break
            good &= uGood
        if good:return True
    return False

def execute(table,tree,w):
    p,branches=tree
    u=table[w,(p,0,0,0)][0]
    f,h,next_by_view=branches[u]
    v=table[w,(p,f,h,0)][1]
    a=(p,f,h,next_by_view[v])
    return table[w,a],a
