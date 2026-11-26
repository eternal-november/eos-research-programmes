"""Patch only the pinned fixture to construct physical old-authority events."""
from hashlib import sha1
from pathlib import Path
import sys

def adapt(source_dir):
    path=source_dir/'native.py'
    sys.path.insert(0,str(source_dir))
    for name,sha in [('native.py','dcba6da00966bb61d72134662947d429ea1a6c35'),
                     ('release.py','2b3da4f85d129bf1c31cd9d3594c537d5ec5c654')]:
        data=(source_dir/name).read_bytes()
        assert sha1(f"blob {len(data)}\0".encode()+data).hexdigest()==sha
    src=path.read_text()
    def replace(old,new):
        nonlocal src
        assert src.count(old)==1,(old,src.count(old))
        src=src.replace(old,new)
    replace("from release import lawful","from release import lawful\nfrom lineage import Permutation,carry")
    replace("read=(True,True)):", "read=(True,True),events=(),omitted=None):")
    replace("    pad(45)\n","""    pad(45)
    def physical():
        return tuple(int(env.grid[1,y,x]) for x,y in BAY)
    archive=physical()
    effects=[]
    def take(i,s):
        assert step({i:T})==(0,)*7
        assert agents[i].carrying_shelf is shelves[s]
    def drop(i):
        assert step({i:T})==(0,)*7
        assert agents[i].carrying_shelf is None
    for generation,swap in enumerate(events):
        before=physical()
        yx=YROW[before.index(shelves[0].id)]
        yy=YROW[before.index(shelves[1].id)]
        move(0,via_y(0,3,yx)+[(1,yx),(2,yx),(3,yx)])
        take(0,0)
        move(0,[(2,yx),(1,yx), (1,3)])
        drop(0)
        if swap:
            move(1,[(3,yy)])
            take(1,1)
            move(1,[(3,3),(3,yx)])
            drop(1)
            move(1,[(3,3)])
            rot(1,E)
        take(0,0)
        target=yy if swap else yx
        move(0,[(2,3),(2,target),(3,target)])
        drop(0)
        move(0,[(x,target) for x in (2,1,0)]+via_y(0,target,3))
        rot(0,E)
        after=physical()
        assert after==(before[::-1] if swap else before)
        # Only after the real re-seat/exchange and carrier clearance.
        assert (at(0),at(1))==((0,3),(3,3))
        assert all(a.carrying_shelf is None for a in agents[:2])
        effects.append(Permutation(generation,generation+1,after!=before))
    pad(148)
""")
    replace("    assert bay_cargo[permutation]==shelves[0].id and bay_cargo[1-permutation]==shelves[1].id",
            "    assert set(bay_cargo)=={shelves[0].id,shelves[1].id}")
    replace("    assert protected==BAY[1-permutation]",
            "    assert protected==BAY[bay_cargo.index(shelves[1].id)]")
    replace("    permit={shelves[0].id}", """    permit={shelves[0].id}
    retained=[r for j,r in enumerate(effects) if j!=omitted]
    if policy=='lineage':report=carry(0,archive,len(effects),retained)
    elif policy=='unchanged-version':report=archive if not effects else None
    elif policy=='stale-audit':report=archive
    else:report=tuple(bay_cargo)
    proposed=[]""")
    replace("        possible=(int(env.grid[1,y,x]),) if read[j] else tuple(s.id for s in shelves[:2])",
            """        possible=(report[j],) if report is not None and read[j] else tuple(s.id for s in shelves[:2])""")
    replace("        assert enabled==reference",
            """        if policy=='local':assert enabled==reference
        if enabled:proposed.append(j)""")
    replace("        if policy=='local' and enabled:elected.append(j)",
            """        if policy in ('local','lineage','unchanged-version') and enabled:elected.append(j)""")
    replace("    if policy=='local':assert elected==direct",
            """    if policy=='local':assert elected==direct
    if policy=='lineage' and omitted is None:assert elected==direct""")
    replace("stored_footprint=[(s.x,s.y) for s in shelves[:2]])",
            """stored_footprint=[(s.x,s.y) for s in shelves[:2]], proposed=proposed,
                    inappropriate_proposal=any(bay_cargo[j] not in permit for j in proposed),
                    declared_events=[e.reverse for e in effects], omitted=omitted)""")
    ns={'__name__':'inherited_fixture'}
    exec(compile(src,str(path),'exec'),ns)
    return ns['run']
