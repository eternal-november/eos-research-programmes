"""Exact #680 downstream policy with a selected VDA observation adapter."""
from pathlib import Path
import sys
p=Path(sys.argv[1])
t=(p/"prior.py").read_text()
def swap(a,b):
    global t
    assert t.count(a)==1,a
    t=t.replace(a,b)
swap("def run(loc,stage,drop,backup,cap,arm):", """def run(loc,race,stitched,observation,drop,backup,cap,arm):
        src=subprocess.run([sys.argv[3]],input=f"{race} {stitched}\\n",text=True,
                           capture_output=True,check=True).stdout.strip().split()
        name,ver,anchor,edge,n_edges=src
        assert name=="cell-issue:7" and n_edges=="0"
        assert (ver,anchor,edge)==(("2","A","AX") if not race else
                                   ("3","B","BX") if stitched else ("1","A","AB"))
        # VDA selected receiver state determines whether the old right
        # still exists. RWARE/SQLite remains the authored physical bridge.
        actual_old=ver!="2"
        stage="durable" if actual_old else "rolled"
        # The durable issuer map makes (order incarnation, version) unique.
        # Neither VDA State nor the receive seam supplies this provenance.
        advertised=(name,int(ver),7) if observation in ("fresh","origin-open") else (
                    (name,int(ver),6) if observation=="old-incarnation" else
                    (name,0,7) if observation=="requested-only" else None)
        qualified=observation!="origin-open" and advertised==(name,2,7)""")
swap('announce=arm=="eager" or (arm=="guard" and payload=="n7!")',
     'announce=(qualified and payload=="n7!" and arm in ("guard","eager")) or (arm=="eager" and observation=="fresh" and old)')
swap("assert (entry,success)==compare(old,drop,backup,cap,arm),(",
     """usable=observation=="fresh"
        allow=usable and (not old or arm=="eager")
        once=allow and (not drop or backup) and arm!="safe-wait"
        expected=(6,True) if once and not old else (11 if once and cap<6 else 9,True)
        assert (entry,success)==expected,(""")
swap("return dict(public=public,early=known,entry=entry,old_paid=success,old_position=old_position,side_tick=5,wire=transmissions)",
     "return dict(public=public,observation=advertised,ver=ver,early=known,entry=entry,old_paid=success,old_position=old_position,side_tick=5,wire=transmissions)")
swap('for case in product(("rolled","durable"),(False,True),(False,True),(5,6),\n                          ("guard","eager","safe-wait","occupancy-only")):',
     'for case in product((0,1),(0,1),("fresh","lost","old-incarnation","requested-only","origin-open"),(False,True),(False,True),(5,6),\n                          ("guard","eager","safe-wait")):')
swap('for arm in ("guard","eager","safe-wait","occupancy-only"):', 'for arm in ("guard","eager","safe-wait"):')
swap('if r[4]==arm','if r[6]==arm')
swap('assert arms["guard"]==dict(n=16,old_paid=16,by9=16,early=6)',
     'assert arms["guard"]==dict(n=160,old_paid=160,by9=160,early=12)')
swap('[r for r in rows if r[1:4]==[True,True,5]]',
     '[r for r in rows if r[1:7]==[1,"fresh",True,True,5,"guard"] or r[0:7]==[0,0,"origin-open",True,True,5,"guard"]]')
# Save exact applied transformation, not a silent rewrite.
Path(sys.argv[2]).write_text(t)
