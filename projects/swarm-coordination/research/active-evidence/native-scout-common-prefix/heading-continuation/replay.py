"""Qualified heading cue from native local sensors; later lawful rule change control."""
import ast,json
from itertools import product
from pathlib import Path
import subprocess,sys

ROOT=Path(sys.argv[1])
sys.path.insert(0,str(ROOT))
import journal

def load_view():
    iso=journal.iso; src=ROOT/"native_source.py"
    f=iso.funcs(iso.read(src),["_get_default_obs"])
    d=dict(iso.__dict__,_LAYER_AGENTS=0,_LAYER_SHELFS=1,Direction=journal.n.Direction)
    exec(compile(ast.Module(body=f,type_ignores=[]),str(src),"exec"),d)
    return d["_get_default_obs"]

def main():
    n=journal.n; A=n.Action;D=n.Direction;iso=journal.iso
    view=load_view()
    with subprocess.Popen([str(Path(sys.argv[2]).resolve())],stdin=subprocess.PIPE,stdout=subprocess.PIPE,
                          text=True,bufsize=1) as radio:
      def ask(*a):
        radio.stdin.write(" ".join(map(str,a))+"\n");radio.stdin.flush()
        return radio.stdout.readline().strip()
      def run(where,program,drop,open_prefix,arm):
        g=iso.make(n,False);g.max_steps=1000
        scout,B=g.agents
        scout.x,scout.y,scout.dir=2,3,D.UP
        B.x,B.y,B.dir=2,4,D.UP
        H=n.Agent(where,1,D.UP,0)
        side=n.Agent(0,4,D.UP,0)
        g.agents.extend((H,side));g.n_agents=len(g.agents)
        opt=n.Shelf(2,3);g.shelfs.append(opt)
        g.sensor_range=1;g.fast_obs=False;g.normalised_coordinates=False;g._obs_sensor_locations=9
        g._recalc_grid()
        def step(actor,act):
            a=[A.NOOP.value]*len(g.agents);a[g.agents.index(actor)]=act.value
            n.step(g,a)
        def read():
            xs=view(g,scout)["sensors"]
            return tuple(tuple((bool(xs[i]["has_agent"][0]),xs[i]["direction"])) for i in (0,2))
        # Mandatory local side work; independent owner and data route.
        assert ask("reset",5)=="ok"
        before=read()
        assert sum(x[0] for x in before)==0
        step(scout,A.FORWARD) # replaces the real native optional pickup act
        assert (scout.x,scout.y)==(2,2) and scout.carrying_shelf is None
        first=read(); assert sum(x[0] for x in first)==1
        # This turn is an observable primitive. Forward motion is a
        # separate authorized suffix, not implied by a direction field.
        if program!="stay":
            step(H,A.RIGHT if where==1 else A.LEFT)
        after=read()
        present=0 if after[0][0] else 1
        committed=after[present][1] != D.UP.value
        block=present if arm=="position" or not committed else 1-present
        payload="R1!" if block==0 else "L1!"
        assert ask("side",2)=="1"; step(side,A.FORWARD); assert side.y==3
        if open_prefix:
            assert not view(g,B)["sensors"][1]["has_agent"][0]
            step(B,A.FORWARD);assert B.y==3
        # Native scheduling t3 can use an early cue without the prefix;
        # the later cue is installed only after the common forward.
        arrival=4 if open_prefix else 3
        dispatch=arm!="safe" and (arm!="scope-uncertain" or not committed)
        got="-";debit=0
        if dispatch:
            got,x=ask("send",arrival,"Q","proof",payload,int(not drop)).split();debit=int(x)
        assert debit==3*dispatch
        branch=got[0] if got!="-" else None
        if branch:
            step(B,A.LEFT if branch=="L" else A.RIGHT)
            step(B,A.FORWARD)
            step(B,A.RIGHT if branch=="L" else A.LEFT)
        # Old movement uses native actuation, and proper completion is the
        # actual arrival at the other bay. It is not prevented by probing.
        if program=="cross":
            step(H,A.FORWARD);step(H,A.FORWARD)
            assert (H.x,H.y)==(4-where,1)
        else: assert (H.x,H.y)==(where,1)
        if branch:
            for _ in range(2 if open_prefix else 3):step(B,A.FORWARD)
        rescue=B.y==1
        assert rescue == bool(branch and B.x!=H.x)
        expected=(dispatch and not drop and
                    ((program!="cross") if arm=="position" else (program!="withdraw")))
        assert rescue==expected
        assert len({(x.x,x.y) for x in g.agents})==len(g.agents)
        return dict(before=before,position=tuple(x[0] for x in after),observed=after,notice=got,
            final_block=H.x,authorized_terminal=(H.x==4-where if program=="cross" else H.x==where),rescue=rescue,debit=debit,new_goal=[B.x,B.y])
      rows=[]
      # stable-heading is deliberately run outside its stable support too
      # as a diagnostic counterfactual; scope-uncertain is the safe arm.
      for case in product((1,3),("stay","cross","withdraw"),(False,True),(False,True),
                         ("position","stable-heading","scope-uncertain","safe")):
          rows.append([*case,run(*case)])
      for w in (1,3):
          a=[x[-1] for x in rows if x[0:1]==[w] and x[1] in ("cross","withdraw")]
          assert all(x["observed"]==a[0]["observed"] for x in a)
          assert len({x["final_block"] for x in a})==2
      stats={}
      for arm in ("position","stable-heading","scope-uncertain","safe"):
          sub=[r[-1] for r in rows if r[-2]==arm]
          stats[arm]=[len(sub),sum(x["rescue"] for x in sub),sum(x["authorized_terminal"] for x in sub)]
      assert stats["position"]==stats["stable-heading"]==[24,8,24]
      # Same aggregate; scope-qualified distinction: all four stable
      # placement/prefix combinations per program are rescued if open.
      good=[r for r in rows if r[1] in ("stay","cross") and not r[2] and r[4]=="stable-heading"]
      assert len(good)==8 and all(r[-1]["rescue"] for r in good)
      radio.stdin.close();assert radio.wait()==0
    print(json.dumps(dict(stats=stats,witness=[r for r in rows if r[0]==1 and not r[2] and r[3] and r[4]=="stable-heading"]),
                     sort_keys=True,indent=2))
if __name__=="__main__":main()
