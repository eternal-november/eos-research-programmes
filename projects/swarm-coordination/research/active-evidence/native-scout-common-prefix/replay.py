"""Move to acquire an actual RWARE crop, then use the selected SubT radio."""
import ast,json
from collections import deque
from itertools import product
from pathlib import Path
import subprocess,sys

ROOT=Path(sys.argv[1])
sys.path.insert(0,str(ROOT))
import journal

def extract():
    iso=journal.iso;source=ROOT/"native_source.py"
    tree=iso.read(source)
    image=[x for x in tree.body if isinstance(x,ast.ClassDef) and x.name=="ImageLayer"][0]
    obs=iso.funcs(tree,["_make_img_obs"])
    n=journal.n
    env=dict(iso.__dict__,_LAYER_AGENTS=0,_LAYER_SHELFS=1,Direction=n.Direction)
    exec(compile(ast.Module(body=[image]+obs,type_ignores=[]),str(source),"exec"),env)
    return env["ImageLayer"],env["_make_img_obs"]

def common_prefix_law():
    # On-plan geometry after a successful scan. Unit actions, separate
    # branch environment after evidence. The scheduled image study does
    # not grant unrestricted motion; this is a separate model comparison.
    start=(2,4,0); last=6 # six unit action slots t3..t8
    def one(s,forbidden):
        x,y,d=s
        dx,dy=((0,-1),(1,0),(0,1),(-1,0))[d]
        v={(x,y,d),(x,y,(d+1)%4),(x,y,(d-1)%4)}
        q=x+dx,y+dy
        if all(0<=i<5 for i in q) and q not in forbidden:v.add((*q,d))
        return v
    def feasible(center_open,unknown_slots):
        fixed={(2,2),(0,3)}
        if not center_open:fixed.add((2,3))
        goals=[(3,1),(1,1)]
        blocks=[(1,1),(3,1)]
        shared={start}
        for _ in range(unknown_slots):
            shared={n for s in shared for n in one(s,fixed|set(blocks))}
        def local(s,b,target):
            arena={s}
            for _ in range(last-unknown_slots):
                arena={n for p in arena for n in one(p,fixed|{b})}
            return any(p[:2]==target for p in arena)
        return any(all(local(s,b,g) for b,g in zip(blocks,goals)) for s in shared)
    cuts=[[feasible(use,t) for t in range(last+1)] for use in (False,True)]
    assert cuts==[[True,False,False,False,False,False,False],
                  [True,True,False,False,False,False,False]],cuts
    return cuts

def main():
    geometry=common_prefix_law()
    n=journal.n; iso=journal.iso
    A=n.Action; D=n.Direction
    img,make_view=extract()
    with subprocess.Popen([str(Path(sys.argv[2]).resolve())],stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,text=True,bufsize=1) as radio:
      def ask(*v):
        radio.stdin.write(" ".join(map(str,v))+"\n");radio.stdin.flush()
        return radio.stdout.readline().strip()
      def execute(hidden,blocked,erased,radio_kind,policy):
        g=iso.make(n,False);g.max_steps=1000
        scout,operator=g.agents
        scout.x,scout.y,scout.dir=2,3,D.UP
        operator.x,operator.y,operator.dir=2,4,D.UP
        stalled=n.Agent(hidden,1,D.UP,0)
        side=n.Agent(0,4,D.UP,0)
        g.agents.extend((stalled,side))
        if blocked:g.agents.append(n.Agent(2,2,D.UP,0))
        g.n_agents=len(g.agents)
        optional=n.Shelf(2,3);g.shelfs.append(optional)
        g.sensor_range=1;g.image_observation_layers=[img.AGENTS]
        g.image_observation_directional=False; g._recalc_grid()
        def initial_or_read(ag):
            make_view(g,scout) # stock layer generation for agent ID 1
            return make_view(g,ag)[0].copy()
        before=[initial_or_read(a).astype(int).tolist() for a in (scout,operator)]
        def move(actor,act):
            intents=[A.NOOP.value]*len(g.agents)
            intents[g.agents.index(actor)]=act.value
            n.step(g,intents)
        def obtain():
            if (scout.x,scout.y)!=(2,2) or erased:return None
            # The frame is the observer's own centered crop, no global
            # map or hidden direction is supplied to this decoder.
            local=initial_or_read(scout)
            L,R=local[0][0],local[0][2]
            assert L+R==1
            return "R1!" if L else "L1!"
        assert ask("reset",5)=="ok"
        if policy in ("active","private","late","late-flex"):
            move(scout,A.FORWARD)
        else:
            move(scout,A.TOGGLE_LOAD)
        pickup=scout.carrying_shelf is optional
        assert pickup==(policy in ("passive","blind-left"))
        sample=obtain()
        if policy in ("passive","blind-left"):assert sample is None
        a_attempt=(scout.x,scout.y)==(2,2)
        assert a_attempt==(policy in ("active","private","late","late-flex") and not blocked)
        early="-";delivered="-";spent=0
        if sample and policy=="active":
            delivered,charge=ask("send",2,"Q","proof",sample,int(radio_kind=="open")).split()
            spent=int(charge);early=delivered
        # This actor's mandatory job advances on the same timeline, it
        # neither consumes the scout action nor shares the receiver.
        assert ask("side",2)=="1"
        move(side,A.FORWARD)
        assert (side.x,side.y)==(0,3)
        branch=early[0] if early!="" and early!="-" else "L" if policy=="blind-left" else None
        if policy=="late-flex":
            # Independent local view of the shared prefix, not the
            # scout's hidden branch observation.
            if initial_or_read(operator)[0][1]==0:
                move(operator,A.FORWARD)
            assert (operator.x,operator.y)==(2,4 if not a_attempt else 3)
        if sample and policy in ("late","late-flex"):
            delivered,charge=ask("send",4,"Q","proof",sample,int(radio_kind=="open")).split()
            spent=int(charge)
            if policy=="late-flex" and delivered!="-":
                branch=delivered[0]
        if branch:
            move(operator,A.LEFT if branch=="L" else A.RIGHT)
            move(operator,A.FORWARD)
            move(operator,A.RIGHT if branch=="L" else A.LEFT)
            for _ in range(2 if policy=="late-flex" else 3):move(operator,A.FORWARD)
        reached=(operator.y==1)
        own=(branch=="L" and hidden==3) or (branch=="R" and hidden==1)
        assert reached==own
        real_can=not blocked and not erased
        assert (sample is not None)==(real_can and policy in ("active","private","late","late-flex"))
        expected=(
            policy in ("active","late-flex") and real_can and radio_kind=="open" or
            policy=="blind-left" and hidden==3)
        assert reached==expected
        assert spent==(3 if real_can and policy in ("active","late","late-flex") else 0)
        if policy=="late" and real_can and radio_kind=="open":
            assert delivered in ("L1!","R1!") and not reached
        assert len({(x.x,x.y) for x in g.agents})==len(g.agents)
        return dict(before=before,sample=sample,receipt=delivered,charge=spent,
                   branch=branch,operator=[operator.x,operator.y],goal=reached,
                   pickup=pickup,other_work=True)
      rows=[]
      for q in product((1,3),(False,True),(False,True),("open","lost"),
                       ("active","private","late","late-flex","passive","blind-left")):
          rows.append([*q,execute(*q)])
      stats={}
      for pol in ("active","private","late","late-flex","passive","blind-left"):
          xs=[r[-1] for r in rows if r[-2]==pol]
          stats[pol]=dict(runs=len(xs),goals=sum(x["goal"] for x in xs),
                          pickup=sum(x["pickup"] for x in xs),other=sum(x["other_work"] for x in xs))
      for b in (False,True):
          q=[e[-1]["before"] for e in rows if e[1]==b and e[-2]=="active"]
          assert all(i==q[0] for i in q)
      assert stats["active"]["goals"]==stats["late-flex"]["goals"]==2 and stats["blind-left"]["goals"]==8
      radio.stdin.close();assert radio.wait()==0
    print(json.dumps(dict(stats=stats,geometry=geometry,witness=[r for r in rows if r[1:4]==[False,False,"open"]]),
                     sort_keys=True,indent=2))
if __name__=="__main__":main()
