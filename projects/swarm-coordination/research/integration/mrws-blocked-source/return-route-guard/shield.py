"""Execute a shared return-route restriction on the pinned notice experiment."""
from pathlib import Path
from hashlib import sha256
import json,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'notice-timing'))
import with_notices

def shielded_base(source):
    old='        r.set_movement_path(w.compute_robot_astar_path(r))'
    assert source.count(old)==1
    patch='''        from mrws.engine.pathfinding import compute_astar_path
        if type(r.get_target()) is RobotHome:
            # At the sampled cut do not add new occupation of a source for owed
            # work. Current position need not itself satisfy the admission rule.
            goal=s._order_goal_assignment.get(0)
            delivered=w._order_stations[goal].report_inventory_item_names() if goal else []
            if not s.are_all_orders_complete():
                rest=set(EXPECTED[len(delivered):])
                forbid={h.get_position() for h in w._shelves.values() if h.get_item().get_name() in rest}
            else:forbid=set()
            r.set_movement_path(compute_astar_path(w._width,w._height,w._position_to_robot,
                r.get_position(),r.get_target().get_position(),blocked_cells=w._wall_cells|forbid))
        else:
            r.set_movement_path(w.compute_robot_astar_path(r))'''
    source=source.replace(old,patch)
    step='                w.move_robot_next_path_spot(r);moves[k]+=1'
    tap=step+"\n                if type(r.get_target()) is RobotHome:events.append((k[0],{'command':'HOMEAUDIT','objName':k[1],'posX':nx,'posY':ny}))"
    assert source.count(step)==1
    return source.replace(step,tap)

def main():
    base=Path(sys.argv[1]); old=json.loads(Path(sys.argv[2]).read_text())
    out=Path(sys.argv[3])
    sc=out.parent/'shielded-source.py'
    sc.write_text(shielded_base(base.read_text()))
    rows=with_notices.verify(sc)
    k=lambda x:(x['arm'],x['lag'],tuple(x['notice_delays']))
    assert [k(r) for r in rows]==[k(r) for r in old]
    import collections
    for a,b in ((a,b) for a in ('discard','retain') for b in (None,1,4)):
        print(a,b,collections.Counter((r['finish'],r0['finish']) for r,r0 in zip(rows,old) if (r['arm'],r['lag'])==(a,b)))
    out.write_text(json.dumps(rows,sort_keys=True,separators=(',',':'))+'\n')
if __name__=='__main__':main()
