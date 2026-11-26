"""Barrier-sampled native bay occupancy, not verification between steps."""
import sys
from hashlib import sha1
from pathlib import Path
path=Path(sys.argv.pop(2))/'native.py'
raw=path.read_bytes()
assert sha1(f"blob {len(raw)}\0".encode()+raw).hexdigest()=="9d0e3c4191a064c37a3d5d04ba5619f58a70617d"
sys.path.insert(0,str(path.parent))
source=raw.decode()
sampler="""    material_tape=[]
    def barrier():
        material_tape.append(tuple(int(any(at(j)==b for j in range(len(agents)))
                               or int(w.grid[1,b[1],b[0]]) != 0) for b in BAY))
    barrier()
"""
patch={
  "    candidate_phase=None":sampler+"    candidate_phase=None",
  "        r=step(commands)":"        r=step(commands)\n        barrier()",
  "    return dict(side=side":"    barrier()\n    return dict(cells=material_tape,side=side",
  "    assert step({follower:F})==(0,)*7":"    assert step({follower:F})==(0,)*7\n    barrier()",
}
for a,b in patch.items():
    assert source.count(a)==(2 if a=="    assert step({follower:F})==(0,)*7" else 1)
    source=source.replace(a,b)
exec(compile(source,str(path),'exec'),{'__name__':'__main__'})
