"""Instrument the pinned #588 producer with an actual hosted idle command."""
import sys
from hashlib import sha1
from pathlib import Path

path=Path(sys.argv[2])/'native.py'
src=path.read_bytes()
assert sha1(f"blob {len(src)}\0".encode()+src).hexdigest()=="9d0e3c4191a064c37a3d5d04ba5619f58a70617d"
src=src.decode()
sys.path.insert(0,str(path.parent))
mode=int(sys.argv.pop(5))
# #588 positional args are upstream, named, flight.
sys.argv.pop(2)
clock="""    physical_idle=0
    physical_relocation=None
    cut12=None
"""
idle="""        if tick==10 and host_idle:
            before=tuple((seen(i),agents[i].dir) for i in range(len(agents)))
            assert step({})==(0,)*7
            assert before==tuple((seen(i),agents[i].dir) for i in range(len(agents)))
            physical_idle+=1
"""
pairs={
    "    while gate.tape or ac is not None:":clock+"    while gate.tape or ac is not None:\n"+idle.rstrip(),
    "    assert source_done is not None and independent and verified_release":
        "        if tick+physical_idle==12:\n            cut12=verified_release\n"
        "    assert cut12 is not None\n    assert source_done is not None and independent and verified_release",
    "                new_done=tick":"                new_done=tick\n                physical_relocation=tick+physical_idle",
    "                actual_due_paid=True,independent_paid=True,events=events,":"                actual_due_paid=True,independent_paid=True,events=events,\n                host_idle=physical_idle,physical_relocation=physical_relocation,cut12=cut12,"
}
for a,b in pairs.items():
    assert src.count(a)==1
    src=src.replace(a,b)
exec(compile(src,str(path),'exec'),{'__name__':'__main__','host_idle':mode})
