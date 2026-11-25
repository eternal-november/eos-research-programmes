"""One narrow amendment to the verified generated-blockage replay."""
from pathlib import Path
import sys
from unittest.mock import patch
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P.parent if not (P/'pilot.py').exists() else P))
import pilot

summary=pilot.summary
def sources(reuse=False):
    if not reuse:return pilot.sources()
    orig=pilot.shield.shielded_base
    def amended(raw):
        s=orig(raw)
        old="            if i in kept:\n                a,inv=kept[i];segments.append((a,inv,True)); i+=len(inv);continue"
        assert s.count(old)==1
        return s.replace(old,'''            if i in kept:
                a,inv=kept[i]
                segments.append((a,inv,True))
                if not empty:
                    empty.append(a)
                    events.append((w.get_total_steps(),dict(command='PREFIXCREDIT',
                        objName=a,items=inv[:], delivered=pre[:])))
                i+=len(inv)
                continue''')
    with patch.object(pilot.shield,'shielded_base',amended):
        return pilot.sources()
