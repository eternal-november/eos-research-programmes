"""Private ordered slot instantiations atop the unchanged occurrence machine.
The parent runtime is a local dependency, not modified by this adapter.
"""
import sys
from pathlib import Path
from occurrence_machine import *

class OrderedMachine(Machine):
    def __init__(self,*args,**kwargs):
        self.interface_order={('job',0):tuple(kwargs.get('caps',()))}
        super().__init__(*args,**kwargs)
        # The finite checked signature may contain None as an actual world.
        # Base Machine uses None as its omitted-world default; retain an explicit value.
        if 'world' in kwargs:self.world=deepcopy(kwargs['world'])
    def owned(self,location):
        return self.interface_order.get(location,())
    def transfer(self,caps,src,dst):
        caps=tuple(caps)
        self.validate_transfer(caps,src)
        remaining=tuple(c for c in self.owned(src) if c not in set(caps))
        incoming=self.owned(dst)+caps
        require_distinct=len(incoming)==len(set(incoming))
        if not require_distinct:raise ValueError('ordered transfer alias')
        super().transfer(caps,src,dst)
        self.interface_order[src]=remaining;self.interface_order[dst]=incoming
    def finish(self,pid,result):
        # Primitive commit can consume/mint/reorder slots before result escrow.
        caps=tuple(c for leaf in leaves(result.tree) for c in leaf.caps)
        actual={c for c,loc in self.ledger.items() if loc==('job',pid)}
        if len(caps)!=len(set(caps)) or set(caps)!=actual:
            raise ValueError('ordered result does not partition actual ledger')
        self.interface_order['job',pid]=caps
        super().finish(pid,result)
    def assert_invariant(self):
        super().assert_invariant()
        locations=set(self.interface_order)|{loc for loc in self.ledger.values() if loc[0]!='retired'}
        for loc in locations:
            order=self.owned(loc)
            actual={c for c,l in self.ledger.items() if l==loc}
            assert len(order)==len(set(order)) and set(order)==actual,(loc,order,actual)
