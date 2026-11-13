"""No resampling: validate field changes against final saved interface."""
from copy import deepcopy
import json
from pathlib import Path
from experiment import Interface,check,coherent,DependencyCache,polling_trace

def main():
    root=Path(__file__).parent/'results';base=Interface(**json.loads((root/'n5_seed731_global_interface.json').read_text()))
    cases={}
    changes={'oversized_A':lambda i:i.A[0].__setitem__(0,2.),
      'negative_B':lambda i:i.B[0].__setitem__(0,-.25),
      'capture_service':lambda i:i.capture.__setitem__(0,'service'),
      'width_one':lambda i:i.widths.__setitem__(0,1),
      'new_independent_block':lambda i:i.blocks.__setitem__(0,99)}
    for name,change in changes.items():
        i=deepcopy(base);change(i);cache=DependencyCache(5)
        a=check(i,[-1]*5,10,cache)[0];b=coherent(i,[-1]*5,10,cache.factors)
        assert not a and not b;cases[name]='rejected_by_both'
    a,ta=polling_trace(base,list(range(5)));b,tb=polling_trace(base,list(reversed(range(5))))
    assert a==b and ta!=tb
    cases['genuine_changed_fifo_service_order']='different_trace_equal_capture_windows'
    (root/'changed_interface_tests.json').write_text(json.dumps(cases,indent=2));print(cases)
if __name__=='__main__':main()
