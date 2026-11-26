from collections import Counter
from itertools import combinations,product
import json
from protocol import Charter, Effect, assign, hall_lower, locally_admit, reply

def naive(allowed):
    best=None
    for placement in product(*allowed):
        width=max(Counter(placement).values(),default=0)
        best=width if best is None else min(width,best)
    return best

assign_tests=0
for n,m in [(1,3),(2,3),(3,3),(4,3),(4,2)]:
    sets=[frozenset(a) for k in range(1,m+1) for a in combinations(range(m),k)]
    for rules in product(sets,repeat=n):
        cap=hall_lower(rules)
        assert cap==naive(rules)
        good=assign(rules,cap)
        assert good is not None and max(Counter(good).values())==cap
        assert all(h in ok for h,ok in zip(good,rules))
        assert assign(rules,cap-1) is None
        assign_tests+=1
assert hall_lower((frozenset(),frozenset([0]))) is None
assert assign((frozenset(),frozenset([0])),2) is None

# Two legal charter revisions for six names and three hint symbols.
# Both use the same total vocabulary. Restricting five names to two hints
# makes response width 3 even though the average bound suggests just 2.
wide=(frozenset(range(3)),)*6
narrow=(frozenset([0,1]),)*5+(frozenset([2]),)
assert hall_lower(wide)==2 and hall_lower(narrow)==3
for n in range(1,7):
    # Every truth table restriction requires a different response.
    bucket=tuple(range(n))
    charter=Charter(1,(bucket,))
    messages={reply(charter,0,0,a).bits for a in product((False,True),repeat=n)}
    assert len(messages)==2**n

# Equal bits and length with different roster order are materially different.
c=Charter(1,((0,1),))
c2=Charter(2,((1,0),))
r=reply(c,0,0,(1,0))
assert locally_admit(c,0,0,0,r)
assert not locally_admit(c2,0,1,0,r)

# All authorities are compliant. The final resource gate does not repair a
# wrong local authorization decision made earlier at the irreversible cut.
effects=0
for old,new in product(product((False,True),repeat=2),repeat=2):
    for v in product(range(2),repeat=6):
        j,seen,bump,scope_change,phys,continue_old=v
        queried=reply(c,0,0,old) if seen else None
        lawful=locally_admit(c,0,j,0,queried)
        assert lawful==bool(seen and old[j])
        gates=Effect(bump,c2 if scope_change else c,tuple(new if bump else old),
                     ['A','A'],(not phys,not phys),['pickup','pickup'],[None,None])
        assert gates.can_amend('A',j) and not gates.can_amend('B',j)
        assert (not continue_old or gates.serve_old())
        won=gates.commit(queried,j,0) if lawful else False
        assert won==bool(seen and old[j] and not bump and not scope_change and phys)
        assert gates.can_amend('B',j)==won and gates.can_amend('A',j)==(not won)
        assert gates.can_amend('A',1-j) and not gates.can_amend('B',1-j)
        assert gates.at[j]==('receiving-bay' if won else 'pickup')
        assert gates.at[1-j]=='pickup'
        assert gates.old_at==('separate-destination' if continue_old else 'separate-origin')
        # Duplicate on old authority cannot repeat a physical or rights change.
        assert not gates.commit(queried,j,0)
        assert not gates.schedule_next('A',j,'inspect')
        hint_of_new_need='inspect' if continue_old else 'egress'
        assert gates.schedule_next('B',j,hint_of_new_need)==won
        assert gates.next_permits[j]==(hint_of_new_need if won else None)
        assert gates.next_permits[1-j] is None
        effects+=1

# A source-valid direct authorization has exactly the same semantics as
# the typed transfer if the direct guard is allowed to inspect these effects.
# A fixed named holder (even allowed to be both or neither) cannot match
# the two distinct exclusive future amendment cuts.
actors={'A','B'}
fixed=[{'A'},{'B'},actors,set()]
assert not any(s=={'A'} and s=={'B'} for s in fixed)
print(json.dumps(dict(allowed_hint_patterns=assign_tests,
       local_admission_and_effect_controls=effects,wide_reply_bits=2,narrow_reply_bits=3),
       sort_keys=True))
