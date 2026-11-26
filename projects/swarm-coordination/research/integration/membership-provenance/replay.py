from collections import defaultdict
from itertools import product
from adapters import PLANTS
from reserve import Profile


for plant in PLANTS:
    cert = Profile.from_worlds(plant.worlds())
    verdicts = {}
    for source in ("dedicated", "facility"):
        service, samples = plant.native_matched(source)
        assert {s[1] for s in samples} == {False,True}  # same marginal for entrant
        for ready in (True,False):
            new = plant.install(source, ready)
            result = cert.verdict(new)
            assert result == plant.native_matched(source, ready)[0]
            verdicts[source,ready] = result
    assert verdicts == {("dedicated",True):"served",("dedicated",False):"shortfall",
                        ("facility",True):"shortfall",("facility",False):"shortfall"}
    print(plant.name)
    print("  independent current member: served; same-domain replacement: shortfall")
    print("  late replacement: shortfall, regardless of domain")
    donor_cell = ("mobile-generator-source", 0, plant.horizon)
    assert cert.verdict({donor_cell:[(2,1)]}) == "unbound"

# In this new extension supply is coupled to a private retained handoff state.
# Each branch has one unit total, yet the coarse artificial product combines
# empty retained supply with empty extra supply. Fine after rebuilding only.
private_joint = [(0,1),(1,0)]
coarse = Profile.from_worlds([("same", a) for a,e in private_joint])
refined = Profile.from_worlds([(a,a) for a,e in private_joint])
assert coarse.verdict({"same":[(e,1) for a,e in private_joint]})=="shortfall"
assert all(a+e>=1 for a,e in private_joint)
assert refined.verdict({a:[(e,1)] for a,e in private_joint})=="served"
print("private coupling: old coarse rejection is not an actual shortfall; refine shared cut")

# Check exact saturated joins, absence, and incremental substitutions.
count=0
for combo in product(range(3), repeat=4):
    old = [(b,v) for b, vs in enumerate((combo[:2],combo[2:])) for v in vs]
    p = Profile.from_worlds(old)
    for new_values in product(range(3),repeat=4):
        for requested in product(range(4),repeat=2):
            ext = {j:[(new_values[2*j+i],requested[j]) for i in range(2)]
                   for j in range(2)}
            expected = "served" if all(v+e>=d
                                       for b,v in old for e,d in ext[b]) else "shortfall"
            assert expected == p.verdict(ext)
            count += 1
print("exact finite join comparisons:",count)
