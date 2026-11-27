from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess,sys,json
from grant import Gate

class Plant:
    def __init__(self,up):
        p=Path(__file__).resolve().with_name('gaz.py')
        self.proc=subprocess.Popen([sys.executable,'-B',p,up],
             stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True)
    def call(self,name):
        self.proc.stdin.write(name+'\n')
        self.proc.stdin.flush()
        k,x,z=self.proc.stdout.readline().split()
        assert k==name
        return F(x),F(z)
    def close(self):
        self.proc.stdin.close()
        assert self.proc.wait()==0

def compare(plant,gate,competitor,lost,method,maylose):
    proof=[]
    def action(a):
        v=plant.call(a)
        proof.append((a,tuple(map(str,v))))
        return v
    five=F(5,8)
    assert action("begin")==action("mail")==action("latch")== (1,five)
    def optional():
        ticket=gate.claim("independent")
        return bool(ticket and gate.consume(ticket))
    pre_optional=optional() if competitor=="early" else False
    advertised=(gate.show()==(None,0))
    gap_optional=optional() if competitor=="preview-gap" else False
    grant=None
    if method=="snapshot":
        rewrite=advertised
    elif method=="reserve":
        if advertised:grant=gate.claim("lift")
        rewrite=bool(grant)
    elif method=="robust":
        if advertised and not maylose:grant=gate.claim("lift")
        rewrite=bool(grant)
    else:raise ValueError(method)
    if rewrite:
        assert action("rewrite")== (0,0)
    if competitor=="between":
        post_optional=optional()
    else:
        post_optional=False
    if method=="snapshot" and rewrite:grant=gate.claim("lift")
    # "lost" is not exposed to the policy. It is an authored availability
    # fault at the plant seam, not a change of the scheduler ledger.
    claimed=bool(grant)
    executed_restore=False
    if claimed:
        assert not gate.consume((gate.cut+'-other','lift'))
        assert gate.consume(grant) and not gate.consume(grant)
        if not lost:
            assert action("restore")== (0,five)
            executed_restore=True
    x,z=action("setter")
    o=pre_optional or gap_optional or post_optional
    ordered=(x==0)
    preserved=(z==five)
    return dict(preview=advertised,granted=claimed,rewrote=rewrite,restored=executed_restore,
                old_h=ordered,independent_z=preserved,optional=o,trace=proof,ledger=gate.show())

def main(up):
    res=[]
    plant=Plant(up)
    try:
        for competitor,lost,method,maylose in product(("early","preview-gap","between","absent"),(False,True),
                            ("snapshot","reserve","robust"),(False,True)):
            with TemporaryDirectory() as root:
                got=compare(plant,Gate(Path(root)/'sched.sqlite','effect-1'),
                                       competitor,lost,method,maylose)
            rewrite=(competitor!="early" and not(method!="snapshot" and competitor=="preview-gap")
                     and not(method=="robust" and maylose))
            granted=rewrite and not (method=="snapshot" and competitor in ("preview-gap","between"))
            assert got['old_h']==rewrite and got['granted']==granted
            assert got['independent_z']==(not rewrite or granted and not lost)
            assert got['optional']==(competitor in ("early","preview-gap") or
                                    competitor=="between" and not granted)
            res.append(dict(competition=competitor,physical_unavailable=lost,
                            admitted_loss=maylose,method=method,**got))
    finally:
        plant.close()
    proven_finite=[x for x in res if x['method']=='robust' and
                   (x['admitted_loss'] or not x['physical_unavailable'])]
    assert all(x['independent_z'] for x in proven_finite)
    return dict(native=res,covered_fixture_cases=len(proven_finite))
if __name__=='__main__':print(json.dumps(main(Path(sys.argv[1]).resolve()),sort_keys=True))
