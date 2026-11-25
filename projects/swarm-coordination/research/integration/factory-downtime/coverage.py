"""Apply preregistered event-source eligibility to the pinned archive."""
from archive_audit import load,records
from collections import Counter
import sys

def run(path):
    hs=Counter(); times=Counter(); modes=Counter(); metadata=Counter()
    n=0; down=0; nonempty_reasons=0; completed=0; work=0; orders=0
    for ns,r in records(load(path)):
        assert ns==('rcll','game_report')
        n+=1
        H,M,O=(r[k] for k in ('machine-history','machines','orders'))
        # A single initial event per machine does not define its trajectory.
        assert len(H)==len(M)==len({h['name'] for h in H})==len({m['name'] for m in M})
        assert {h['name'] for h in H}=={m['name'] for m in M}
        hs[len(H)]+=1;times.update(h['game-time'] for h in H)
        modes.update(h['state'] for h in H)
        for m in M:
            assert isinstance(m['down-period'],list) and len(m['down-period'])==2
            u,v=m['down-period']
            down+=int(0<=u<v)
            nonempty_reasons+=int(bool(m['broken-reason']))
        orders+=len(O)
        for q in O:
            vals=q['quantity-delivered']
            completed+=sum(vals) if isinstance(vals,list) else vals
        metadata[bool(r.get('end-time'))]+=1
    assert n==100 and hs=={14:100} and times=={0:1400} and modes=={'IDLE':1400}
    assert down==nonempty_reasons==completed==0 and orders==900
    assert metadata=={True:99,False:1}
    print(n,'reports;',orders,'orders; exactly one initial IDLE event per machine')
    print('positive-duration downtime intervals:',down,'nonempty broken reasons:',nonempty_reasons)
    print('end metadata in',metadata[True],'reports; delivered order units:',completed)
    print('0 eligible realized compound-fault histories; benchmark may supply nominal inputs')
if __name__=='__main__':run(sys.argv[1] if len(sys.argv)>1 else 'rcll100.gz')
