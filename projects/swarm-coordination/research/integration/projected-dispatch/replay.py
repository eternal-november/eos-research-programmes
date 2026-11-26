"""Direct subqueue oracle and selected native simulator witness."""
from itertools import product
import json
import subprocess
import sys
from admission import Item, choose

def exhaustive(queue, missing):
    n=len(queue)
    valid=[]
    for choices in product((False,True),repeat=n):
        if any(bit and (queue[i].inputs & missing) for i,bit in enumerate(choices)):
            continue
        if any(not choices[i] and choices[j] and
               queue[i].resources&queue[j].resources
               for i in range(n) for j in range(i+1,n)):
            continue
        valid.append(frozenset(i for i,bit in enumerate(choices) if bit))
    top=frozenset().union(*valid)
    assert top in valid
    return tuple(x.name for i,x in enumerate(queue) if i in top)

class Plant:
    def __init__(self,scenario):
        self.p=subprocess.Popen([sys.argv[1]],stdin=subprocess.PIPE,stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE,text=True)
        self.write(scenario)
    def write(self,s):
        self.p.stdin.write(s+'\n')
        self.p.stdin.flush()
    def desc(self):
        self.write('M 0')
        data=[]
        for ln in self.p.stdout:
            if ln.startswith('!'):return data,frozenset(ln[1:].split())
            k,s,*rs=ln.split()
            writes=frozenset({'tx:'+s}|{'rx:'+r for r in rs})
            data.append(Item(k,writes,frozenset([s,*rs])))
        assert False
    def call(self,c):
        self.write(c)
        s,q,z=self.p.stdout.readline().split('|')
        return [s.split(),q.strip(),list(map(int,z.split()))]
    def close(self):
        self.p.stdin.close()
        assert self.p.wait()==0,self.p.stderr.read()
        self.p.stdout.close()
        self.p.stderr.close()

def one(scenario,mode):
    p=Plant(scenario)
    try:
        items,missing=p.desc()
        correct,held=choose(items,missing)
        assert correct==exhaustive(items,missing)
        if mode=='empty':
            init=p.call('N 0')
        elif mode=='projection':
            init=p.call('P 0 '+(''.join(correct) or '-'))
        else:
            # Deliberately erase one receiver dependency of held c.
            wrong=[Item(x.name,x.resources-{'rx:D2'} if x.name=='c' else x.resources,
                        x.inputs) for x in items]
            policy,_=choose(wrong,missing)
            init=p.call('P 0 '+''.join(policy))
        return dict(early=init,at_recovery=p.call('R 0.25'),
                    from_read=[''.join(correct),''.join(held)])
    finally:
        p.close()

rows={}
for kind in 'NOF': # none using failed input, ordinary blocked, fanout blocked
    for mode in ('empty','projection','wrong'):
        rows[kind+':'+mode]=one(kind,mode)
for kind in 'NOF':
    stock=rows[kind+':empty']
    proj=rows[kind+':projection']
    assert stock['early'][0]==[] and 'a' in stock['early'][1]
    assert set(stock['at_recovery'][0])==set(proj['at_recovery'][0])
    assert stock['at_recovery'][2]==proj['at_recovery'][2]
    assert 'X:a' in proj['early'][0] and 'E:e' in proj['early'][0]
    if kind!='N':
        assert all(k not in proj['early'][0] for k in ('B:b','F:b','Y:c','Y:d'))
        assert 'Y:c' in proj['at_recovery'][0] and 'Y:d' not in proj['at_recovery'][0]
        assert 'Y:d' in rows[kind+':wrong']['early'][0]
        assert 'Y:c' not in rows[kind+':wrong']['at_recovery'][0]

scope=(frozenset('A'),frozenset('B'),frozenset('AB'))
count=0
for n in range(6):
    for options in product(scope,repeat=n):
        for flags in product((False,True),repeat=n):
            q=tuple(Item(chr(65+i),s,frozenset('X') if f else frozenset())
                    for i,(s,f) in enumerate(zip(options,flags)))
            assert choose(q,{'X'})[0]==exhaustive(q,{'X'})
            count+=1
limits=[]
for configured in (1,5,30):
    z=subprocess.check_output([sys.argv[1],str(configured)],text=True).split()
    assert z==[str(configured),'6']
    limits.append(dict(receiver_configured_limit=configured,
                       rejected_tx_5=True,accepted_tx_6=True,retained_charge=6))
print(json.dumps(dict(native=rows,limits=limits,exact_subset_comparisons=count),indent=2,sort_keys=True))
