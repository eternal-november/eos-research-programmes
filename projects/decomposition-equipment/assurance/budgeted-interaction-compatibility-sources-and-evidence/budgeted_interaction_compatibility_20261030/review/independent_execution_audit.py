"""Independent dense interpreter. Imports no author solver, model, or checker.

Finite worlds are enumerated from ladder adjacency and no-reciprocity. All
controls and stage-credit assignments are reconstructed, not trusted from a
certificate. Physical units are doubled integers.
"""
import hashlib, itertools, json, pathlib, sys, time
from functools import lru_cache
ROOT=pathlib.Path(__file__).resolve().parents[1]

def canon(x): return json.dumps(x,sort_keys=True,separators=(',',':'))
def nid(s): return hashlib.sha256(canon(s).encode()).hexdigest()
def freeze(x): return tuple(freeze(v) for v in x) if isinstance(x,list) else x

def adjacency(n):
    return tuple(tuple([-1]+sorted({i^1}|({i-2} if i>=2 else set())|({i+2} if i+2<n else set()))) for i in range(n))

class Reference:
    def __init__(self,n,jobs,power,energy,frozen=False):
        self.n=n; self.jobs=jobs; self.power=power; self.energy=energy; self.frozen=frozen
        self.choices=adjacency(n)
        self.worlds=tuple(w for w in itertools.product(*self.choices) if all(p<0 or w[p]!=i for i,p in enumerate(w)))
        self.controls=tuple(u for u in itertools.product((0,1,2),repeat=n) if sum(u)<=power)
        self.world_queries=0;self.checked_transitions=0
    def initial(self):
        return (0,self.energy,(0,)*self.n,tuple((-1,0) for _ in self.jobs),tuple((1<<len(c))-1 for c in self.choices))
    @lru_cache(None)
    def compatible(self,domains):
        self.world_queries+=1
        return tuple(w for w in self.worlds if all(domains[i]&(1<<self.choices[i].index(p)) for i,p in enumerate(w)))
    def projected(self,ws):
        assert ws
        return tuple(sum(1<<self.choices[i].index(p) for p in {w[i] for w in ws}) for i in range(self.n))
    def remaining(self,s):
        return tuple((len(j['routes'][r]) if r>=0 else min(len(rt) for rt in j['routes']))-done for j,(r,done) in zip(self.jobs,s[3]))
    def terminal(self,s):
        t,energy,prev,progress,domains=s; rem=self.remaining(s)
        if any(k>0 and t>j['deadline'] for k,j in zip(rem,self.jobs)):return ('LOSE','deadline_missing_stage')
        if sum(rem)*2>energy:return ('LOSE','insufficient_productive_energy')
        if any(k>max(0,j['deadline']-max(t,j['release'])+1) for k,j in zip(rem,self.jobs)):return ('LOSE','insufficient_sequential_slots')
        if sum(rem)==0 and set(prev)<={0}:return ('WIN','mission_complete_and_tail_cleared')
        if t>max(j['deadline'] for j in self.jobs)+1:return ('LOSE','horizon_exhausted')
        return None
    def actions(self,s):
        return self._actions_key(s[0],s[1],s[3])
    @lru_cache(None)
    def _actions_key(self,t,energy,progress):
        out=[]
        for controls in self.controls:
            if sum(controls)>energy:continue
            opts=[]
            for j,(selected,done) in zip(self.jobs,progress):
                candidates=[(-1,None)]
                for r,route in enumerate(j['routes']):
                    if selected not in (-1,r) or done>=len(route) or not j['release']<=t<=j['deadline']:continue
                    if controls[route[done]]==2:candidates.append((r,route[done]))
                opts.append(candidates)
            for allocation in itertools.product(*opts):
                nodes=[node for _,node in allocation if node is not None]
                if len(set(nodes))==len(nodes):out.append((controls,tuple(r for r,_ in allocation)))
        return tuple(out)
    @lru_cache(None)
    def delayed_groups(self,domains,prev):
        groups={}
        for world in self.compatible(domains):
            obs=tuple(0 if p<0 else prev[p] for p in world)
            groups.setdefault(obs,[]).append(world)
        return tuple((obs,self.projected(ws)) for obs,ws in sorted(groups.items()))
    @lru_cache(None)
    def supported(self,domains):
        return self.projected(self.compatible(domains))
    def step(self,s,a):
        self.checked_transitions+=1
        t,energy,prev,progress,domains=s; controls,credits=a
        support=self.supported(domains)
        for i in range(self.n):
            for bit,p in enumerate(self.choices[i]):
                if support[i]&(1<<bit) and controls[i]+(prev[p] if p>=0 else 0)>3:
                    return {'unsafe':True}
        updated=tuple((r,k) if c<0 else (c,k+1) for (r,k),c in zip(progress,credits))
        if self.frozen:return {'outcomes':[((),(t+1,energy-sum(controls),controls,updated,domains))]}
        outcomes=[]
        for delay,postdomains in self.delayed_groups(domains,prev):
            obs=tuple(a+b for a,b in zip(controls,delay))
            outcomes.append((obs,(t+1,energy-sum(controls),controls,updated,postdomains)))
        return {'outcomes':outcomes}
    def verify_unsafe(self,s,a,witness):
        if 'node' in witness:
            i=witness['node'];p=witness['parent'];load=a[0][i]+(s[2][p] if p>=0 else 0)
            assert load==witness['twice_load'] and load>3
            assert self.supported(s[4])[i] & (1<<self.choices[i].index(p))
        else:raise AssertionError(('unrecognized unsafe witness',witness))
    def certificate(self,result):
        if result['status']=='UNKNOWN':
            assert result['certificate']=={}
            return {'status':'UNKNOWN','nodes':0,'actions':0}
        cert=result['certificate']; seen=set(); active=set();counts={'actions':0,'branches':0,'unsafe':0}
        def visit(s,status):
            key=nid(s);assert key in cert,key
            rec=cert[key];assert freeze(rec['state'])==s and rec['status']==status
            if key in seen:return
            assert key not in active;active.add(key)
            term=self.terminal(s)
            if term:
                assert rec['kind']=='terminal' and tuple(term)==(rec['status'],rec['reason'])
            elif status=='WIN':
                assert rec['kind']=='choice';a=freeze(rec['action']);assert a in self.actions(s)
                step=self.step(s,a);assert not step.get('unsafe'); counts['actions']+=1
                edges={freeze(e['observation']):e for e in rec['outcomes']}
                assert len(edges)==len(rec['outcomes'])==len(step['outcomes'])
                for obs,sn in step['outcomes']:
                    assert obs in edges and edges[obs]['next']==nid(sn)
                    counts['branches']+=1;visit(sn,'WIN')
            else:
                assert rec['kind']=='refutation'
                edges={freeze(e['action']):e for e in rec['actions']}
                allowed=self.actions(s)
                assert len(edges)==len(rec['actions'])==len(allowed)
                assert set(edges)==set(allowed)
                for a in allowed:
                    e=edges[a];step=self.step(s,a);counts['actions']+=1
                    if 'unsafe' in e:
                        assert step.get('unsafe');self.verify_unsafe(s,a,e['unsafe']);counts['unsafe']+=1
                    else:
                        assert not step.get('unsafe')
                        branches=dict(step['outcomes']);obs=freeze(e['observation']);assert obs in branches
                        sn=branches[obs];assert e['next']==nid(sn)
                        counts['branches']+=1;visit(sn,'LOSE')
            active.remove(key);seen.add(key)
        assert result['root']==nid(self.initial())
        visit(self.initial(),result['status']);assert seen==set(cert)
        return dict(status='PASS',nodes=len(seen),**counts)


def audit_exports(path):
    data=json.loads(pathlib.Path(path).read_text());total={'states':0,'actions':0,'transitions':0,'outcomes':0}
    for block in data:
        ref=Reference(block['n'],block['jobs'],block['power'],block['energy'])
        for sample in block['samples']:
            s=freeze(sample['state']);total['states']+=1
            supported=ref.projected(ref.compatible(s[4]))
            assert list(supported)==sample['support']
            assert set(ref.actions(s))=={freeze(a) for a in sample['actions']}
            total['actions']+=len(sample['actions'])
            for test in sample['transitions']:
                a=freeze(test['action']);got=ref.step(s,a);total['transitions']+=1
                if test['unsafe'] is not None:
                    assert got.get('unsafe');ref.verify_unsafe(s,a,test['unsafe'])
                else:
                    assert not got.get('unsafe')
                    expected={(freeze(x['observation']),freeze(x['state'])) for x in test['outcomes']}
                    assert set(got['outcomes'])==expected
                    total['outcomes']+=len(expected)
    return total

if __name__=='__main__':
    if len(sys.argv)>1:print(json.dumps(audit_exports(sys.argv[1]),indent=2))
    else:print('Independent reference ready; pass author export JSON for semantic comparison.')
