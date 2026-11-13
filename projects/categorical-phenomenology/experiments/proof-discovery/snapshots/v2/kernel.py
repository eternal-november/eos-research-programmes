"""Small trusted checker for universally quantified equations of finite lists.

Terms are tuples: ('v', name), ('e', name), ('nil',), ('cons', Elem, List),
('app', List, List), ('rev', List). List variables and element variables are
universally quantified. Elements are an arbitrary inhabited type: no equality
on elements is used. An induction certificate has nil and cons cases, with
all non-induction variables generalized. A cons-case IH may instantiate all
parameters but must leave its fresh tail variable FIXED. This restriction is
critical: the IH does not authorize arbitrary substitution for the tail.
The checker uses no enumerator, model evaluator, or proof search code.
"""
from dataclasses import dataclass

AXIOMS = {
 'app_nil': (('app',('nil',),('v','Y')), ('v','Y')),
 'app_cons': (('app',('cons',('e','a'),('v','X')),('v','Y')), ('cons',('e','a'),('app',('v','X'),('v','Y')))),
 'rev_nil': (('rev',('nil',)), ('nil',)),
 'rev_cons': (('rev',('cons',('e','a'),('v','X'))), ('app',('rev',('v','X')),('cons',('e','a'),('nil',))))
}

class Rejected(ValueError): pass

@dataclass
class Meter:
    ticks: int = 0
    def add(self, n=1): self.ticks += n


def freeze(t):
    return tuple(freeze(x) if isinstance(x,(tuple,list)) else x for x in t)


def sort(t, meter):
    meter.add()
    if not isinstance(t,tuple) or not t: raise Rejected('Malformed term')
    f=t[0]
    if f in ('v','e') and len(t)==2 and isinstance(t[1],str): return 'L' if f=='v' else 'E'
    if f=='nil' and len(t)==1: return 'L'
    if f=='cons' and len(t)==3 and sort(t[1],meter)=='E' and sort(t[2],meter)=='L': return 'L'
    if f=='app' and len(t)==3 and sort(t[1],meter)==sort(t[2],meter)=='L': return 'L'
    if f=='rev' and len(t)==2 and sort(t[1],meter)=='L': return 'L'
    raise Rejected('Ill-typed term')


def variables(t):
    if t[0] in ('v','e'): return {t}
    return set().union(*(variables(a) for a in t[1:])) if len(t)>1 else set()


def instantiate(t, env, meter):
    meter.add()
    if t[0] in ('v','e'): return env.get(t,t)
    return (t[0],*(instantiate(a,env,meter) for a in t[1:]))


def match(pattern, term, env, fixed, meter):
    meter.add()
    if pattern[0] in ('v','e'):
        if pattern in fixed: return pattern == term
        if sort(pattern,meter)!=sort(term,meter): return False
        if pattern in env: return env[pattern]==term
        env[pattern]=term
        return True
    return pattern[0]==term[0] and len(pattern)==len(term) and all(match(a,b,env,fixed,meter) for a,b in zip(pattern[1:],term[1:]))


def subterm(t, pos):
    for i in pos:
        if not isinstance(i,int) or i<1 or i>=len(t) or t[0] in ('v','e'): raise Rejected('Invalid path')
        t=t[i]
    return t


def replace(t,pos,u):
    if not pos: return u
    i=pos[0]
    return t[:i]+(replace(t[i],pos[1:],u),)+t[i+1:]


def replay(start, steps, rules, fixed_by_rule, meter):
    t=start
    for s in steps:
        meter.add()
        key=s['rule']; direction=s.get('direction',1)
        if key not in rules or direction not in (1,-1): raise Rejected('Unknown rule or direction')
        lhs,rhs=rules[key]
        if direction==-1: lhs,rhs=rhs,lhs
        # Matching cannot leave a free RHS-only variable.
        if not variables(rhs)<=variables(lhs): raise Rejected('Unbound replacement variable')
        pos=s['path']; u=subterm(t,pos); env={}
        if not match(lhs,u,env,fixed_by_rule.get(key,set()),meter): raise Rejected('Rule does not match')
        t=replace(t,pos,instantiate(rhs,env,meter))
        if sort(t,meter)!='L': raise Rejected('Replacement changed sort')
    return t


def check_equation(eq, cert, library, meter=None):
    meter=meter or Meter()
    lhs,rhs=map(freeze,eq)
    if sort(lhs,meter)!=sort(rhs,meter) or sort(lhs,meter)!='L': raise Rejected('Not a list equation')
    rules=dict(AXIOMS)
    for name,statement in library.items():
        if name in rules or name=='IH': raise Rejected('Reserved rule name')
        rules[name]=tuple(map(freeze,statement))
    mode=cert['mode']
    def branch(a,b,c,rs,fixed):
        if replay(a,c['left'],rs,fixed,meter)!=replay(b,c['right'],rs,fixed,meter): raise Rejected('Normal forms differ')
    if mode=='rewrite':
        branch(lhs,rhs,cert,rules,{})
    elif mode=='induction':
        x=('v',cert['variable']); tail=('v',cert['tail']); head=('e',cert['head'])
        vs=variables(lhs)|variables(rhs)
        if x not in vs or tail in vs or head in vs or tail==x: raise Rejected('Induction variable/freshness invalid')
        base_env={x:('nil',)}
        branch(instantiate(lhs,base_env,meter),instantiate(rhs,base_env,meter),cert['base'],rules,{})
        step_env={x:('cons',head,tail)}
        ih_env={x:tail}
        rules['IH']=(instantiate(lhs,ih_env,meter),instantiate(rhs,ih_env,meter))
        branch(instantiate(lhs,step_env,meter),instantiate(rhs,step_env,meter),cert['step'],rules,{'IH':{tail}})
    else: raise Rejected('Unknown proof mode')
    return meter.ticks


def check_bundle(bundle):
    library={}; meter=Meter()
    for entry in bundle['library']:
        if entry['name'] in library or entry['name'] in AXIOMS or entry['name']=='IH': raise Rejected('Duplicate or reserved lemma')
        eq=tuple(map(freeze,entry['equation']))
        check_equation(eq,entry['certificate'],library,meter)
        library[entry['name']]=eq
    for entry in bundle['proofs']:
        check_equation(entry['equation'],entry['certificate'],library,meter)
    return {'lemmas':len(library),'theorems':len(bundle['proofs']),'kernel_ticks':meter.ticks}

if __name__=='__main__':
    import json,sys
    with open(sys.argv[1]) as f: bundle=json.load(f)
    print(json.dumps(check_bundle(bundle),sort_keys=True))
