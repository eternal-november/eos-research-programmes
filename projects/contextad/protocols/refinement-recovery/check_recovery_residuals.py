"""Finite local checks supplement, rather than replace, contextual induction."""
from itertools import product

# phase, physical Boolean payload, durable audit flag, request budget

def stage(s):
    phase, x, d, j = s
    assert phase == 'A'
    return ('Stage', 1-x, 1, j)

def rollback(s):
    phase, y, d, j = s
    assert phase == 'Stage' and d == 1
    return ('A', 1-y, d, j)

def related(s,t):
    return s[0] == t[0] == 'A' and s[1] == t[1] and s[3] == t[3]

def method(s, op, b=None):
    phase, x, d, j = s
    assert phase == 'A' and j > 0
    if op == 'read': out, value = x, x
    elif op == 'write': out, value = 'written', b
    elif op == 'health': out, value = 'A-ready', x
    else: raise ValueError(op)
    return (op,out), ('A',value,d,j-1), 1

checks = 0
for x,d,j in product(range(2),range(2),range(4)):
    base = ('A',x,d,j)
    recovered = rollback(stage(base))
    assert related(base,recovered)
    assert recovered == ('A',x,1,j)
    # Recovery consumed k; baseline cancel also consumed k. No method restores k.
    checks += 1
for x,d0,d1,j in product(range(2),range(2),range(2),range(1,4)):
    s,t = ('A',x,d0,j),('A',x,d1,j)
    for op,b in [('read',None),('health',None),('write',0),('write',1)]:
        event_s, s1, cost_s = method(s,op,b)
        event_t, t1, cost_t = method(t,op,b)
        assert event_s == event_t and cost_s == cost_t and related(s1,t1)
        checks += 1
base=('A',0,0,2)
rec=rollback(stage(base))
assert base[2] != rec[2]  # authorized audit returns these flags
assert method(('A',0,0,1),'read')[0] != method(('A',1,0,1),'read')[0]
print(f'PASS: {checks} recovery/local invariance cases; audit and payload distinguishers checked.')

# Explicit finite capability/prefix runner. Tokens are actual identities, not
# reconstructible from receipt data; pure receipt-discard preserves all tokens.
from dataclasses import dataclass, replace
@dataclass(frozen=True)
class Config:
    store: tuple
    tokens: tuple
    datum: object = None
    events: tuple = ()
    cost: int = 0

def run(c, op):
    assert c.datum is None, "method requires its declared unit-data input"
    ts = dict(c.tokens)
    j = c.store[3]
    if op == 'stage':
        assert ts.get('r') == ('A',j) and ts.get('k') == 'Fresh'
        state, datum = stage(c.store), 'staged'
        ts['r'],ts['k'] = ('Stage',j),'Armed'
    elif op == 'rollback':
        assert ts.get('r') == ('Stage',j) and ts.get('k') == 'Armed'
        state, datum = rollback(c.store), 'rolledBack'
        ts['r'] = ('A',j)
        del ts['k']
    elif op == 'cancel':
        assert ts.get('r') == ('A',j) and ts.get('k') == 'Fresh'
        state, datum = c.store, 'cancelled'
        del ts['k']
    elif op == 'audit':
        assert ts.get('r') == ('A',j) and ts.get('a') == 'Audit1'
        state, datum = c.store, c.store[2]
        ts['a'] = 'Audit0'
    else: raise ValueError(op)
    return Config(state,tuple(sorted(ts.items())),datum,
                  c.events+((op,datum),),c.cost+1)

def discard_receipt(c):
    return replace(c,datum=None)

prefix_cases=0
for x,d,j,has_a in product(range(2),range(2),range(4),[False,True]):
    ts={'r':('A',j),'k':'Fresh'}
    if has_a: ts['a']='Audit1'
    start=Config(('A',x,d,j),tuple(sorted(ts.items())))
    rec_raw=run(discard_receipt(run(start,'stage')),'rollback')
    base_raw=run(start,'cancel')
    assert rec_raw.datum != base_raw.datum
    rec,base=discard_receipt(rec_raw),discard_receipt(base_raw)
    assert rec.datum == base.datum is None
    assert rec.tokens == base.tokens
    assert dict(rec.tokens)['r'] == ('A',j) and 'k' not in dict(rec.tokens)
    assert rec.store[3] == base.store[3] == start.store[3]
    assert related(rec.store,base.store)
    assert rec.cost == 2 and base.cost == 1 and rec.cost-base.cost == 1
    assert rec.events == (('stage','staged'),('rollback','rolledBack'))
    assert base.events == (('cancel','cancelled'),)
    assert rec.events != base.events
    assert rec.events == rec_raw.events and rec.cost == rec_raw.cost
    assert base.events == base_raw.events and base.cost == base_raw.cost
    if has_a:
        assert dict(rec.tokens)['a'] == 'Audit1'
        audited_rec,audited_base=run(rec,'audit'),run(base,'audit')
        assert audited_rec.tokens == audited_base.tokens
        assert dict(audited_rec.tokens) == {'a':'Audit0','r':('A',j)}
        assert audited_rec.datum == 1 and audited_base.datum == d
        # Returning the Boolean keeps the exact token output, including spent a.
        assert audited_rec.store == rec.store
    else:
        try: run(rec,'audit')
        except AssertionError: pass
        else: raise AssertionError('audit without owned authority was accepted')
    # A receipt alone cannot reconstitute the consumed recovery token.
    fake_receipt=replace(rec,datum='staged')
    try: run(fake_receipt,'rollback')
    except AssertionError: pass
    else: raise AssertionError('receipt incorrectly authorized rollback')
    prefix_cases+=1
print(f'PASS: {prefix_cases} explicit token/prefix/boundary cases; owned audit and receipt rejection checked.')
