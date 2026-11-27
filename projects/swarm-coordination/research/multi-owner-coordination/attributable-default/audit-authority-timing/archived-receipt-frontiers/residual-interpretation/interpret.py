"""Execute a bounded residual-profile interpretation for read-only receipts."""
from collections import defaultdict
from contextlib import closing
from itertools import product
from pathlib import Path
import importlib.util
import json, sqlite3, sys, tempfile

UP=Path(sys.argv[1]).resolve()
sp=importlib.util.spec_from_file_location('verified_matcher',UP/'archived_matcher.py')
V=importlib.util.module_from_spec(sp);sp.loader.exec_module(V)
J=V.J

def source_f(d,qs,key_payload_cut):
    key,payload,cut=qs[key_payload_cut]
    row=d.execute('select tick,payload,result from receipt where intent=?',(key,)).fetchone()
    if row is None or row[0]>cut or row[1]!=payload:return None
    return (key,*row)

def stateless_f(packet,qs,key_payload_cut):
    key,payload,cut=qs[key_payload_cut]
    row=packet[0].get(key)
    if row is None or row[0]>cut or row[1]!=payload:return None
    return (key,*row)

def export(d,keys):
    # Actual map at one immutable snapshot, not a comparison with a
    # subsequent open/autocommit query to a possibly later historian.
    rows={}
    for k in keys:
        x=d.execute('select tick,payload,result from receipt where intent=?',(k,)).fetchone()
        if x is not None:
            assert d.execute('select payload,result from log where tick=?',(x[0],)).fetchone()==x[1:]
            rows[k]=x
    return rows,'S1'

def model(root):
    log,tags=J.plan()
    names=('acceptA','unloadA','acceptB')
    locs=[tags[x] for x in names]
    keys=[f'run:{i}' for i in locs]
    g=J.make(); rewards=[J.step(g,a) for a in log[:locs[-1]+1]]
    # Independently declared target schema: all presence subsets of
    # these named realized plain-run outcomes, with arbitrary labels.
    rows={k:(i+1,J.encode(log[i]),J.encode(rewards[i])) for k,i in zip(keys,locs)}
    targets=[({k:rows[k] for j,k in enumerate(keys) if bits>>j&1},label)
             for bits in range(8) for label in ('S1','S2','S3')]
    Q=[(k,P,t) for k,i in zip(keys,locs)
       for P in (J.encode(log[i]),'[]') for t in (0,i,i+1,locs[-1]+2)]
    Q.extend([('not-the-authorized-key',J.encode(log[i]),locs[-1]+2) for i in locs])
    assert len(Q)==27
    good_query=[Q.index((k,v[1],locs[-1]+2)) for k,v in rows.items()]
    native=[]
    for bits in range(8):
        db=root/f'author-{bits}.sqlite'; arc=root/f'archive-{bits}.sqlite'
        for i,act in enumerate(log[:locs[-1]+1]):
            k=f'run:{i}'
            if i in locs and not bits>>(locs.index(i))&1:
                J.child(str(db),k,act,'after-commit','split')
            else:
                with closing(J.open_db(db)) as d:J.apply(d,k,act,'none','bundled')
        V.backup(db,arc)
        with closing(sqlite3.connect(str(arc.resolve().as_uri())+'?mode=ro',uri=True)) as d:
            d.execute('begin')
            emitted=export(d,keys)
            physical=J.state(J.reconstruct(d))
            actual=tuple(source_f(d,Q,q) for q in range(len(Q)))
            assert actual==tuple(stateless_f(emitted,Q,q) for q in range(len(Q)))
            native.append((emitted,physical,actual))
    assert len({J.encode(physical) for _,physical,_ in native})==1
    target_classes={tuple(stateless_f(w,Q,q) for q in range(len(Q))) for w in targets}
    classes={x[2] for x in native}
    assert classes==target_classes and len(classes)==8
    assert len({native[b][2] for b in (0,1,3,7)})==4 # complete-prefix sublanguage
    assert native[0][2][good_query[0]]!=native[7][2][good_query[0]]
    # Reuse the exact prior matcher on either source form. All mixed
    # slot pairs are verified fixture domains; correlated real roles
    # keep only their separately admitted histories.
    sets=sorted(V.all_subsets(tuple(names)))
    checks=0
    groups=lambda evidence:{names[i] for i,k in enumerate(good_query) if evidence[k] is not None}
    for a,b in product(range(8),repeat=2):
        S=(native[a],native[b])
        src=[groups(x[2]) for x in S]
        wire=[groups(tuple(stateless_f(x[0],Q,q) for q in range(len(Q)))) for x in S]
        assert src==wire
        for wanted in sets:
            assert V.match_order(wanted,src)==V.match_order(wanted,wire)
            checks+=1
    # Keep the authored role support: one full slot and one sparse
    # slot backed by the actual native archives.
    encoded=[(groups(native[7][2]),groups(native[i][2])) for i in (1,2,4)]
    choice=[s for s in sets if all(V.match_order(s,v) for v in encoded)]
    assert all(len(s)<=1 for s in choice)
    return dict(archived_states=len(native),raw_target_states=len(targets),
                native_classes=len(classes),complete_prefix_classes=4,
                primitive_equalities=8*len(Q),matched_reader_choices=checks,
                old_effect_state_classes=1,common_choices=choice,
                exported_subjects=names)
if __name__=='__main__':
    with tempfile.TemporaryDirectory() as r: x=model(Path(r))
    print(json.dumps(x,indent=2,sort_keys=True))
