"""Real durable receipt snapshots and an exact prefix reduction."""
from contextlib import closing
from itertools import combinations, combinations_with_replacement, product
from hashlib import sha256
from pathlib import Path
import importlib.util
import json
import sqlite3
import sys
import tempfile

UP=Path(sys.argv[1]).resolve()
spec=importlib.util.spec_from_file_location('journal_source',UP/'journal.py')
J=importlib.util.module_from_spec(spec)
spec.loader.exec_module(J)

def all_subsets(xs):
    return {y for k in range(len(xs)+1) for y in combinations(xs,k)}

def match_order(T,slots):
    def search(todo,used):
        if not todo:return True
        return any(i not in used and todo[0] in have and
                   search(todo[1:],used|{i}) for i,have in enumerate(slots))
    return search(T,set())

def profile(views):
    # High-to-low archive frontiers; each valid slot yields one lookup.
    slots=[sorted(v,reverse=True) for v in views]
    n=max(map(len,slots))
    return tuple(min(s[k] if k<len(s) else 0 for s in slots) for k in range(n))

def greedy(T,times,slots):
    q=sorted((times[x] for x in T),reverse=True)
    return len(q)<=len(slots) and all(a<=b for a,b in zip(q,slots))

def contract_checks():
    arrays=[x for l in (1,2,3) for xs in combinations_with_replacement(range(5),l)
        for x in [tuple(reversed(xs))]]
    selections=sorted(all_subsets(tuple(range(1,5))))
    z=0
    for left,right,third in product(arrays,arrays,arrays[1::7]):
        cuts=(left,right,third)
        prefix=profile(cuts)
        slotsets=[tuple(frozenset(range(1,t+1)) for t in g) for g in cuts]
        for X in selections:
            assert greedy(X,{i:i for i in range(1,5)},prefix)==all(
                match_order(X,s) for s in slotsets),(X,cuts,prefix)
            z+=1
    return z

def backup(src,path):
    with closing(J.open_db(src)) as a, closing(J.open_db(path)) as b:
        a.backup(b)
        assert b.execute('pragma quick_check').fetchone()==('ok',)

def get_view(path,truth):
    # Separate historical matching from the archive's latest ordinary state.
    # readonly sqlite snapshot in this controlled local archive setting.
    with closing(sqlite3.connect(str(path.resolve().as_uri())+'?mode=ro',uri=True)) as d:
        d.execute('begin')
        k=d.execute('select max(tick) from log').fetchone()[0]
        named=set()
        for symbol,(key,want) in truth.items():
            have=d.execute('select tick,payload,result from receipt where intent=?',(key,)).fetchone()
            if have==want:
                assert d.execute('select payload,result from log where tick=?',(want[0],)).fetchone()==want[1:]
                named.add(symbol)
        g=J.state(J.reconstruct(d))
        content=sha256(J.encode(g).encode()).hexdigest()
    return dict(tick=k,named=sorted(named),state=content)

def native(root):
    log,tags=J.plan()
    names=['acceptA','unloadA','acceptB']
    tel={s:tags[s]+1 for s in names}
    w=root/'writer.sqlite'
    with closing(J.open_db(w)) as d:
        for i,act in enumerate(log[:max(tel.values())]):
            J.apply(d,f'run:{i}',act,'none','bundled')
            if i+1 in tel.values():
                backup(w,root/f'cut{i+1}.sqlite')
        truth={s:(f'run:{t-1}',d.execute(
            'select tick,payload,result from receipt where intent=?',(f'run:{t-1}',)).fetchone())
            for s,t in tel.items()}
        assert all(t is not None for _,t in truth.values())
    W=tuple(tel.values())
    cut_roles=((W[2],W[0]),(W[1],W[1]),(W[2],W[1]))
    full=get_view(root/f'cut{W[-1]}.sqlite',truth)
    enumerated=sorted(all_subsets(tuple(names)))
    epoch=[tuple(get_view(root/f'cut{x}.sqlite',truth) for x in role) for role in cut_roles]
    real_graphs=[tuple(set(slot['named']) for slot in role) for role in epoch]
    common=profile(cut_roles)
    result=[]
    for T in enumerated:
        if all(match_order(T,G) for G in real_graphs):
            result.append(T)
        assert greedy(T,tel,common)==(T in result)
    assert result==[(),('acceptA',),('acceptA','unloadA'),('unloadA',)]
    # Split postcommit failures remove named receipts without removing the
    # source effect. Continue the authorized test prefix without executing
    # the old intents again; save separate complete and partial archives.
    sparse=[]
    for keep in names:
        writer=root/f'{keep}-writer.sqlite'
        path=root/f'{keep}-copy.sqlite'
        for i,act in enumerate(log[:W[-1]]):
            source_subject=next((s for s,t in tel.items() if t==i+1),None)
            if source_subject is not None and source_subject!=keep:
                assert J.child(str(writer),f'run:{i}',act,'after-commit','split') is None
            else:
                with closing(J.open_db(writer)) as d:
                    J.apply(d,f'run:{i}',act,'none','bundled')
        backup(writer,path)
        v=get_view(path,truth)
        assert v['state']==full['state']
        assert v['tick']==full['tick'] and v['named']==[keep],(v,full)
        sparse.append(v)
    branch=[(set(full['named']),set(v['named'])) for v in sparse]
    assert all(any(match_order(X,b) for X in enumerated if len(X)==2) for b in branch)
    with_holes=[T for T in enumerated if all(match_order(T,b) for b in branch)]
    assert with_holes==[(),*(tuple((s,)) for s in sorted(names))]
    oracle_latest={T for T in enumerated if len(T)<=2}
    false=set(oracle_latest)-set(with_holes)
    assert false=={T for T in enumerated if len(T)==2}
    return dict(tick_by_subject=tel,coherent_prefix_slots=cut_roles,virtual_slots=common,
                prefix_common=result,complete_archive=full,sparse_archives=sparse,
                gapped_common=with_holes,pairs_losing_qualification=sorted(false))

if __name__=='__main__':
    with tempfile.TemporaryDirectory() as w: ex=native(Path(w))
    print(json.dumps(dict(native=ex,prefix_comparisons=contract_checks()),indent=2,sort_keys=True))
