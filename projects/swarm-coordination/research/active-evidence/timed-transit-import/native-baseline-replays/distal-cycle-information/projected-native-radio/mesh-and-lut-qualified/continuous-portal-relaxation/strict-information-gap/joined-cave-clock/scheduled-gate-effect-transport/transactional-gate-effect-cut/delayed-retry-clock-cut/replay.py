from pathlib import Path
from tempfile import TemporaryDirectory
from itertools import product
from contextlib import closing
import ast, json, sqlite3, subprocess, sys
U=Path(sys.argv[1]).resolve()
# Adopt the exact parent store schema without executing parent trials.
ast0=ast.parse((U/'trace.py').read_text())
fn=next(v for v in ast0.body if isinstance(v,ast.FunctionDef) and v.name=='scenario')
queries=[ast.literal_eval(v.args[0]) for v in ast.walk(fn) if isinstance(v,ast.Call) and
         isinstance(v.func,ast.Attribute) and v.func.attr=='executescript']
assert len(queries)==1
schema=queries[0]
worker=U/'worker.py'
def call(db,args,status):
    p=subprocess.run([sys.executable,str(worker),str(db),*map(str,args)],
                     text=True,capture_output=True,timeout=10)
    assert p.returncode==status and not p.stderr,p
    return p.stdout.strip()
def snapshot(db,now):
    with closing(sqlite3.connect(db)) as c:
        hist=c.execute('SELECT key,at,decision FROM Receipt ORDER BY key').fetchall()
        inst=c.execute('SELECT key,start,finish FROM Installed ORDER BY key').fetchall()
        ev=c.execute('SELECT key,at,decision FROM Event ORDER BY key').fetchall()
    assert ev==hist
    return hist,inst,tuple(a for a,start,end in inst if start<=now<=end)
def scenario(gate,order,cut):
    out,back=map(tuple,gate['hulls'])
    core=gate['cores'][1]
    safe=out[1]+10**6
    inside=core[0]
    after=back[1]+1
    span=250000
    assert safe+span<back[0] and inside+span<=core[1] and after+span<gate['end']
    t0,t1={'clear_to_held':(safe,inside),'held_to_clear':(inside,after)}[order]
    with TemporaryDirectory() as d:
        db=Path(d)/'gate.db'
        with closing(sqlite3.connect(db)) as c:
            c.executescript(schema)
            c.executemany('INSERT INTO Hold VALUES (?,?)',(out,back))
            c.commit()
        assert call(db,('issue','A',safe,span),43)==''
        assert call(db,('apply','A',t0,'effect',cut),{'before':51,'after':52}[cut])==''
        hist,inst,current=snapshot(db,t1)
        assert (len(hist),len(inst),current)==(int(cut=='after'),int(cut=='after' and order=='clear_to_held'),())
        old=call(db,('apply','A',t1,'effect','reply'),0)
        hist,inst,current=snapshot(db,t1)
        expected='closed' if (order=='clear_to_held')==(cut=='after') else 'blocked'
        assert old==expected
        (key,t,receipt),=hist
        assert (key,t,receipt)==('A',t0 if cut=='after' else t1,expected)
        assert inst==([] if expected=='blocked' else [('A',t,t+span-1)])
        assert current==(('A',) if expected=='closed' and cut=='before' else ())
        # Only the branch that already settled to refusal uses a new,
        # explicitly authorized id. First request remains immutable.
        fresh=None
        if order=='held_to_clear' and cut=='after':
            assert call(db,('issue','B',t1,span),43)==''
            fresh=call(db,('apply','B',t1,'effect','reply'),0)
            h,i,v=snapshot(db,t1)
            assert h==[('A',t0,'blocked'),('B',t1,'closed')] and i==[('B',t1,t1+span-1)] and v==('B',)
            assert fresh=='closed'
            assert call(db,('apply','A',t1,'effect','reply'),0)=='blocked'
        return dict(first_us=t0,retry_us=t1,receipt=old,receipt_us=t,
                    present_closed=bool(current),fresh=fresh)
for z in (U/'PORTAL.jsonl').read_text().splitlines():
    gate=json.loads(z)
    out={f"{o}/{c}":scenario(gate,o,c) for o,c in product(('clear_to_held','held_to_clear'),('before','after'))}
    assert out['clear_to_held/after']['receipt']==out['held_to_clear/before']['receipt']
    assert out['clear_to_held/after']['present_closed']!=out['held_to_clear/before']['present_closed']
    assert out['clear_to_held/before']['receipt']==out['held_to_clear/after']['receipt']
    print(json.dumps(dict(gate=gate['gate'],outcomes=out),sort_keys=True))
