"""Restore an untagged cohort only with actual upstream and downstream cuts."""
import json
import subprocess
import sys
from itertools import product
from core import Cut,can_open

def read4(stream):
    row=tuple(map(int,stream.readline().split()))
    assert len(row)==4,row
    return Cut(bool(row[0]),row[1],row[2],bool(row[3]))

def experiment(case,method):
    p=subprocess.Popen([sys.argv[1]],stdin=subprocess.PIPE,stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE,text=True)
    def send(text):p.stdin.write(text+'\n');p.stdin.flush()
    try:
        send(case)
        send(('A' if method=='publication' else 'S')+' 1')
        if method=='drain':
            send('D 1')
        send('M 1')
        c=read4(p.stdout)
        # Direct strongest same-envelope rule: a failure witness for each
        # disallowed condition, keeping terminal prerequisite separate from
        # the set of still eligible old fragments.
        old_is_possible = (not c.old_sources_sealed or
                           c.old_before_dispatch>0 or c.old_after_dispatch>0)
        legal = not old_is_possible and c.old_duty_paid
        assert legal==can_open(c)
        d='X' if method=='publication' else 'Y' if can_open(c) else 'N'
        send('F 1 '+d)
        row=p.stdout.readline().split()
        assert len(row)==4 and row[1]=='1',row
        if method!='publication':
            assert (row[3]=='llr')==can_open(c)
            assert (row[2]=='1')==can_open(c)
        return dict(cut=c.__dict__,action=d,old_paid=int(row[0]),
                    independent=int(row[1]),assembled=row[3])
    finally:
        p.stdin.close();assert p.wait()==0,p.stderr.read()
        p.stdout.close();p.stderr.close()

rows={}
for case,method in product("qtpwu",("publication","close","drain")):
    rows[case+":"+method]=experiment(case,method)
for case in 'qtpw':
    assert rows[case+':publication']['assembled']=='llq'
    assert rows[case+':drain']['assembled']=='llr'
assert rows['q:close']['assembled']=='llr'
assert rows['p:close']['assembled']=='llr'
assert rows['w:close']['assembled']=='llr'
assert rows['t:close']['assembled']=='-'
assert rows['t:close']['cut']['old_before_dispatch']==0
assert rows['t:close']['cut']['old_after_dispatch']==1
assert all(rows['u:'+m]['old_paid']==0 and rows['u:'+m]['independent']==1
           for m in ('close','drain'))
print(json.dumps(rows,sort_keys=True,indent=2))
