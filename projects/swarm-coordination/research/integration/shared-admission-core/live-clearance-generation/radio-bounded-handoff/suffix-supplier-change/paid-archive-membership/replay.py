"""Paid archive classification while protecting a previously committed job."""
from itertools import product
from pathlib import Path
from fractions import Fraction as F
import json
import sys
import tempfile

import archived_matcher as m
import supplier as sup

NAMES=('acceptA','unloadA','acceptB')
ENC={('Q',0):'a',('Q',1):'b',('P',0):'c',('P',1):'d'}
DEC={v:k for k,v in ENC.items()}

def build(up):
    src=None
    old=sup.load_runner(up/'feedback.py')
    def intercept(text,filename,mode):
        nonlocal src
        src=text
        return compile('',filename,mode)
    sup.compile=intercept
    try:
        sup.instrument(up/'parent.py',old)
    finally:
        del sup.compile
    assert src
    def replace(old,new):
        nonlocal src
        assert src.count(old)==1,old
        src=src.replace(old,new)
    replace('    checks(6)\n    header_view=None',
            '    assert not send(5,"Base","sink","z"*base_debit,False)\n'
            '    assert tape[-1][4]==base_debit\n    checks(6)\n    header_view=None')
    replace('    observed=send(7,"Base","preq",mode,int(notice==7))',
             '''    cue=None
    if framing=="separate":
        observed=send(7,"Base","preq",mode,True)
    else:
        raw=send(7,"Base","preq",encode[mode,source_bit],delivery!="erase")
        observed,cue=decode.get(raw,(None,None))
'''.rstrip())
    replace('                assert requested\n        if notice==8:\n            assert send(8,"Base","preq",mode,True)==mode\n        late=None',
             '''                # A failure to reserve the actual supplier is not a success.
        if framing=="separate" and requested and delivery!="late":
            raw=send(7,"Base","preq",str(source_bit),delivery!="erase")
            cue=int(raw) if raw in ("0","1") else None
        late=None''')
    replace('            permitted=selected[0]\n            late=send(8,permitted,"owed",fragment if requested else row[0],\n                      permitted==mode)',
            '''            permitted=selected[0]
            late=send(8,permitted,"owed",fragment if requested else row[0],
                      permitted==mode)
        if framing=="separate" and requested and delivery=="late":
            send(8,"Base","preq",str(source_bit),True)  # not a decision input''')
    replace('    if selected and row and header_view and not first_complete:',
            '    if selected and requested and row and header_view and not first_complete:')
    replace('charged=sum(x[4] for x in tape)+2,side=2,selection=selected)',
            'charged=sum(x[4] for x in tape)+2,side=2,selection=selected,cue=cue)')
    ns={}
    exec(compile(src,'joined-trial','exec'),ns)
    return ns

def all_choices(roles,cue):
    candidates=[v for v in roles if cue is None or int(NAMES[0] in v[1])==cue]
    assert candidates
    return {xs for xs in m.all_subsets(NAMES) if all(m.match_order(xs,v) for v in candidates)}

def policy(cue):
    if cue==1: return [(NAMES[0],NAMES[1]),(NAMES[2],)]
    if cue==0: return [(NAMES[1],NAMES[2]),(NAMES[0],)]
    return [(x,) for x in NAMES]

def main():
    up=Path(sys.argv[1])
    with tempfile.TemporaryDirectory() as root:
        export=m.native(Path(root))
    full=frozenset(export['complete_archive']['named'])
    roles=[(full,frozenset(v['named'])) for v in export['sparse_archives']]
    for cue in (None,0,1):
        possible=all_choices(roles,cue)
        p=F(1,3) if cue is None else F(1,2)
        assert all(choice in possible for choice in policy(cue))
        assert all(F(sum(x in a for a in policy(cue)),len(policy(cue)))==p for x in NAMES)
        # Summed marginals bound the blind cell; any negative membership cell
        # has a role excluding A from one slot and a conflicting other role.
        assert max(map(len,possible))==(1 if cue is None else 2)
        if cue is not None:
            forbidden={tuple(y for y in NAMES if y!=x) for x in NAMES}-possible
            assert forbidden
            i,j=next(iter(forbidden))
            assert all(int(i in t)+int(j in t)<=1 for t in possible)
    s=build(up)
    rows=[]
    plan=sup.verdict(7,33,{'Q','P'})
    plan={tuple((7,v) for _,v in view):value for view,value in plan.items()}
    for role,mode,b,framing,delivery in product(roles,('Q','P'),(316,317,318),
                                                ('separate','packed'),('ok','erase','late')):
        if framing=='packed' and delivery=='late':continue
        bit=int(NAMES[0] in role[1])  # exact matched SQL receipt, not latest pose
        s.update(mode=mode,notice=7,p_debit=33,plan=plan,encode=ENC,decode=DEC,
                 source_bit=bit,base_debit=b,framing=framing,delivery=delivery)
        case=[]
        for arm in ('split','direct'):
            with tempfile.TemporaryDirectory() as d:
                case.append(s['trial'](Path(d),'after-commit','after-witness-commit',
                                       True,True,140,arm))
        assert case[0]==case[1]
        v=case[0]
        old=b<=317 and not(framing=='packed' and delivery=='erase')
        decoded=delivery=='ok' and (framing=='packed' or b<=316)
        assert bool(v['apply'])==old and v['side']==2
        assert v['cue']==(bit if decoded else None)
        base=[x for x in v['radio'] if x[1]=='Base']
        assert sum(x[4] for x in base)<=320
        if framing=='separate' and b==316 and delivery=='late':
            assert base[-1][0]==8 and base[-1][-2:]==(1,True)
        if framing=='separate' and b==317 and delivery=='ok':
            assert base[-1][0]==7 and base[-1][-2:]==(0,False)
        if framing=='packed' and delivery=='erase':
            assert base[-1][0]==7 and base[-1][-2:]==(1,False)
        # Decoding alone is not joint success: at 318 the prepare cannot fit.
        read=v['cue']
        choices=policy(read)
        assert all(m.match_order(a,role) for a in choices)
        rows.append(dict(sparse=sorted(role[1]),mode=mode,debit=b,framing=framing,
                         delivery=delivery,per_subject='1/2' if read is not None else '1/3',
                         simultaneous=old and decoded,native=v))
    s['air'].stdin.close()
    assert s['air'].wait()==0
    print('{"cases":'+str(len(rows))+',"rows":[')
    print(',\n'.join(json.dumps(row,sort_keys=True,separators=(',',':')) for row in rows))
    print(']}')

if __name__=='__main__':main()
