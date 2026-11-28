from pathlib import Path
m=Path("motion_journal.py")
s=m.read_text()
a='''    apply(d,Plant(iso,n),sys.argv[2],0,True)'''
b='''    key=sys.argv[2]
    apply(d,Plant(iso,n),None if key=="__ambient__" else key,-1 if key=="__ambient__" else 0,True)'''
assert s.count(a)==1
m.write_text(s.replace(a,b))
m=Path("journal_effect.py")
s=m.read_text()
a='''for prior,blocked,after,arm,edge,owner in product(range(2),'''
b='''for prior,blocked,after,arm,edge,owner in product(range(3),'''
assert s.count(a)==1
s=s.replace(a,b)
s=s.replace('case=(prior,blocked,after,arm,edge,owner)','case=(prior,blocked,after,arm,edge,owner)\n                settled=prior==1')
s=s.replace('prior_key=j.OLD if prior else j.SAME_PHYSICAL_UNRELATED',
'''prior_key=(j.SAME_PHYSICAL_UNRELATED,j.OLD,"__ambient__")[prior]''')
s=s.replace('if prior else None','if settled else None')
s=s.replace('''                if prior:assert traces.pop(case[1:])==(motions,plant.snapshot(pre))
                else:traces[case[1:]]=(motions,plant.snapshot(pre))''',
'''                if settled:assert traces.pop(case[1:])==(motions,plant.snapshot(pre))
                elif prior==0:traces[case[1:]]=(motions,plant.snapshot(pre))''')
s=s.replace('mov={1} if not blocked else set()',
'''mov={k for k in (0,1) if not pre.grid[0,k+1,2]}
                assert mov==({1} if not blocked else set())|({0} if prior==2 else set())''')
s=s.replace('if prior else','if settled else').replace('2 if prior else','2 if settled else')
s=s.replace('not prior and','not settled and').replace('int(prior or','int(settled or')
s=s.replace('result==[old_tick+1,1,2,2]','result==[old_tick+1,k,2,k+1]')
s=s.replace('    print(json.dumps({"cases":sum(1 for _ in product(range(2),',
            '    print(json.dumps({"cases":sum(1 for _ in product(range(3),')
# Add matched individually-valid but jointly-impossible source controls.
a='''                if after==0 and not edge and owner in (0,2):'''
b='''                if prior==2 and not blocked and arm==0 and not edge:
                    if (after,owner) in ((0,3),(3,1),(0,1),(0,2)):
                        assert (after,owner)!=(0,1) or (paid,rx,tx)==(0,0,0)
                        assert (after,owner)==(0,1) or paid==1
                        if (after,owner)==(0,1):
                            assert rad=={1} and live=={0} and mov=={0,1}
                        runs[f"compound/{after}/{owner}"]=paid
                if prior==2 and not blocked and after==3 and not edge and owner==2:
                    assert ((k,paid,rx,tx)==(1,1,1,4)) if arm<2 else ((k,paid,rx,tx)==(0,0,1,4))
                    examples[f"live-B-airtime/{arm}"]=[paid,rx,tx,result]
                if after==0 and not edge and owner in (0,2):'''
assert s.count(a)==1
s=s.replace(a,b)
m.write_text(s)
