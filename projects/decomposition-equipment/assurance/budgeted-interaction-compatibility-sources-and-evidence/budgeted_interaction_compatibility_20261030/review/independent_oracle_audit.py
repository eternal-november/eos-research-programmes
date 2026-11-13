"""Independent known-world scheduling truth check for sampled oracle labels.

Only credited full-power controls and idle are necessary when the world is
known: deleting uncredited nonnegative inputs reduces present/future load and
energy, leaves stage credits intact, and sacrifices no needed information.
This dominance argument permits a complete smaller scheduling action space.
No author imports. Search limits produce UNRESOLVED, never a negative claim.
"""
import json,pathlib,itertools,time
ROOT=pathlib.Path(__file__).resolve().parents[1]
def solve(n,jobs,power,energy,world,cap=100000,seconds=10):
    started=time.monotonic();memo={};expanded=0
    def go(state):
        nonlocal expanded
        if state in memo:return memo[state]
        t,b,prev,progress=state
        remain=[(len(j['routes'][r]) if r>=0 else min(map(len,j['routes'])))-done for j,(r,done) in zip(jobs,progress)]
        if any(k>0 and (t>j['deadline'] or k>j['deadline']-max(t,j['release'])+1) for k,j in zip(remain,jobs)) or sum(remain)*2>b:return False
        if not any(remain) and not any(prev):return True
        if expanded>=cap or time.monotonic()-started>seconds:return None
        expanded+=1;options=[]
        for job,(r,done) in zip(jobs,progress):
            opt=[None]
            if job['release']<=t<=job['deadline']:
                for k,route in enumerate(job['routes']):
                    if r in (-1,k) and done<len(route):opt.append((k,route[done]))
            options.append(opt)
        controls=[]
        for credits in itertools.product(*options):
            nodes=[v[1] for v in credits if v is not None]
            if len(set(nodes))!=len(nodes) or 2*len(nodes)>min(power,b):continue
            u=tuple(2 if i in nodes else 0 for i in range(n))
            if any(u[i]+(0 if p<0 else prev[p])>3 for i,p in enumerate(world)):continue
            prog=tuple(old if c is None else (c[0],old[1]+1) for old,c in zip(progress,credits))
            urgency=sum(1/(1+j['deadline']-t) for j,c in zip(jobs,credits) if c is not None)
            controls.append((-len(nodes),-urgency,u,prog))
        controls.sort();unknown=False
        for _,__,u,prog in controls:
            answer=go((t+1,b-sum(u),u,prog))
            if answer is True:memo[state]=True;return True
            if answer is None:unknown=True
        if not unknown:memo[state]=False;return False
        return None
    v=go((0,energy,(0,)*n,tuple((-1,0) for j in jobs)))
    return dict(status='WIN' if v is True else ('LOSE' if v is False else 'UNKNOWN'),expanded=expanded,seconds=time.monotonic()-started)
rows=[]
for path in sorted((ROOT/'example'/'results').glob('*_summary.json')):
    source=json.loads(path.read_text())
    if 'case' not in source:continue
    case=source['case']
    for item in source['sampled_oracles']:
        check=solve(case['n'],source['jobs'],case['power'],case['energy'],tuple(item['world']))
        if check['status']!='UNKNOWN' and item['status']!='UNKNOWN':assert check['status']==item['status'],(case,item,check)
        rows.append(dict(case=case['id'],world=item['world'],reported=item['status'],independent=check))
report=dict(cases=len(rows),resolved=sum(r['independent']['status']!='UNKNOWN' for r in rows),mismatches=0,rows=rows)
(ROOT/'review'/'independent_oracle_results.json').write_text(json.dumps(report,sort_keys=True,indent=2));print(json.dumps({k:v for k,v in report.items() if k!='rows'}))
