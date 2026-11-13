"""Independent exhaustive audit of four supplemental diagnosis certificates."""
import json,pathlib,hashlib
ROOT=pathlib.Path(__file__).resolve().parents[1]
def nid(s):return hashlib.sha256(json.dumps(s,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def terminal(s,objective):
    budget,worlds,done=s
    if objective=='classify' and worlds in (1,2,4):return ('WIN','feasibility_class_identified')
    if done:return ('WIN','service_completed')
    if worlds==4:return ('WIN','certified_initially_infeasible') if objective=='diagnose_and_serve' else ('LOSE','broken_world_cannot_complete')
    if budget==0:return ('LOSE','remaining_service_option_exhausted')
    return None
def actions(s):return [a for a,c in [('probe',2),('serve_L',1),('serve_R',1)] if c<=s[0]]
def step(s,a):
    b,k,done=s
    if a=='probe':return None,{w:(b-2,1<<w,False) for w in range(3) if k&(1<<w)}
    target={'serve_L':0,'serve_R':1}[a];wrong=target^1
    if k&(1<<wrong):return wrong,{}
    obs={}
    if k&(1<<target):obs['done']=(b-1,1<<target,True)
    if k&4:obs['broken']=(b-1,4,False)
    return None,obs
records=json.loads((ROOT/'example'/'diagnosis_gate_results.json').read_text());audits=[]
for result in records['results']:
    objective=result['objective'];cert=result['certificate'];seen=set()
    def walk(s,status):
        key=nid(s);assert key in cert;r=cert[key];assert r['state']==list(s) and r['status']==status
        if key in seen:return
        seen.add(key);term=terminal(s,objective)
        if term:assert r['kind']=='terminal' and (r['status'],r['reason'])==term;return
        legal=actions(s)
        if status=='WIN':
            assert r['kind']=='choice' and r['action'] in legal
            unsafe,branches=step(s,r['action']);assert unsafe is None
            edges={e['observation']:e for e in r['outcomes']};assert set(edges)==set(branches) and len(edges)==len(r['outcomes'])
            for obs,sn in branches.items():assert edges[obs]['next']==nid(sn);walk(sn,'WIN')
        else:
            assert r['kind']=='refutation';coverage={e['action']:e for e in r['actions']};assert set(coverage)==set(legal) and len(coverage)==len(r['actions'])
            for a in legal:
                e=coverage[a];unsafe,branches=step(s,a)
                if 'unsafe' in e:assert unsafe is not None and e['unsafe']=={'world':unsafe,'reason':'wrong_service_mode'}
                else:assert unsafe is None and e['observation'] in branches;sn=branches[e['observation']];assert e['next']==nid(sn);walk(sn,'LOSE')
    initial=(result['energy'],7,False);assert result['root']==nid(initial);walk(initial,result['status']);assert seen==set(cert)
    audits.append(dict(objective=objective,budget=result['energy'],status=result['status'],nodes=len(seen)))
report={'status':'PASS','cases':audits,'qualification':'Classification gate identifies a singleton mechanism, stronger than merely L/R-versus-broken feasibility. In the tested reachable states this does not change the claimed four outcomes.'}
(ROOT/'review'/'independent_diagnosis_results.json').write_text(json.dumps(report,sort_keys=True,indent=2));print(json.dumps(report,indent=2))
