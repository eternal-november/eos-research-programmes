"""Author-side certificate replay. Independent audit must use separate semantics."""
import hashlib, json, time
from exact_search import WIN, LOSE, UNKNOWN

def canonical(x): return json.dumps(x,sort_keys=True,separators=(',',':'))
def node_id(model,state):
    return hashlib.sha256(canonical(model.encode_state(state)).encode()).hexdigest()

def check_certificate(model, initial, result):
    started=time.perf_counter()
    if result['status']==UNKNOWN:
        assert not result['certificate']
        return dict(status=UNKNOWN,checked_nodes=0,transition_calls=0)
    cert=result['certificate']; seen=set(); active=set(); calls=0
    def visit(s, expected):
        nonlocal calls
        nid=node_id(model,s)
        assert nid in cert, ('missing',nid)
        rec=cert[nid]
        assert rec['state']==model.encode_state(s)
        assert rec['status']==expected
        if nid in seen: return
        assert nid not in active, 'cyclic certificate'
        active.add(nid)
        terminal=model.terminal(s)
        if terminal is not None:
            assert rec['kind']=='terminal' and rec['status']==terminal[0]
            assert rec['reason']==terminal[1]
        else:
            actions=list(model.actions(s))
            by_encoded={canonical(model.encode_action(a)):a for a in actions}
            assert len(by_encoded)==len(actions), 'noninjective action encoding'
            if expected==WIN:
                assert rec['kind']=='choice'
                a=by_encoded[canonical(rec['action'])]
                calls+=1; st=model.transition(s,a)
                assert st.unsafe is None and st.outcomes
                edges={canonical(e['observation']):e for e in rec['outcomes']}
                assert len(edges)==len(rec['outcomes'])==len(st.outcomes)
                for o,sn in st.outcomes:
                    e=edges[canonical(model.encode_observation(o))]
                    assert e['next']==node_id(model,sn)
                    visit(sn,WIN)
            else:
                assert rec['kind']=='refutation'
                coverage={canonical(e['action']):e for e in rec['actions']}
                assert len(coverage)==len(rec['actions'])==len(actions)
                assert set(coverage)==set(by_encoded)
                for ak,a in by_encoded.items():
                    e=coverage[ak]; calls+=1; st=model.transition(s,a)
                    if 'unsafe' in e:
                        assert st.unsafe is not None
                    else:
                        assert st.unsafe is None and st.outcomes
                        branches={canonical(model.encode_observation(o)):sn for o,sn in st.outcomes}
                        sn=branches[canonical(e['observation'])]
                        assert e['next']==node_id(model,sn)
                        visit(sn,LOSE)
        active.remove(nid);seen.add(nid)
    assert result['root']==node_id(model,initial)
    visit(initial,result['status'])
    assert set(cert)==seen, 'unreachable certificate nodes'
    return dict(status='PASS',checked_nodes=len(seen),transition_calls=calls,
                seconds=time.perf_counter()-started)
