"""Exact min-plus certificate and direct substring oracle for the #475 alphabet."""
import hashlib
from itertools import product
import json
from pathlib import Path

def words():
    raw=(Path(__file__).resolve().parent.parent/"alphabet.txt").read_bytes()
    assert hashlib.sha1(f"blob {len(raw)}\0".encode()+raw).hexdigest()=="c98f10db5ed1169e82904f047a51fbdcfccb7415"
    result=[]
    for n in map(int,raw.split()):
        payload=f"{n:07b}"
        result.append("0"+payload+str(payload.count("1")%2)+"11")
    assert len(set(result))==len(result)==84
    return result

def hamming(a,b):
    assert len(a)==len(b)
    return sum(x!=y for x,y in zip(a,b))

def product_certificate(codes):
    prefixes=set(w[:i] for w in codes for i in range(11))
    by_prefix={s:[(b,"" if len(s)==10 else s+b)
                  for b in "01" if len(s)==10 and s+b in codes
                  or len(s)<10 and s+b in prefixes] for s in prefixes}
    d={(a,b):0 for a,b in product(prefixes,repeat=2) if len(a)<len(b)}
    pairs=len(d)
    assert len(prefixes)==349 and pairs==48896
    lows=[0]
    saved=None
    for n in range(1,28):
        next_d={}
        for (s,t),c in d.items():
            for (x,u),(y,v) in product(by_prefix[s],by_prefix[t]):
                q=(u,v)
                cost=c+(x!=y)
                if q not in next_d or cost<next_d[q]:
                    next_d[q]=cost
        d=next_d
        lows.append(min(d.values()))
        if n==16:
            saved=d
    assert lows[16:18]==[0,1]
    assert d=={k:v+2 for k,v in saved.items()}
    return len(prefixes),pairs,len(d),lows

def block_distance(codes, received, phase):
    """This oracle splits at a fixed phase and never builds the product."""
    at=0
    cost=0
    while at<len(received):
        n=min(11-phase,len(received)-at)
        block=received[at:at+n]
        cost+=min(hamming(block,c[phase:phase+n]) for c in codes)
        at+=n
        phase=0
    return cost

def main():
    codes=words()
    count,pairs,support,minima=product_certificate(codes)
    obs="011011011000000100110000001"
    u="011011011000000000110000001"
    v="011011011000000110110000001"
    assert hamming(obs,u)==hamming(obs,v)==1
    assert block_distance(codes,u,2)==block_distance(codes,v,5)==0
    witness=[block_distance(codes,obs,s) for s in range(11)]
    assert [s for s,c in enumerate(witness) if c<=1]==[2,5]
    u="00000000011";v="00000001111"
    assert u in codes and v in codes and hamming(u,v)==2
    differences=[i for i,(a,b) in enumerate(zip(u,v)) if a!=b]
    k=differences[0]
    w=u[:k]+v[k]+u[k+1:]
    observation=u[1:]+w+u[:10]
    assert len(observation)==31
    assert all(hamming(observation,u[1:]+f+u[:10])==1 for f in (u,v))
    assert w not in codes
    print(json.dumps({"starting_pairs":pairs,"trie_states":count,
        "certified_equal_support":support,"shift_from":16,"shift_to":27,
        "cost_increment":2,"minima_through_27":minima,
        "phase_threshold_examples":{e:17+11*e for e in range(10)},
        "27_bit_witness_phase_costs":witness,
        "31_bit_observation":observation,"31_bit_one_complete_frame_candidates":[u,v]},
        indent=2,sort_keys=True))

if __name__=="__main__":main()
