"""Uncapped absolute-time source validator for two histories."""
from itertools import product

OLD=((1,5,6),(5,2,7))
NEW=((1,4,6),(4,2,7))
CASES=('A.....B.A','A.....AB.')

def valid(past,future,old=OLD,new=NEW):
    prev={};same={};phase={'A':0,'B':0}
    for t,k in enumerate(past+future,start=-len(past)):
        if k=='.':continue
        p=(old if t<0 else new)[ord(k)-65]
        assert p[2]==old[ord(k)-65][2]
        q=(k,phase[k])
        if t-prev.get(k,-10000)<p[phase[k]] or t-same.get(q,-10000)<p[2]:
            return False
        prev[k]=same[q]=t;phase[k]^=1
    return True

if __name__=='__main__':
    for prior,word in zip(CASES,('BA..BA','AB..AB')):
        assert valid(prior,'')
        out={''.join(w) for w in product('AB.',repeat=6)
             if w.count('A')>=2 and w.count('B')>=2 and valid(prior,''.join(w))}
        assert out=={word},out
        print(prior,'same old profile (0,5) for both; unique amended service',word)
    assert all(valid(p,'A') and valid(p,'B') for p in CASES)
    old_words=tuple({''.join(w) for w in product('AB.',repeat=6)
                     if valid(p,''.join(w),new=OLD)} for p in CASES)
    assert old_words[0]==old_words[1]
    print(len(old_words[0]),'identical whole old legal schedules compared against both traces')
