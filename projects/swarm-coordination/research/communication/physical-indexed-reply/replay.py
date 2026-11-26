from itertools import product
from collections import Counter
import json, random, subprocess, sys
from pathlib import Path
from hashlib import sha1
from index import by_fibers,brute,validate
from readout import controls

tag,radio=sys.argv[1:3]
old,args=sys.argv[3],sys.argv[4:]
def process(binary,rows):
    t=subprocess.run([binary],input=''.join(' '.join(map(str,x))+'\n' for x in rows),
            text=True,capture_output=True,check=True).stdout
    out=[tuple(map(int,l.split())) for l in t.splitlines()]
    assert len(out)==len(rows)
    return out

def prefix(word):return word&255

def requested_port(index):return int(index>=16)

def reply_at_site(word,observed_port):
    return -1 if observed_port is None else (word>>(8+8*observed_port))&255

def answer_at_mover(index,early,late):
    return (early>>index)&1 if index<8 else None if late<0 else (late>>(index%8))&1

def main():
    census={}
    synth=0
    for K,p,q,r in product((1,2,3),range(2),range(2),range(2)):
        D={(x,j):tuple(range(1<<q)) for x,j in product(range(1<<K),range(K))}
        a=by_fibers(K,p,q,r,D)
        assert bool(a)==(p+(1<<q)*r>=K)
        assert bool(a)==brute(K,p,q,r,D)
        if a:validate(K,p,q,r,D,a)
        synth+=1
    # On incomplete support even having every source word possible is not
    # enough to infer all (word,index) pairs. Randomized fixture selection
    # here is deterministic and explicitly not a field-rate estimate.
    rng=random.Random(602)
    for c in range(150):
        K=rng.choice((2,3))
        p,q,r=rng.choice(tuple(product(range(2),repeat=3)))
        D={(x,j):tuple(g for g in range(1<<q) if rng.randrange(5)!=0)
            for x,j in product(range(1<<K),range(K)) if rng.randrange(4)!=0}
        if not D:continue
        a=by_fibers(K,p,q,r,D)
        assert bool(a)==brute(K,p,q,r,D)
        if a:validate(K,p,q,r,D,a)
        synth+=1
    d={(x,0):(0,) for x in range(4)}|{(x,1):(0,) if x==0 else (0,1) for x in range(4)}
    assert by_fibers(2,0,1,1,d) is None
    assert by_fibers(2,1,1,1,d) is not None
    perm={(x,j):(0,1) for x,j in d}
    assert by_fibers(2,0,1,1,perm) is not None
    # Fully possible words, but an admitted index always refers to a zero.
    corr={(x,j):(0,) for x,j in product(range(7),range(3)) if not x>>j&1}
    assert by_fibers(3,0,0,0,corr) is not None
    assert by_fibers(3,0,0,0,{(x,j):(0,) for x,j in product(range(7),range(3))}) is None

    # Captured current frame; no marker; wrong identity; identical pixels on
    # a stale frame; identical pixels on a frame arriving after reply.
    frames=list(product(range(2),range(5)))
    raw=process(tag,[(p,1 if mode==1 else 2 if mode==2 else 0) for p,mode in frames])
    obs={}
    offered_epoch=11
    # Perspective of the site: an authenticated aperture frame may have
    # current or earlier capture scope and may be delivered before or
    # after the reply. Identical pixels encode none of this provenance.
    metadata=[(11,1),(11,1),(11,1),(10,1),(11,3)]
    for (port,mode),row in zip(frames,raw):
        assert row==((0,-1,-1,-1) if mode==1 else (1,8 if mode==2 else 7,port,0))
        e,t=metadata[mode]
        obs[port,mode]=row[2] if row[0:2]==(1,7) and e==offered_epoch and t<=1 else None
    assert obs[0,3] is None and obs[1,4] is None

    # A native data byte depends only on source bits and the site's
    # qualified endpoint view. The mover alone knows the requested j.
    # Authorship of x and actual field observations are not inferred.
    replies=[]; meta=[]
    words=[0,(1<<24)-1,0xaaaaaa,0x555555,0x123456,0x800000]
    words += [rng.randrange(1<<24) for _ in range(30)]
    for x,j,mode,drop in product(words,range(24),range(5),range(2)):
        e=prefix(x)
        p=obs[requested_port(j),mode]
        late=reply_at_site(x,p)
        replies.append((e,late,drop))
        meta.append((x,j,mode,drop,e,late))
    rows=process(radio,replies)
    hist=Counter()
    for (x,j,mode,drop,e,late),row in zip(meta,rows):
        early,delivered,tx,rx,other=row
        assert early==e and delivered==(late if not drop else -1) and other==1
        assert tx==1+int(late>=0) and rx==1+int(late>=0 and not drop)
        ans=answer_at_mover(j,early,delivered)
        assert (ans is not None)==(j<8 or (mode==0 and not drop))
        if ans is not None:assert ans==x>>j&1
        hist['answered' if ans is not None else 'no-certified-answer']+=1

    inline=[]
    for index,mode,drop in ((0,1,0),(8,0,0),(16,0,0),(8,2,0),(16,3,0),(16,4,0),(8,0,1),(16,1,0)):
        x=0x9c628d
        with subprocess.Popen([radio],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True) as q:
            q.stdin.write(f'{prefix(x)} -2 {drop}\n');q.stdin.flush()
            label,word=q.stdout.readline().split()
            assert label=='early'
            observed_early=int(word)
            g=requested_port(index)
            n,id,port,err=process(tag,[(g,1 if mode==1 else 2 if mode==2 else 0)])[0]
            e,t=metadata[mode]
            eligible=port if n==1 and id==7 and e==offered_epoch and t<=1 else None
            q.stdin.write(f'{reply_at_site(x,eligible)}\n');q.stdin.flush()
            ret=tuple(map(int,q.stdout.readline().split()))
            q.stdin.close()
            assert q.wait(timeout=5)==0
        ans=answer_at_mover(index,observed_early,ret[1])
        assert ans==((x>>index)&1 if index<8 or (mode==0 and not drop) else None)
        inline.append([index,mode,drop,eligible,ans])
    # Carry through the measured old hold from #596, not a guessed future
    # effect. Physical branch is the issued endpoint, even with a blank frame.
    w=Path(old)
    b=w.read_bytes()
    assert sha1(f"blob {len(b)}\0".encode()+b).hexdigest()=="ba2a4efafc15120373dfd0bc1e1942a94c34bd93"
    held=[]
    for pause in (0,1):
        q0=subprocess.run([sys.executable,'-B',old,*args,str(pause)],
                          capture_output=True,check=True,text=True)
        held.append({(x['side'],x['case']):x['physical_relocation'] for x in json.loads(q0.stdout)})
    laws=[]
    for demand in (18,19):
        base=next(k for k in held[0] if held[0][k]==demand)
        y=held[1][base]
        assert y==demand+1
        laws.append(dict(plain=demand,issued_feedback_port1=y,tight_old_safe=(y<=19)))
    # With port 1 prohibited even two perfect bytes cannot implement K=24:
    # p=r=8, q=0 (or one physical symbol), capacity 16, not 24.
    print(json.dumps(dict(exact_syntheses=synth,qualified_frame_controls=len(raw),
                raw_frames=raw,inline_native=inline,cross_readout_controls=controls(),native_packet_cases=len(rows),outcomes=dict(hist),
                staged_old_clearance=laws,full_product=dict(two_ports=24,only_one_port=16),
                guard_and_correlated_controls=True),sort_keys=True,indent=2))

if __name__=='__main__':main()
