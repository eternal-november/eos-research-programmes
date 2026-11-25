"""Read-only bounded parser for pinned local MongoDB dump; no DB restore."""
from collections import Counter
import gzip, hashlib, struct, sys
from pathlib import Path
FILE_SHA='6336be1e56339981a9235edf94a6fc67bef7d93f4fb0a041b376f79256f5773e'
def load(path):
    assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==FILE_SHA
    with gzip.open(path,'rb') as f:b=f.read((64<<20)+1)
    assert len(b)<=64<<20 and b[:4].hex()=='6de29981'
    return b

def document(b,p,depth=0):
    assert depth<100
    L=struct.unpack_from('<i',b,p)[0]
    end=p+L
    assert L>=5 and end<=len(b) and b[end-1]==0
    q=p+4;out={}
    while q<end-1:
        tag=b[q];q+=1
        z=b.index(0,q,end);k=b[q:z].decode();q=z+1
        if tag in (3,4):
            val,q=document(b,q,depth+1)
            if tag==4:
                assert tuple(val)==tuple(map(str,range(len(val))))
                val=list(val.values())
        elif tag in (2,13,14):
            n=struct.unpack_from('<i',b,q)[0];q+=4
            assert n>0 and q+n<=end and b[q+n-1]==0
            val=b[q:q+n-1].decode();q+=n
        elif tag==1:val=struct.unpack_from('<d',b,q)[0];q+=8
        elif tag==5:
            n=struct.unpack_from('<i',b,q)[0];q+=5
            assert n>=0 and q+n<=end
            val='<binary>';q+=n
        elif tag==7:val=b[q:q+12].hex();q+=12
        elif tag==8:val=bool(b[q]);q+=1
        elif tag in (6,10,127,255):val=None
        elif tag in (9,16,17,18):
            fmt={9:'<q',16:'<i',17:'<Q',18:'<q'}[tag]
            val=struct.unpack_from(fmt,b,q)[0];q+=struct.calcsize(fmt)
        elif tag==19:val='<decimal>';q+=16
        else:raise ValueError((tag,k,depth))
        assert q<end and k not in out,(q,end,k)
        out[k]=val
    assert q==end-1
    return out,end

def records(b):
    p=4
    header,p=document(b,p)
    assert header['version']=='0.1'
    while b[p:p+4]!=b'\xff'*4:
        pre,p=document(b,p)
        assert 'collection' in pre and 'db' in pre
    p+=4
    eof=set()
    while p<len(b):
        h,p=document(b,p)
        ns=(h['db'],h['collection'])
        assert ns not in eof
        hs=h.get('EOF',h.get('eof',False))
        while b[p:p+4]!=b'\xff'*4:
            d,p=document(b,p)
            yield ns,d
        p+=4
        if hs:eof.add(ns)
    assert p==len(b)

def main():
    path=sys.argv[1] if len(sys.argv)>1 else 'rcll100.gz'
    n=Counter(); keys={}; shapes={}
    for ns,d in records(load(path)):
        n[ns]+=1
        keys.setdefault(ns,Counter()).update(d.keys())
        Z=shapes.setdefault(ns,{})
        for k,v in d.items():
            if isinstance(v,list):
                z=Z.setdefault(k,[0,Counter()])
                z[0]+=len(v)
                for x in v:
                    if isinstance(x,dict):z[1].update(x.keys())
            elif isinstance(v,dict):
                Z.setdefault(k,[0,Counter()])[1].update(v.keys())
    for ns,k in sorted(n.items()):
        print('collection',ns,'records',k)
        print('fields',sorted(keys[ns].items()))
        for field,(length,children) in sorted(shapes[ns].items()):
            print(' ',field,'list entries',length,'child fields',sorted(children.items()))

if __name__=='__main__':main()
