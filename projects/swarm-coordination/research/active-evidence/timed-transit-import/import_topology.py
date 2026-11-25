"""Parse only the documented simple NumPy matrix wire shape, never unpickle."""
from pathlib import Path
from pickletools import genops
import struct,math,hashlib,json,sys

MARK=object()
GLOBAL={
    ("numpy.core.multiarray","_reconstruct"),("numpy","ndarray"),("numpy","dtype")
}

def matrix(file):
    blob=Path(file).read_bytes()
    assert len(blob)<=1000000 # pinned source adapter bound
    s=[];memo=[];root=None
    for op,arg,pos in genops(blob):
        n=op.name
        if n=="PROTO":assert arg==4 and pos==0
        elif n=="FRAME":assert arg<=len(blob)
        elif n in ("SHORT_BINUNICODE","SHORT_BINBYTES","BINBYTES","BININT","BININT1","BININT2"):
            s.append(arg)
        elif n=="NONE":s.append(None)
        elif n in ("NEWFALSE","NEWTRUE"):s.append(n=="NEWTRUE")
        elif n=="MEMOIZE":memo.append(s[-1])
        elif n=="BINGET":s.append(memo[arg])
        elif n=="MARK":s.append(MARK)
        elif n in ("TUPLE1","TUPLE3"):
            k=int(n[-1]);assert len(s)>=k
            values=tuple(s[-k:]);del s[-k:];s.append(values)
        elif n=="TUPLE":
            j=max(i for i,x in enumerate(s) if x is MARK)
            values=tuple(s[j+1:]);del s[j:];s.append(values)
        elif n=="STACK_GLOBAL":
            name=s.pop();module=s.pop()
            assert (module,name) in GLOBAL
            s.append(("symbol",module,name))  # never resolved or imported
        elif n=="REDUCE":
            args=s.pop();fun=s.pop()
            if fun==("symbol","numpy.core.multiarray","_reconstruct"):
                assert args==(("symbol","numpy","ndarray"),(0,),b"b")
                s.append(("array-placeholder",))
            elif fun==("symbol","numpy","dtype"):
                assert args==("f8",False,True)
                s.append(("dtype-placeholder",))
            else:raise ValueError("unsupported symbolic instruction")
        elif n=="BUILD":
            state=s.pop();kind=s.pop()
            if kind==("dtype-placeholder",):
                assert state==(3,"<",None,None,None,-1,-1,0)
                s.append(("float64","little"))
            elif kind==("array-placeholder",):
                version,dims,dtype,column_major,data=state
                assert version==1 and len(dims)==3 and dims[1]==dims[2]
                assert all(type(x) is int and 1<=x<=512 for x in dims)
                assert dtype==("float64","little") and column_major is False
                assert isinstance(data,bytes) and len(data)==8*dims[0]*dims[1]*dims[2]
                vals=struct.unpack("<"+"d"*(dims[0]*dims[1]*dims[2]),data)
                s.append(("matrix",dims,vals))
            else:raise ValueError("unsupported build type")
        elif n=="STOP":
            assert pos==len(blob)-1 and len(s)==1 and s[0][0]=="matrix"
            root=s[0]
        else:raise ValueError("unsupported opcode "+n)
        assert len(s)<=256 and len(memo)<=256
    assert root is not None
    return root[1:],hashlib.sha256(blob).hexdigest()

if __name__=="__main__":
    (dims,v),sha=matrix(sys.argv[1])
    N=dims[-1]
    summary={"dims":dims,"sha256":sha,
             "diagonal_sample":list(v[i*N+i] for i in range(min(N,8))),
             "unique":sorted({float(x) for x in v if math.isfinite(x)}),
             "unknown":sum(1 for x in v if not math.isfinite(x)),
             "positive":sum(1 for x in v if math.isfinite(x) and x>0)}
    print(json.dumps(summary,sort_keys=True))
